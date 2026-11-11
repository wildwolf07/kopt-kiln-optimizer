// optimizer.cpp - pass pipeline, candidate selection and self-verification.
#include "optimizer.h"

#include <cmath>
#include <map>
#include <sstream>

#include <cstdio>

#include <algorithm>
#include <chrono>
#include <cstdlib>
#include <unordered_map>

#include "backend.h"
#include "ir.h"
#include "loops.h"
#include "passes.h"

namespace kopt {

Program legalize(const Program &p, const Machine &m) {
    Program q = p;
    uint32_t maxReg = 0;
    for (uint32_t r : q.params) maxReg = std::max(maxReg, r);
    for (const Block &b : q.blocks)
        for (const Instr &in : b.ins) {
            if (hasDest(in.op)) maxReg = std::max(maxReg, in.dst);
            for (int s = 0; s < in.nsrc; s++) if (in.src[s].isReg) maxReg = std::max(maxReg, in.src[s].v);
        }
    const uint32_t tmp = maxReg + 1;
    for (Block &b : q.blocks) {
        std::vector<Instr> out;
        for (const Instr &in : b.ins) {
            if (in.op == OP_MAC && !m.fused_mac) {
                Instr mul = in, add = in;
                mul.op = OP_MUL; mul.dst = tmp; mul.nsrc = 2;
                add.op = OP_ADD; add.nsrc = 2; add.src[0] = Operand::reg(tmp); add.src[1] = in.src[2];
                out.push_back(mul);
                out.push_back(add);
            } else if (in.op == OP_ADDSH && !m.fused_addsh) {
                Instr shl = in, add = in;
                shl.op = OP_SHL; shl.dst = tmp; shl.nsrc = 2; shl.src[0] = in.src[1]; shl.src[1] = Operand::imm(in.k); shl.k = 0;
                add.op = OP_ADD; add.nsrc = 2; add.src[0] = in.src[0]; add.src[1] = Operand::reg(tmp); add.k = 0;
                out.push_back(shl);
                out.push_back(add);
            } else {
                out.push_back(in);
            }
        }
        b.ins.swap(out);
    }
    return q;
}

namespace {

bool usesUnsupported(const Program &p, const Machine &m) {
    for (const Block &b : p.blocks)
        for (const Instr &in : b.ins) {
            if (in.op == OP_MAC && !m.fused_mac) return true;
            if (in.op == OP_ADDSH && !m.fused_addsh) return true;
        }
    return false;
}

struct Flags {
    bool reassoc = true;         // shorten loop-carried add chains
    bool fuseReductions = false; // mac even on a reduction (fewer registers, longer chain)
    bool speculate = false;      // hoist pure work above branches
    bool specLoadsOnly = false;  // ... but only loads and their address work
    bool strength = true;        // strength-reduce induction-variable multiplies
    bool loadPhis = false;       // loads at merges -> phis of known values
    bool tabulate = false;       // state-machine dispatch -> packed tables
    bool storeSel = false;       // conditional stores with known old values -> select + store
    std::string name() const {
        return std::string(reassoc ? "" : "-noreassoc") + (fuseReductions ? "-macred" : "") +
               (speculate ? "-spec" : "") + (strength ? "" : "-nosr") + (loadPhis ? "-lp" : "") + (storeSel ? "-ss" : "") + (tabulate ? "-tab" : "");
    }
};

// Per-pass wall time, printed with KOPT_TIMING=1 (developer diagnostics only;
// never influences the output).
bool timingOn() {
    static const bool on = getenv("KOPT_TIMING") != nullptr;
    return on;
}
struct PassTimer {
    const char *name;
    std::chrono::steady_clock::time_point t0;
    explicit PassTimer(const char *n) : name(n) { if (timingOn()) t0 = std::chrono::steady_clock::now(); }
    ~PassTimer() {
        if (timingOn()) {
            double ms = std::chrono::duration<double, std::milli>(std::chrono::steady_clock::now() - t0).count();
            if (ms > 5) fprintf(stderr, "  %-14s %8.1f ms\n", name, ms);
        }
    }
};
// KOPT_DISABLE=pass1,pass2 skips passes (developer aid for bisecting).
bool passEnabled(const char *name) {
    static const char *dis = getenv("KOPT_DISABLE");
    if (!dis) return true;
    std::string list = std::string(",") + dis + ",";
    return list.find(std::string(",") + name + ",") == std::string::npos;
}
#define TIMED(name, expr) ([&] { if (!passEnabled(name)) return false; PassTimer pt_(name); return static_cast<bool>(expr); }())

void runPipeline(Func &f, const Machine &m, int level, const Flags &fl) {
    TIMED("simplifyCFG", simplifyCFG(f));
    if (level <= 0) return;
    size_t fsize = 0;
    for (const BB &B : f.bb) if (B.alive) fsize += B.insts.size();
    for (int round = 0; round < 4; round++) {
        bool c = false;
        TIMED("ivranges", (computeIVRanges(f), true));
        // Value ranges are the costliest analysis; on very large functions they
        // run in the first round only (their facts stay valid afterwards).
        if (round == 0 || fsize < 20000) TIMED("vrp", (computeVRP(f), true));
        if (level >= 2 && fl.loadPhis && passEnabled("dupret")) c |= TIMED("dupret", dupConstReturns(f, 32, 512));
        if (level >= 2 && fl.tabulate && passEnabled("tabulate"))
            for (int r = 0; r < 4 && TIMED("tabulate", tabulateDispatch(f)); r++) c = true;
        if (level >= 2 && passEnabled("inclusive")) c |= TIMED("inclusive", normalizeInclusive(f));
        if (level >= 2 && passEnabled("closedform"))
            for (int r = 0; r < 4 && TIMED("closedform", closedFormLoops(f)); r++) c = true;
        if (level >= 2 && passEnabled("popcount"))
            for (int r = 0; r < 4 && TIMED("popcount", popcountLoops(f)); r++) c = true;
        c |= TIMED("sccp", sccp(f));
        c |= TIMED("combineLinear", combineLinear(f));
        c |= TIMED("simplifyCFG", simplifyCFG(f));
        c |= TIMED("instSimplify", instSimplify(f));
        c |= TIMED("gvn", gvn(f));
        if (level >= 2 && fl.loadPhis && passEnabled("loadphis")) c |= TIMED("loadPhis", loadPhis(f));
        if (level >= 2 && fl.loadPhis && passEnabled("aliasfwd")) c |= TIMED("aliasForward", aliasForward(f));
        if (level >= 2 && fl.storeSel && passEnabled("storeselect")) c |= TIMED("storeSelect", storeSelect(f));
        if (level >= 2 && fl.storeSel && passEnabled("armstores")) c |= TIMED("armStores", mergeArmStores(f));
        c |= TIMED("instSimplify", instSimplify(f));
        c |= TIMED("dce", dce(f));
        c |= TIMED("deadStores", deadStores(f));
        c |= TIMED("deadScratch", deadScratchStores(f));
        c |= TIMED("simplifyCFG", simplifyCFG(f));
        if (level >= 2) c |= TIMED("licm", licm(f));
        if (!c) break;
    }
    if (level >= 2) {
        if (fl.strength && TIMED("strength", strengthReduce(f))) {
            instSimplify(f);
            gvn(f);
            dce(f);
        }
        if (fl.reassoc && TIMED("reassociate", reassociate(f))) {
            instSimplify(f);
            gvn(f);
            licm(f);
            dce(f);
        }
        if (fl.reassoc && passEnabled("divconst") && TIMED("divconst", divByConstant(f, m))) {
            instSimplify(f);
            dce(f);
        }
        if (fl.reassoc && fl.storeSel && passEnabled("balance") && TIMED("balance", balanceSums(f))) {
            instSimplify(f);
            dce(f);
        }
        if (fl.reassoc && TIMED("horner", hornerSplit(f, m.registers))) {
            instSimplify(f);
            dce(f);
        }
        if (fl.specLoadsOnly && passEnabled("pipeloads") && TIMED("pipeloads", pipelineHeaderLoads(f))) {
            gvn(f);
            dce(f);
        }
        if (fl.speculate && TIMED("speculate", speculate(f, 4 * m.issue_width, true, fl.specLoadsOnly))) {
            gvn(f);
            dce(f);
        }
        TIMED("fuseOps", fuseOps(f, m, fl.fuseReductions));
        TIMED("ifConvert", ifConvert(f, m));
        if (fl.reassoc) TIMED("selectToAdd", selectToAdd(f));
        TIMED("instSimplify", instSimplify(f));
        // If-conversion and select folding can leave sums that now merge.
        if (TIMED("combineLinear", combineLinear(f))) {
            instSimplify(f);
            gvn(f);
            dce(f);
            TIMED("fuseOps", fuseOps(f, m, fl.fuseReductions));
            instSimplify(f);
        }
        TIMED("dce", dce(f));
        TIMED("simplifyCFG", simplifyCFG(f));
    }
}

int distinctRegisters(const Program &p) {
    std::vector<uint32_t> regs(p.params.begin(), p.params.end());
    for (const Block &b : p.blocks)
        for (const Instr &in : b.ins) {
            if (hasDest(in.op)) regs.push_back(in.dst);
            for (int s = 0; s < in.nsrc; s++) if (in.src[s].isReg) regs.push_back(in.src[s].v);
        }
    std::sort(regs.begin(), regs.end());
    return static_cast<int>(std::unique(regs.begin(), regs.end()) - regs.begin());
}

struct Cand {
    Program p;
    Flags flags;
    std::string what;
    uint64_t cycles = 0;
    bool ok = false;
};

// Side trajectory (programs derived from the pipelineAcrossLoops base; their
// names start with "across"). Seeds of the main search never come from it;
// stages add at most one side seed after their own seeds, and its compile
// work has a separate meter, so the main search is exactly as without it.
inline bool sideCand(const Cand &c) { return c.what.compare(0, 6, "across") == 0; }

// The best `count` candidates whose programs differ (backend variants of one
// program often fill the top places with near-copies).
std::vector<const Cand *> bestDistinctOf(const std::vector<Cand> &cands, size_t count, bool side) {
    std::vector<const Cand *> best;
    for (const Cand &c : cands) if (c.ok && sideCand(c) == side) best.push_back(&c);
    std::stable_sort(best.begin(), best.end(), [](const Cand *a, const Cand *b) { return a->cycles < b->cycles; });
    std::vector<const Cand *> out;
    std::vector<std::string> seen;
    for (const Cand *c : best) {
        if (out.size() >= count) break;
        std::string text = printProgram(c->p);
        if (std::find(seen.begin(), seen.end(), text) != seen.end()) continue;
        seen.push_back(text);
        out.push_back(c);
    }
    return out;
}
// Seeds: the best main-search programs, then at most one side program.
std::vector<const Cand *> bestDistinct(const std::vector<Cand> &cands, size_t count) {
    std::vector<const Cand *> out = bestDistinctOf(cands, count, false);
    for (const Cand *c : bestDistinctOf(cands, 2, true)) out.push_back(c);
    return out;
}


// A deterministic layout hint from executions on our fixed training inputs.
// Only block order and label indices change; all instructions remain intact.
Program traceLayout(const Program &p, const std::vector<Input> &inputs, bool chains) {
    const int nb = static_cast<int>(p.blocks.size());
    if (nb < 2) return p;
    std::vector<int> blockOf;
    std::vector<uint32_t> start(nb);
    for (int b = 0; b < nb; b++) {
        start[b] = static_cast<uint32_t>(blockOf.size());
        blockOf.insert(blockOf.end(), p.blocks[b].ins.size(), b);
    }
    std::vector<uint64_t> frequency(nb, 0);
    std::vector<std::unordered_map<int, uint64_t>> edges(nb);
    SimProgram sim(p);
    for (size_t i = 0; i < std::min<size_t>(16, inputs.size()); i++) {
        const RunResult r = sim.run(inputs[i], 200000, true);
        if (r.status == Status::TIMEOUT) continue;
        int previous = -1;
        for (uint32_t ip : r.trace) {
            const int b = blockOf[ip];
            if (ip != start[b]) continue;
            frequency[b]++;
            if (previous >= 0) edges[previous][b]++;
            previous = b;
        }
    }
    std::vector<int> order, index(nb, -1);
    std::vector<char> used(nb, 0);
    int b = 0;
    while (static_cast<int>(order.size()) < nb) {
        index[b] = static_cast<int>(order.size());
        order.push_back(b); used[b] = 1;
        int next = -1;
        uint64_t weight = 0;
        if (chains) {
            const Instr &t = p.blocks[b].ins.back();
            const int ns = t.op == OP_BR ? 2 : (t.op == OP_JMP ? 1 : 0);
            for (int i = 0; i < ns; i++) {
                const int s = t.target[i];
                const auto it = edges[b].find(s);
                const uint64_t count = it == edges[b].end() ? 0 : it->second;
                if (!used[s] && count > weight) { next = s; weight = count; }
            }
        }
        if (next < 0) for (int s = 0; s < nb; s++)
            if (!used[s] && (next < 0 || frequency[s] > frequency[next])) next = s;
        if (next < 0) break;
        b = next;
    }
    Program out;
    out.name = p.name; out.params = p.params;
    for (int old : order) {
        Block block = p.blocks[old];
        Instr &t = block.ins.back();
        if (t.op == OP_JMP || t.op == OP_BR) t.target[0] = index[t.target[0]];
        if (t.op == OP_BR) t.target[1] = index[t.target[1]];
        out.blocks.push_back(std::move(block));
    }
    return out;
}

// Optimize `in` with the SSA pipeline and lower it; with both register
// allocators when the plain one needs more names than the machine has.
// Deterministic compile-work meter (instructions lowered; K-name allocation
// counts three times). Phase 1 always runs in full; once the budget is spent,
// later stages stop trying K-name allocations, the costly part. It counts
// work, never time, so the output is the same on every machine and run.
size_t gCompileWork = 0;
size_t gSideWork = 0;           // the side trajectory's own meter
bool gWorkLimited = false;      // true from phase 2 on
const size_t kWorkBudget = 150000, kSideBudget = 60000;

void compileVariants(const Program &in, const Machine &m, int level, const Flags &fl, const std::string &tag,
                     bool tryK, std::vector<Cand> &out, bool plainOnly = false) {
    Func f;
    std::string err;
    if (!buildSSA(in, f, err)) return;
    runPipeline(f, m, level, fl);
    const bool scratch = tryK && canSpillToScratch(f);
    // Backend variants of the same optimized function: plain; scheduled on
    // values before allocation (+S: independent long-latency results get
    // different registers); and, when the program needs more than K names and
    // scratch is free, K names with spills to scratch (+K, +KS).
    std::vector<std::string> texts;
    auto emit = [&](bool pre, bool k, const char *suffix, bool spread = false) -> const Program * {
        if (pre && !passEnabled("preschedule")) return nullptr;
        const bool sideWork = tag.compare(0, 6, "across") == 0;
        size_t &meter = sideWork ? gSideWork : gCompileWork;
        if (k && gWorkLimited && meter > (sideWork ? kSideBudget : kWorkBudget)) return nullptr;
        Func g = f;
        BackendOptions bo;
        bo.preSchedule = pre;
        bo.spillToK = k;
        bo.spreadColors = spread;
        if (plainOnly) bo.spillReuse = 0;   // biggest programs: one allocation attempt
        Cand c;
        {
            PassTimer pt(k ? "lower+K" : "lower");
            c.p = lowerToProgram(g, m, bo);
        }
        if (usesUnsupported(c.p, m)) c.p = legalize(c.p, m);
        meter += c.p.instrCount() * (k ? 3 : 1);
        std::string text = printProgram(c.p);
        for (const std::string &t : texts) if (t == text) return nullptr;
        texts.push_back(text);
        c.what = tag + suffix;
        c.flags = fl;
        out.push_back(std::move(c));
        return &out.back().p;
    };
    const Program *plain = emit(false, false, "");
    const bool overK = plain && distinctRegisters(*plain) > m.registers;
    if (plainOnly && passEnabled("trees")) {
        Func tree = f;
        if (schedulePureTrees(tree)) {
            BackendOptions bo;
            Cand c; c.p = lowerToProgram(tree, m, bo);
            c.what = tag + "/tree"; c.flags = fl;
            out.push_back(std::move(c));
        }
    }
    if (plainOnly) {   // biggest programs: no pre-scheduled variants
        if (scratch && overK) emit(false, true, "+K");
        return;
    }
    const Program *pre = emit(true, false, "+S");
    const bool preOverK = pre && distinctRegisters(*pre) > m.registers;
    if (scratch && overK) emit(false, true, "+K");
    if (scratch && (overK || preOverK)) emit(true, true, "+KS");
    if (passEnabled("spreadcolors")) {
        emit(true, false, "+spread", true);
        if (scratch && (overK || preOverK)) emit(true, true, "+Kspread", true);
    }
}

}  // namespace

// Canonical form: blocks in reverse postorder from the entry (the first
// target of a branch placed right after it), unreachable blocks after them in
// file order, and registers renamed in order of first appearance (parameters
// first). Programs that differ only in block order or register names then get
// the same output, so the result does not depend on how the input was
// shuffled or renamed.
Program canonicalize(const Program &p) {
    const int nb = static_cast<int>(p.blocks.size());
    std::vector<char> seen(nb, 0);
    std::vector<int> post;
    // Iterative DFS; successors pushed so that target[0] is visited last and
    // therefore comes first in reverse postorder.
    std::vector<std::pair<int, int>> st;
    st.push_back({0, 0});
    seen[0] = 1;
    while (!st.empty()) {
        auto &top = st.back();
        const Block &b = p.blocks[top.first];
        const Instr &t = b.ins.back();
        int succ[2] = {-1, -1}, ns = 0;
        if (t.op == OP_JMP) succ[ns++] = t.target[0];
        else if (t.op == OP_BR) { succ[ns++] = t.target[1]; succ[ns++] = t.target[0]; }
        if (top.second < ns) {
            int s = succ[top.second++];
            if (s >= 0 && s < nb && !seen[s]) { seen[s] = 1; st.push_back({s, 0}); }
            continue;
        }
        post.push_back(top.first);
        st.pop_back();
    }
    std::vector<int> order(post.rbegin(), post.rend());
    for (int b = 0; b < nb; b++) if (!seen[b]) order.push_back(b);
    std::vector<int> newIndex(nb, -1);
    for (int i = 0; i < nb; i++) newIndex[order[i]] = i;
    Program q;
    q.name = p.name;
    std::unordered_map<uint32_t, uint32_t> ren;
    auto name = [&](uint32_t r) {
        auto it = ren.find(r);
        if (it != ren.end()) return it->second;
        uint32_t n = static_cast<uint32_t>(ren.size());
        ren.emplace(r, n);
        return n;
    };
    for (uint32_t r : p.params) q.params.push_back(name(r));
    for (int i = 0; i < nb; i++) {
        Block b = p.blocks[order[i]];
        for (Instr &x : b.ins) {
            for (int s = 0; s < x.nsrc; s++) if (x.src[s].isReg) x.src[s].v = name(x.src[s].v);
            if (hasDest(x.op)) x.dst = name(x.dst);
            for (int k = 0; k < 2; k++) if (x.target[k] >= 0) x.target[k] = newIndex[x.target[k]];
        }
        q.blocks.push_back(b);
    }
    return q;
}

// Profile hint: "edge FROM TO COUNT" lines naming blocks of the input program.
// Returns the counts keyed by (from block, to block) indices of `p`; empty when
// the profile is missing or names no edge of this program.
std::map<std::pair<int, int>, double> parseProfile(const std::string &text, const Program &p) {
    std::map<std::string, int> idx;
    for (size_t b = 0; b < p.blocks.size(); b++) idx[p.blocks[b].label] = static_cast<int>(b);
    std::map<std::pair<int, int>, double> out;
    std::istringstream in(text);
    std::string line;
    while (std::getline(in, line)) {
        std::istringstream ls(line);
        std::string kw, from, to;
        double count;
        if (!(ls >> kw >> from >> to >> count) || kw != "edge" || count < 0) continue;
        auto a = idx.find(from), b = idx.find(to);
        if (a == idx.end() || b == idx.end()) continue;
        out[{a->second, b->second}] += count;
    }
    return out;
}

// Edge counts of one run (from its instruction trace).
std::map<std::pair<int, int>, double> edgeCounts(const Program &p, const std::vector<uint32_t> &trace) {
    std::vector<int> blockOf;
    for (size_t b = 0; b < p.blocks.size(); b++)
        for (size_t i = 0; i < p.blocks[b].ins.size(); i++) blockOf.push_back(static_cast<int>(b));
    std::map<std::pair<int, int>, double> out;
    for (size_t i = 1; i < trace.size(); i++) {
        const int a = blockOf[trace[i - 1]], b = blockOf[trace[i]];
        const Block &blk = p.blocks[static_cast<size_t>(a)];
        if (trace[i - 1] + 1 == trace[i] && a == b) continue;
        if (!isTerminator(blk.ins.back().op)) continue;
        out[{a, b}] += 1;
    }
    return out;
}

const size_t kSeeds = 5;   // distinct programs seeding the late stages

std::string optimizeProgram(const std::string &origText, const Program &orig, const Machine &m,
                            const std::string &profileText, const Options &opt) {
    gCompileWork = 0;
    gSideWork = 0;
    gWorkLimited = false;
    const Program canon = canonicalize(orig);
    const Program base = usesUnsupported(canon, m) ? legalize(canon, m) : canon;
    SimProgram so(base);
    const int np = static_cast<int>(base.params.size());
    // Timing sample first: typical runs, then the small edge values. The rest of
    // the inputs (edge values, special pairs, random) only check behaviour.
    // Big programs run longer: the step limit grows with the size (a 100k
    // instruction program with loops easily runs a few hundred thousand
    // steps), and they get fewer check inputs to stay inside the time limit.
    const size_t progSize = base.instrCount();
    const uint64_t stepLimit = std::min<uint64_t>(6000000, std::max<uint64_t>(200000, 30 * progSize));
    const int nCheck = progSize > 4000 ? 16 : opt.checkInputs;
    std::vector<Input> inputs = typicalInputs(np, 16, 0x74797069ull);
    // With a usable profile, half of the timing sample becomes the pool inputs
    // whose runs of the input program look most like the profile (log-scale
    // edge-count distance). The other half stays as it is, so a wrong profile
    // can only shift the choice, never decide it alone.
    if (!profileText.empty() && progSize <= 4000 && passEnabled("profile")) {
        const auto prof = parseProfile(profileText, orig);
        if (!prof.empty()) {
            SimProgram sp(orig);
            std::vector<Input> pool = typicalInputs(np, 48, 0x70726f66ull);
            std::vector<Input> g2 = generateInputs(np, 16, 0x70726f67ull);
            pool.insert(pool.end(), g2.begin(), g2.end());
            std::vector<std::pair<double, size_t>> dist;
            for (size_t i = 0; i < pool.size(); i++) {
                RunResult r = sp.run(pool[i], stepLimit, true);
                if (r.status == Status::TIMEOUT) continue;
                auto ec = edgeCounts(orig, r.trace);
                double d = 0;
                for (const auto &e : prof) {
                    auto it = ec.find(e.first);
                    const double c = it == ec.end() ? 0 : it->second;
                    d += std::fabs(std::log2(1 + c) - std::log2(1 + e.second));
                }
                for (const auto &e : ec)
                    if (!prof.count(e.first)) d += std::log2(1 + e.second);
                dist.push_back({d, i});
            }
            std::sort(dist.begin(), dist.end());
            for (size_t k = 0; k < 8 && k < dist.size(); k++) inputs[8 + k] = pool[dist[k].second];
        }
    }
    std::vector<Input> gen = generateInputs(np, nCheck, 0x6b6f7074ull);
    inputs.insert(inputs.end(), gen.begin(), gen.end());
    std::vector<Input> more = generateInputs(np, nCheck / 2, 0x4b494c4eull);
    inputs.insert(inputs.end(), more.begin(), more.end());
    std::vector<Input> lit = literalInputs(base, nCheck / 2, 0x4c495453ull);
    inputs.insert(inputs.end(), lit.begin(), lit.end());
    const size_t timingSample = 16;   // the typical inputs
    std::vector<RunResult> origRuns;
    std::vector<uint64_t> baseCyc(timingSample, 0);
    for (size_t i = 0; i < inputs.size(); i++) {
        origRuns.push_back(so.run(inputs[i], stepLimit, i < timingSample));
        if (i < timingSample && origRuns.back().status != Status::TIMEOUT)
            baseCyc[i] = so.cycles(origRuns.back().trace, m);
        origRuns.back().trace.clear();
        origRuns.back().trace.shrink_to_fit();
    }
    // Score = total cycles over the typical inputs: the expected cost of an
    // ordinary run. (Edge values only check behaviour; their run lengths are
    // not what a judge measures.)
    uint64_t baseCycles = 0;
    for (size_t i = 0; i < timingSample; i++) baseCycles += baseCyc[i];
    // Quick evaluation: behaviour and exact cycles on the timing sample.
    auto quick = [&](Cand &c) {
        PassTimer pt("quickcheck");
        SimProgram sc(c.p);
        c.ok = true;
        c.cycles = 0;
        for (size_t i = 0; i < timingSample && i < inputs.size(); i++) {
            const RunResult &a = origRuns[i];
            if (a.status == Status::TIMEOUT) continue;
            RunResult b = sc.run(inputs[i], 20 * a.steps + 1000, true);
            std::string d = compareRuns(a, b);
            if (!d.empty()) {
                c.ok = false;
                if (opt.verbose || opt.strict) fprintf(stderr, "kopt: %s failed quick check: %s\n", c.what.c_str(), d.c_str());
                if (opt.strict) exit(3);
                return;
            }
            c.cycles += sc.cycles(b.trace, m);
        }
        if (opt.verbose)
            fprintf(stderr, "kopt: %-22s cycles %8llu (input %llu), %zu instrs, %d regs\n", c.what.c_str(),
                    static_cast<unsigned long long>(c.cycles), static_cast<unsigned long long>(baseCycles),
                    c.p.instrCount(), distinctRegisters(c.p));
    };
    auto fullCheck = [&](const Cand &c) {
        PassTimer pt("fullcheck");
        SimProgram sc(c.p);
        for (size_t i = timingSample; i < inputs.size(); i++) {
            const RunResult &a = origRuns[i];
            if (a.status == Status::TIMEOUT) continue;
            RunResult b = sc.run(inputs[i], 20 * a.steps + 1000, false);
            std::string d = compareRuns(a, b);
            if (!d.empty()) {
                if (opt.verbose || opt.strict) fprintf(stderr, "kopt: %s failed full check: %s\n", c.what.c_str(), d.c_str());
                if (opt.strict) exit(3);
                return false;
            }
        }
        return true;
    };

    // The variant search multiplies compile time, so its size depends on the
    // program size (never on the clock): the full search up to 1000
    // instructions, a reduced one up to 4000, a single compile above that.
    const bool dense = base.blocks.size() > 256 || distinctRegisters(base) > 256;
    uint64_t trainingWork = 0;
    for (size_t i = 0; i < timingSample; i++)
        trainingWork += origRuns[i].status == Status::TIMEOUT ? stepLimit : origRuns[i].steps;
    // Execution counts on fixed inputs are deterministic. Expensive nested
    // loops get fewer recompilations without using a wall-clock cutoff.
    int effort = dense ? 0 : (progSize <= 1000 ? 2 : (progSize <= 4000 ? 1 : 0));
    if (trainingWork > 1000000) effort = 0;
    else if (trainingWork > 300000) effort = std::min(effort, 1);
    std::vector<Cand> cands;
    // Phase 1: the SSA pipeline, in a few flavours.
    {
        std::vector<Cand> p1;
        // reassoc, fuseReductions, speculate, strength
        static const bool kVariants[][4] = {
            {true, false, false, true}, {false, false, false, true}, {false, true, false, true},
            {true, true, false, true}, {true, false, true, true}, {false, true, true, true},
            {true, false, false, false}, {false, true, false, false}, {true, false, false, true},
        };
        const int nVariants = effort == 2 ? 9 : (effort == 1 ? 2 : 1);
        for (int v = 0; v < nVariants; v++) {
            Flags fl;
            fl.reassoc = kVariants[v][0];
            fl.fuseReductions = kVariants[v][1];
            fl.speculate = kVariants[v][2];
            fl.strength = kVariants[v][3];
            fl.tabulate = v == 8;
            compileVariants(base, m, opt.maxLevel, fl, "pipeline" + fl.name(), true, p1, effort == 0);
        }
        // A second base when the next iteration's first load can be read
        // before inner loops whose stores provably miss it (pipelineAcrossLoops).
        // Only programs where that proof succeeds get these extra candidates.
        if (effort == 2 && progSize <= 500 && passEnabled("pipeacross")) {
            Func f; std::string err;
            if (buildSSA(base, f, err)) {
                Flags prepare;
                runPipeline(f, m, opt.maxLevel, prepare);
                int moved = 0;
                for (int r = 0; r < 2 && pipelineAcrossLoops(f); ++r) ++moved;
                clearIVRanges();
                if (moved) {
                    instSimplify(f); dce(f); simplifyCFG(f);
                    BackendOptions initial;
                    const Program across = lowerToProgram(f, m, initial);
                    std::vector<Cand> side;
                    for (int v = 0; v < nVariants; v++) {
                        Flags fl;
                        fl.reassoc = kVariants[v][0];
                        fl.fuseReductions = kVariants[v][1];
                        fl.speculate = kVariants[v][2];
                        fl.strength = kVariants[v][3];
                        fl.tabulate = v == 8;
                        compileVariants(across, m, opt.maxLevel, fl, "across" + fl.name(), true, side, false);
                    }
                    for (Cand &c : side) p1.push_back(std::move(c));
                }
            }
        }
        for (Cand &c : p1) quick(c);
        for (Cand &c : p1) cands.push_back(c);
        gWorkLimited = true;
    }
    // Phase 2: loop rotation and unrolling on the register form of the best
    // phase-1 results, then the whole pipeline again.
    {
        // Bases: the default pipeline plus the best distinct phase-1 programs (a
        // variant that wins before unrolling can lose after it, so keep several).
        std::vector<const Cand *> sorted;
        for (const Cand &c : cands) if (c.ok && !sideCand(c)) sorted.push_back(&c);
        std::stable_sort(sorted.begin(), sorted.end(), [](const Cand *a, const Cand *b) { return a->cycles < b->cycles; });
        std::vector<const Cand *> bases;
        std::vector<std::string> seen;
        auto addBase = [&](const Cand *c) {
            std::string text = printProgram(c->p);
            for (const std::string &t : seen) if (t == text) return;
            seen.push_back(text);
            bases.push_back(c);
        };
        for (const Cand *c : sorted) if (c->what == "pipeline") addBase(c);
        const size_t maxBases = effort == 2 ? 4 : 1;
        for (const Cand *c : sorted) { if (bases.size() >= maxBases) break; addBase(c); }
                if (effort == 2) {   // side trajectory: its default-flag program, then its best two
            for (const Cand *c : bestDistinctOf(cands, 1000, true)) if (c->what == "across") { addBase(c); break; }
            for (const Cand *c : bestDistinctOf(cands, 2, true)) addBase(c);
        }
        std::vector<Program> basePrograms;
        std::vector<std::string> baseNames;
        std::vector<Flags> baseFlags;
        for (const Cand *b : bases) { basePrograms.push_back(b->p); baseNames.push_back(b->what); baseFlags.push_back(b->flags); }
        const int budget = std::max(24, m.icache_size);
        // Register-form transforms: rotate+unroll by 1/2/4/8, jump threading,
        // and full peeling of short loops (constant trip counts fold away).
        struct Plan {
            const char *name;
            int unroll, peel;
            bool thread;
            int counted;
            bool unswitch = false;
            bool reduced = false;   // also in the reduced search (up to 4000 instructions)
            bool huge = false;      // also for the biggest programs (one cheap transform)
            bool headCounted = false;
            int outer = 0;          // unroll factor for top-level loop nests
            bool msplit = false;    // monotone unswitching first
        };
        static const Plan plans[] = {
            {"unroll1", 1, 0, false, 0, false, false, true}, {"unroll2", 2, 0, false, 0, false, true}, {"unroll4", 4, 0, false, 0},
            {"unroll8", 8, 0, false, 0}, {"thread", 0, 0, true, 0, false, true}, {"peel8", 0, 8, true, 0, false, true},
            {"peel16", 0, 16, true, 0}, {"cunroll2", 1, 0, false, 2}, {"cunroll4", 1, 0, false, 4},
            {"cunroll8", 1, 0, false, 8}, {"cunroll4r", 1, 0, false, -4, false, true}, {"cunroll8r", 1, 0, false, -8},
            {"unswitch", 0, 0, false, 0, true, true}, {"unswitch+peel16", 0, 16, true, 0, true},
            {"unswitch+unroll4", 4, 0, false, 0, true},
            {"counted2", 0, 0, false, 2, false, false, false, true},
            {"counted4", 0, 0, false, 4, false, false, false, true},
            {"counted8", 0, 0, false, 8, false, false, false, true},
            {"ounroll2", 0, 0, false, 0, false, false, false, false, 2},
            {"ounroll4", 0, 0, false, 0, false, false, false, false, 4},
            {"ounroll2+unroll2", 2, 0, false, 0, false, false, false, false, 2},
            {"msplit", 0, 0, false, 0, false, true, false, false, 0, true},
            {"msplit+unroll2", 2, 0, false, 0, false, false, false, false, 0, true},
            {"msplit+unroll4", 4, 0, false, 0, false, false, false, false, 0, true},
        };
        std::vector<Cand> p2;
        for (size_t bi = 0; bi < basePrograms.size(); bi++) {
            for (const Plan &pl : plans) {
                if (effort == 1 && !pl.reduced) continue;
                if (effort == 0 && !pl.huge) continue;
                std::vector<uint32_t> names;
                Func rf = toRegisterForm(basePrograms[bi], names);
                bool any = false;
                if (pl.headCounted) {
                    if (!unrollCountedLoops(rf, names, pl.counted, budget)) continue;
                    any = true;
                }
                if (pl.unswitch) {
                    if (!unswitchLoops(rf, 2 * budget)) continue;
                    any = true;
                }
                if (pl.msplit) {
                    if (!passEnabled("msplit") || !monotoneUnswitch(rf, 2 * budget)) continue;
                    any = true;
                }
                if (pl.outer) {
                    any |= rotateLoops(rf, 8);
                    if (!unrollLoops(rf, pl.outer, 2 * budget, true)) continue;
                    any = true;
                }
                if (pl.peel) any |= peelLoops(rf, pl.peel, 2 * std::max(64, m.icache_size));
                if (pl.thread) any |= threadJumps(rf, 12, 256);
                if (pl.unroll) {
                    any |= rotateLoops(rf, 8);
                    if (pl.counted) {
                        // every innermost counted loop, one at a time
                        if (!countedUnroll(rf, names, std::abs(pl.counted), 2 * budget, pl.counted < 0)) continue;
                        any = true;
                    } else {
                        any |= unrollLoops(rf, pl.unroll, budget);
                    }
                }
                if (!any) continue;
                Program transformed = fromRegisterForm(rf, names);
                compileVariants(transformed, m, opt.maxLevel, baseFlags[bi], baseNames[bi] + "/" + pl.name, true, p2,
                                effort == 0);
            }
        }
        for (Cand &c : p2) quick(c);
        for (Cand &c : p2) cands.push_back(std::move(c));

        // Phase 3: jump threading on the best programs so far (after unrolling
        // and constant folding, repeated tests of one condition become visible).
        // Two rounds: each recompile can expose more known branches.
        for (int round = 0; round < (effort == 2 ? 2 : 0); round++) {
            std::vector<const Cand *> top;
            for (const Cand &c : cands) if (c.ok && !sideCand(c)) top.push_back(&c);
            std::stable_sort(top.begin(), top.end(), [](const Cand *a, const Cand *b) { return a->cycles < b->cycles; });
            // Distinct programs only (backend variants of one program count once).
            std::vector<const Cand *> distinct;
            std::vector<std::string> seenText;
            for (const Cand *c : top) {
                if (distinct.size() >= 5) break;
                std::string t = printProgram(c->p);
                bool dup = false;
                for (const std::string &x : seenText) if (x == t) dup = true;
                if (dup) continue;
                seenText.push_back(t);
                distinct.push_back(c);
            }
            std::vector<std::pair<Program, std::pair<std::string, Flags>>> work;
            for (const Cand *c : distinct) work.push_back({c->p, {c->what, c->flags}});
            std::vector<Cand> p3;
            for (auto &w : work) {
                if (w.second.first.size() > 120) continue;
                // Threading, and peeling (a transform in phase 2 can leave a loop
                // that only the recompile made short enough to peel away).
                for (int kind = 0; kind < 2; kind++) {
                    std::vector<uint32_t> names;
                    Func rf = toRegisterForm(w.first, names);
                    bool any = kind == 0 ? threadJumps(rf, 16, 512)
                                         : (round == 0 && peelLoops(rf, 16, 2 * std::max(64, m.icache_size)) &&
                                            (threadJumps(rf, 12, 256), true));
                    if (!any) continue;
                    Program transformed = fromRegisterForm(rf, names);
                    compileVariants(transformed, m, opt.maxLevel, w.second.second,
                                    w.second.first + (kind == 0 ? "/thread" : "/peel16"), true, p3);
                }
            }
            if (p3.empty()) break;
            for (Cand &c : p3) quick(c);
            for (Cand &c : p3) cands.push_back(std::move(c));
        }
    }
    // Flatten nests of short constant-trip loops: peel the innermost loop away,
    // recompile, and repeat on the result, so a 4x4x4 nest becomes straight-line
    // code that GVN and the scheduler can work on. Each step is a candidate; the
    // simulator (with the icache cost) decides.
    if (effort == 2 && passEnabled("flatten")) {
        const std::vector<const Cand *> best = bestDistinct(cands, 3);
        std::vector<std::pair<Program, std::pair<std::string, Flags>>> seeds;
        for (size_t i = 0; i < best.size(); i++)
            seeds.push_back({best[i]->p, {best[i]->what, best[i]->flags}});
        // Bounded so compile time stays small whatever the machine's icache.
        // Deterministic work budget: total instructions compiled by this chain.
        const int budget = std::min(2048, 16 * std::max(64, m.icache_size));
        size_t work = 0;
        const size_t workCap = 12000;
        std::vector<Cand> flat;
        for (auto &sd : seeds) {
            Program cur = sd.first;
            std::string name = sd.second.first;
            for (int step = 0; step < 4; step++) {
                std::vector<uint32_t> names;
                Func rf = toRegisterForm(cur, names);
                const bool split = splitIrreducible(rf, budget);
            if (!peelLoops(rf, 16, budget) && !split) break;
                threadJumps(rf, 12, 256);
                Program transformed = fromRegisterForm(rf, names);
                if (transformed.instrCount() > 2500 || work + transformed.instrCount() > workCap) break;
                work += transformed.instrCount();
                std::vector<Cand> got;
                name += "/flat";
                compileVariants(transformed, m, opt.maxLevel, sd.second.second, name, true, got);
                if (got.empty()) break;
                for (Cand &c : got) quick(c);
                const Cand *pick = nullptr;
                for (const Cand &c : got) if (c.ok && (!pick || c.cycles < pick->cycles)) pick = &c;
                if (!pick) break;
                cur = pick->p;
                for (Cand &c : got) flat.push_back(std::move(c));
            }
        }
        for (Cand &c : flat) cands.push_back(std::move(c));
    }
    // Load phis on the best programs so far (a separate stage: it helps
    // mostly after unrolling/flattening has exposed the repeated loads).
    if (effort == 2 && passEnabled("loadphis")) {
        const std::vector<const Cand *> best = bestDistinct(cands, kSeeds);
        std::vector<Cand> more;
        size_t lpWork = 0;   // deterministic budget: instructions recompiled here
        for (size_t i = 0; i < best.size(); i++)
            for (int ss = 0; ss < 2; ss++) {
                if (lpWork + best[i]->p.instrCount() > 8000) continue;
                lpWork += best[i]->p.instrCount();
                Flags fl = best[i]->flags;
                fl.loadPhis = true;
                fl.storeSel = ss == 1;
                std::vector<Cand> got;
                compileVariants(best[i]->p, m, opt.maxLevel, fl, best[i]->what + (ss ? "/ss" : "/lp"), true, got);
                for (Cand &c : got) quick(c);
                for (Cand &c : got) more.push_back(std::move(c));
            }
        for (Cand &c : more) cands.push_back(std::move(c));
    }
    if (effort == 2 && passEnabled("pressure")) {
        const auto seeds = bestDistinct(cands, 4);
        std::vector<Cand> scheduled;
        for (const Cand *seed : seeds) {
            Func f; std::string err;
            if (!buildSSA(seed->p, f, err)) continue;
            instSimplify(f); dce(f); simplifyCFG(f);
            const bool scratch = canSpillToScratch(f);
            for (int spill = 0; spill < (scratch ? 2 : 1); spill++) {
                Func copy = f;
                BackendOptions bo; bo.preSchedule = true; bo.pressureSchedule = true;
                bo.spillToK = spill != 0;
                Cand c; c.p = lowerToProgram(copy, m, bo);
                c.what = seed->what + (spill ? "/pressureK" : "/pressure");
                c.flags = seed->flags; quick(c); scheduled.push_back(std::move(c));
            }
        }
        for (Cand &c : scheduled) cands.push_back(std::move(c));
    }
    if (effort == 2 && passEnabled("remat")) {
        const auto seeds = bestDistinct(cands, 4);
        std::vector<Cand> remat;
        for (const Cand *seed : seeds) {
            Func f; std::string err;
            if (!buildSSA(seed->p, f, err)) continue;
            instSimplify(f); dce(f); simplifyCFG(f);
            if (!rematerialize(f, m)) continue;
            for (int pre = 0; pre < 2; pre++) {
                Func copy = f;
                BackendOptions bo; bo.preSchedule = pre != 0;
                Cand c; c.p = lowerToProgram(copy, m, bo);
                c.what = seed->what + (pre ? "/rematS" : "/remat");
                c.flags = seed->flags; quick(c); remat.push_back(std::move(c));
            }
        }
        for (Cand &c : remat) cands.push_back(std::move(c));
    }
    if (effort == 2 && passEnabled("trees")) {
        const auto seeds = bestDistinct(cands, 4);
        std::vector<Cand> trees;
        for (const Cand *seed : seeds) {
            Func f; std::string err;
            if (!buildSSA(seed->p, f, err)) continue;
            instSimplify(f); dce(f); simplifyCFG(f);
            if (!schedulePureTrees(f)) continue;
            for (int spread = 0; spread < 2; spread++) {
                Func copy = f;
                BackendOptions bo; bo.spreadColors = spread != 0;
                Cand c; c.p = lowerToProgram(copy, m, bo);
                c.what = seed->what + (spread ? "/treeSpread" : "/tree");
                c.flags = seed->flags; quick(c); trees.push_back(std::move(c));
            }
        }
        for (Cand &c : trees) cands.push_back(std::move(c));
    }
    if (effort == 2 && passEnabled("arithmetic")) {
        const auto seeds = bestDistinct(cands, 5);
        std::vector<Cand> arithmetic;
        for (const Cand *seed : seeds) {
            Func f;
            std::string err;
            if (!buildSSA(seed->p, f, err)) continue;
            bool changed = shareDivRem(f, m);
            changed |= signedPowerTwo(f, m);
            if (!changed) continue;
            instSimplify(f); gvn(f); dce(f); simplifyCFG(f);
            for (int pre = 0; pre < 2; pre++) {
                Func copy = f;
                BackendOptions bo; bo.preSchedule = pre != 0;
                Cand c; c.p = lowerToProgram(copy, m, bo);
                c.what = seed->what + (pre ? "/arithS" : "/arith");
                c.flags = seed->flags; quick(c);
                arithmetic.push_back(std::move(c));
            }
        }
        for (Cand &c : arithmetic) cands.push_back(std::move(c));
    }
    // Speculation recompiles of the best programs so far, after the stages
    // above (which seed from the best candidates and must keep their seeds):
    // full speculation (work of an unrolled chain's later steps moves above
    // its exit branches) and loads-only speculation with pipelined header
    // loads. Own deterministic budget.
    if (effort == 2 && passEnabled("latespec")) {
        const std::vector<const Cand *> best = bestDistinct(cands, kSeeds);
        std::vector<Cand> more;
        size_t specWork = 0;
        for (size_t i = 0; i < best.size(); i++)
            for (int ss = 2; ss < 4; ss++) {
                if (best[i]->flags.speculate && !(ss == 3 && !best[i]->flags.specLoadsOnly)) continue;
                if (specWork + best[i]->p.instrCount() > 8000) continue;
                specWork += best[i]->p.instrCount();
                Flags fl = best[i]->flags;
                fl.loadPhis = false;
                fl.storeSel = false;
                fl.speculate = true;
                fl.specLoadsOnly = ss == 3;
                std::vector<Cand> got;
                compileVariants(best[i]->p, m, opt.maxLevel, fl, best[i]->what + (ss == 3 ? "/specL" : "/spec"), false, got);
                for (Cand &c : got) quick(c);
                for (Cand &c : got) more.push_back(std::move(c));
            }
        for (Cand &c : more) cands.push_back(std::move(c));
    }
    if (effort == 2 && passEnabled("tracelayout")) {
        std::vector<const Cand *> best;
        for (const Cand &c : cands) if (c.ok && !sideCand(c)) best.push_back(&c);
        std::stable_sort(best.begin(), best.end(), [](const Cand *a, const Cand *b) { return a->cycles < b->cycles; });
        if (best.size() > 8) best.resize(8);
        for (const Cand *c : bestDistinctOf(cands, 1, true)) best.push_back(c);
        std::vector<Cand> layouts;
        for (size_t i = 0; i < best.size(); i++) {
            for (bool chains : {true, false}) {
                Cand c;
                c.p = traceLayout(best[i]->p, inputs, chains);
                if (printProgram(c.p) == printProgram(best[i]->p)) continue;
                c.what = best[i]->what + (chains ? "/trace" : "/hot");
                c.flags = best[i]->flags;
                quick(c);
                layouts.push_back(std::move(c));
            }
        }
        for (Cand &c : layouts) cands.push_back(std::move(c));
    }
    if (effort == 2 && passEnabled("compact")) {
        const auto seeds = bestDistinct(cands, 8);
        std::vector<Cand> compact;
        for (const Cand *seed : seeds) {
            for (bool tails : {false, true}) {
                Cand c; c.p = compactBlocks(seed->p, tails);
                if (c.p.instrCount() >= seed->p.instrCount()) continue;
                c.what = seed->what + (tails ? "/tails" : "/compact"); c.flags = seed->flags;
                quick(c); compact.push_back(std::move(c));
            }
        }
        for (Cand &c : compact) cands.push_back(std::move(c));
    }
    if (effort == 2 && passEnabled("bottomup")) {
        const auto seeds = bestDistinct(cands, 4);
        std::vector<Cand> scheduled;
        for (const Cand *seed : seeds) {
            Func f; std::string err;
            if (!buildSSA(seed->p, f, err)) continue;
            instSimplify(f); dce(f); simplifyCFG(f);
            const bool scratch = canSpillToScratch(f);
            for (int mode = 0; mode < 4; mode++) {
                if ((mode & 1) && !scratch) continue;
                Func copy = f;
                BackendOptions bo; bo.preSchedule = true; bo.bottomUpSchedule = true;
                bo.spillToK = (mode & 1) != 0; bo.spreadColors = (mode & 2) != 0;
                Cand c; c.p = lowerToProgram(copy, m, bo);
                c.what = seed->what + "/bottomup" + std::to_string(mode);
                c.flags = seed->flags; quick(c); scheduled.push_back(std::move(c));
            }
        }
        for (Cand &c : scheduled) cands.push_back(std::move(c));
    }
    if (effort == 2 && passEnabled("sink")) {
        const auto seeds = bestDistinct(cands, 4);
        std::vector<Cand> sunk;
        for (const Cand *seed : seeds) {
            Func f; std::string err;
            if (!buildSSA(seed->p, f, err)) continue;
            instSimplify(f); dce(f); simplifyCFG(f);
            if (!sinkInstructions(f)) continue;
            const bool scratch = canSpillToScratch(f);
            for (int mode = 0; mode < 6; mode++) {
                if ((mode & 1) && !scratch) continue;
                Func copy = f;
                BackendOptions bo;
                bo.spillToK = (mode & 1) != 0;
                bo.preSchedule = mode >= 2;
                bo.bottomUpSchedule = mode >= 4;
                Cand c; c.p = lowerToProgram(copy, m, bo);
                c.what = seed->what + "/sink" + std::to_string(mode);
                c.flags = seed->flags; quick(c); sunk.push_back(std::move(c));
            }
        }
        for (Cand &c : sunk) cands.push_back(std::move(c));
    }
    if (progSize <= 1000 && !dense) {
        auto programs = finiteAlternatives(base, passEnabled("finite"), passEnabled("packed"));
        for (size_t i = 0; i < programs.size(); i++) {
            Cand c; c.p = std::move(programs[i]);
            c.what = "finite-table" + std::to_string(i); quick(c);
            cands.push_back(std::move(c));
        }
    }
    // Final-only layout candidates: preserve every earlier seed lineage.
    if (effort == 2 && passEnabled("latepolish")) {
        const auto seeds = bestDistinct(cands, 3);
        std::vector<Cand> polished;
        for (const Cand *seed : seeds) for (bool chains : {true, false}) {
            Cand c; c.p = traceLayout(seed->p, inputs, chains);
            if (printProgram(c.p) == printProgram(seed->p)) continue;
            c.what = seed->what + (chains ? "/lateTrace" : "/lateHot");
            c.flags = seed->flags; quick(c); polished.push_back(std::move(c));
        }
        for (Cand &c : polished) cands.push_back(std::move(c));
    }
    if (progSize <= 1000 && !dense && passEnabled("affine")) {
        Program p;
        if (bitAffineFunction(base, m, p)) {
            Cand raw; raw.p = p; raw.what = "bit-affine"; quick(raw); cands.push_back(std::move(raw));
            Func f; std::string err;
            if (buildSSA(p, f, err)) {
                instSimplify(f); dce(f); simplifyCFG(f);
                for (int pre = 0; pre < 2; pre++) {
                    Func copy = f; BackendOptions bo; bo.preSchedule = pre != 0;
                    Cand c; c.p = lowerToProgram(copy, m, bo);
                    c.what = pre ? "bit-affineS" : "bit-affine-lowered"; quick(c);
                    cands.push_back(std::move(c));
                }
            }
        }
    }
    if (progSize <= 1000 && !dense && passEnabled("widefinite")) {
        auto programs = finiteWideAlternatives(base);
        for (size_t i = 0; i < programs.size(); i++) {
            Cand c; c.p = std::move(programs[i]); c.what = "wide-table" + std::to_string(i);
            quick(c); cands.push_back(std::move(c));
        }
    }
    // Final-only load splitting; preserve every earlier candidate and seed set.
    if (effort == 2 && passEnabled("loadremat")) {
        const auto seeds = bestDistinct(cands, 3);
        std::vector<Cand> split;
        size_t work = 0;
        for (const Cand *seed : seeds) {
            if (seed->p.instrCount() > 500 || work + 4 * seed->p.instrCount() > 2000) continue;
            Func f; std::string err;
            if (!buildSSA(seed->p, f, err)) continue;
            instSimplify(f); dce(f); simplifyCFG(f);
            if (!rematerializeLoads(f)) continue;
            size_t size = 0;
            for (const BB &b : f.bb) if (b.alive) size += b.insts.size();
            if (size > 500 || work + 4 * size > 2000) continue;
            const bool scratch = canSpillToScratch(f);
            for (int mode = 0; mode < 4; mode++) {
                if (mode == 3 && !scratch) continue;
                Func copy = f; BackendOptions bo;
                bo.preSchedule = mode != 0; bo.bottomUpSchedule = mode >= 2;
                bo.spillToK = mode == 3;
                Cand c; c.p = lowerToProgram(copy, m, bo);
                c.what = seed->what + "/loadremat" + std::to_string(mode); c.flags = seed->flags;
                quick(c); split.push_back(std::move(c));
                work += size;
            }
        }
        for (Cand &c : split) cands.push_back(std::move(c));
    }
    // Distance-one memory reuse is prepared before this stage's own unrolling,
    // independently of every earlier candidate/seed trajectory.
    if (effort == 2 && progSize <= 500 && passEnabled("rolling")) {
        Func f; std::string err;
        if (buildSSA(base, f, err)) {
            Flags prepare; prepare.loadPhis = true; prepare.storeSel = true; prepare.reassoc = false;
            runPipeline(f, m, opt.maxLevel, prepare);
            for (int r = 0; r < 4; ++r) {
                bool changed = storeSelect(f); changed |= mergeArmStores(f); changed |= ifConvert(f, m);
                instSimplify(f); dce(f); simplifyCFG(f);
                if (!changed) break;
            }
            int promoted = 0;
            for (int r = 0; r < 4 && promoteRollingLoad(f); ++r) ++promoted;
            if (promoted) {
                Func copy = f; BackendOptions initial;
                const Program seed = lowerToProgram(copy, m, initial);
                size_t work = 0;
                const size_t workCap = 6000;
                auto emit = [&](Func &ir, const Flags &fl, const std::string &tag, std::vector<Cand> &out) {
                    size_t units = 0;
                    for (const BB &b : ir.bb) if (b.alive) {
                        units += b.insts.size();
                        for (const Phi &ph : b.phis) units += ph.in.size();
                    }
                    if (units > 1000) return;
                    const bool scratch = canSpillToScratch(ir);
                    for (int mode = 0; mode < 4; ++mode) {
                        if (mode == 3 && !scratch) continue;
                        const size_t cost = units * (mode == 3 ? 3 : 1);
                        if (work + cost > workCap) continue;
                        work += cost;
                        Func g = ir; BackendOptions bo;
                        bo.preSchedule = mode != 0; bo.spreadColors = mode == 2; bo.spillToK = mode == 3;
                        Cand c; c.p = lowerToProgram(g, m, bo); c.what = tag + "/" + std::to_string(mode); c.flags = fl;
                        quick(c); out.push_back(std::move(c));
                    }
                };
                std::vector<Cand> rolling;
                for (int factor : {1, 2, 4, 8}) {
                    Program p = seed;
                    if (factor > 1) {
                        std::vector<uint32_t> names; Func rf = toRegisterForm(seed, names);
                        rotateLoops(rf, 8);
                        if (!unrollLoops(rf, factor, 500)) continue;
                        p = fromRegisterForm(rf, names);
                    }
                    if (p.instrCount() > 500 || work >= workCap) continue;
                    Func ir; if (!buildSSA(p, ir, err)) continue;
                    Flags fl; runPipeline(ir, m, opt.maxLevel, fl);
                    const std::string tag = "rolling" + std::to_string(factor);
                    std::vector<Cand> group; emit(ir, fl, tag, group);
                    const auto best = bestDistinct(group, 2);
                    std::vector<Cand> advanced;
                    for (const Cand *c : best) {
                        Func next; if (work >= workCap || !buildSSA(c->p, next, err)) continue;
                        Flags spec; spec.speculate = true; spec.specLoadsOnly = true;
                        runPipeline(next, m, opt.maxLevel, spec);
                        emit(next, spec, c->what + "/prefetch", advanced);
                    }
                    for (Cand &c : group) rolling.push_back(std::move(c));
                    for (Cand &c : advanced) rolling.push_back(std::move(c));
                }
                for (Cand &c : rolling) cands.push_back(std::move(c));
            }
        }
    }
    if (effort == 2 && progSize <= 160 && passEnabled("packedcounts")) {
        unsigned loads = 0;
        bool hasStore = false;
        for (const Block &block : base.blocks) for (const Instr &x : block.ins) {
            if (x.op == OP_LOAD) ++loads;
            if (x.op == OP_STORE) hasStore = true;
        }
        Func f; std::string err;
        if (hasStore && loads >= 2 && buildSSA(base, f, err)) {
            instSimplify(f); gvn(f); dce(f); simplifyCFG(f);
            if (packIndexedCounts(f)) {
                BackendOptions raw; raw.schedule = false;
                const Program seed = lowerToProgram(f, m, raw);
                std::vector<Cand> packed;
                size_t work = 0;
                for (int plan : {1, 2, 4, -4, -8}) {
                    const int factor = std::abs(plan);
                    Program p = seed;
                    if (factor != 1) {
                        std::vector<uint32_t> names;
                        Func rf = toRegisterForm(seed, names);
                        if (plan < 0) {
                            if (!unrollCountedLoops(rf, names, factor, 240)) continue;
                        } else {
                            rotateLoops(rf, 8);
                            if (!unrollLoops(rf, factor, 240)) continue;
                        }
                        p = fromRegisterForm(rf, names);
                    }
                    const size_t size = p.instrCount();
                    if (size > 240 || work + 2 * size > 1600) continue;
                    work += 2 * size;
                    for (bool advance : {false, true}) {
                        Flags fl;
                        fl.speculate = advance; fl.specLoadsOnly = advance;
                        const std::string tag = "packedcounts" + std::to_string(plan) +
                                                (advance ? "/prefetch" : "");
                        compileVariants(p, m, opt.maxLevel, fl, tag, false, packed);
                    }
                }
                for (Cand &c : packed) quick(c);
                const auto seeds = bestDistinct(packed, 2);
                std::vector<Cand> scheduled;
                for (const Cand *best : seeds) {
                    if (best->p.instrCount() > 160) continue;
                    Func ir;
                    if (!buildSSA(best->p, ir, err)) continue;
                    instSimplify(ir); dce(ir); simplifyCFG(ir);
                    BackendOptions bo;
                    bo.preSchedule = true;
                    bo.bottomUpSchedule = true;
                    Cand c;
                    c.p = lowerToProgram(ir, m, bo);
                    c.what = best->what + "/bottomup";
                    c.flags = best->flags;
                    quick(c);
                    Cand layout = c;
                    layout.p = traceLayout(c.p, inputs, false);
                    layout.what += "/hot";
                    quick(layout);
                    scheduled.push_back(std::move(c));
                    scheduled.push_back(std::move(layout));
                }
                for (Cand &c : packed) cands.push_back(std::move(c));
                for (Cand &c : scheduled) cands.push_back(std::move(c));
            }
        }
    }
    if (effort == 2 && passEnabled("selectfactor")) {
        const auto seeds = bestDistinct(cands, 3);
        std::vector<Cand> factored;
        size_t work = 0;
        for (const Cand *seed : seeds) {
            if (seed->p.instrCount() > 500) continue;
            Func f; std::string err;
            if (!buildSSA(seed->p, f, err) || !factorSelects(f)) continue;
            size_t size = 0;
            for (const BB &block : f.bb) if (block.alive) size += block.insts.size();
            if (work + 4 * size > 2000) continue;
            const bool scratch = canSpillToScratch(f);
            for (int mode = 0; mode < 4; ++mode) {
                if (mode == 3 && !scratch) continue;
                Func copy = f;
                BackendOptions bo;
                bo.preSchedule = mode != 0;
                bo.bottomUpSchedule = mode == 2;
                bo.spillToK = mode == 3;
                Cand c;
                c.p = lowerToProgram(copy, m, bo);
                c.flags = seed->flags;
                c.what = seed->what + "/selectfactor" + std::to_string(mode);
                quick(c);
                factored.push_back(std::move(c));
                work += size;
            }
        }
        for (Cand &c : factored) cands.push_back(std::move(c));
    }
    // Two-row reuse, final-only and independently budgeted.
    if (effort == 2 && progSize <= 160 && passEnabled("rowpairs")) {
        const auto recipes = rowPairAlternatives(base);
        size_t work = 0;
        std::vector<Cand> pairs;
        auto emitPairs = [&](Func &ir, const Flags &fl, const std::string &tag, std::vector<Cand> &out) {
            size_t units = 0;
            for (const BB &b : ir.bb) if (b.alive) {
                units += b.insts.size();
                for (const Phi &ph : b.phis) units += ph.in.size();
            }
            if (units > 600) return;
            const bool scratch = canSpillToScratch(ir);
            for (int mode = 0; mode < 4; ++mode) {
                if (mode == 3 && !scratch) continue;
                const size_t cost = units * (mode == 3 ? 3 : 1);
                if (work + cost > 6000) continue;
                work += cost;
                Func f = ir; BackendOptions bo;
                bo.preSchedule = mode != 0; bo.bottomUpSchedule = mode >= 2; bo.spillToK = mode == 3;
                Cand c; c.p = lowerToProgram(f, m, bo); c.flags = fl;
                c.what = tag + "/" + std::to_string(mode);
                quick(c); out.push_back(std::move(c));
            }
        };
        // Peeling exposes a bounded constant inner loop to the usual cleanup;
        // both the rolled and fully unrolled structural recipes remain options.
        for (int plan : {0, 1, 2, 3}) {
            if (recipes.empty()) break;
            Program p = recipes[plan == 1 ? 1 : 0];
            if (plan == 0 || plan == 3) {
                std::vector<uint32_t> names; Func rf = toRegisterForm(p, names);
                if (!peelLoops(rf, plan == 0 ? 8 : 16, 600)) continue;
                p = fromRegisterForm(rf, names);
            }
            if (work >= 4000 || p.instrCount() > 600 || work + p.instrCount() > 6000) continue;
            work += p.instrCount();
            Func ir; std::string err;
            if (!buildSSA(p, ir, err)) continue;
            Flags fl; fl.reassoc = false; fl.fuseReductions = true;
            runPipeline(ir, m, opt.maxLevel, fl);
            emitPairs(ir, fl, "rowpairs" + std::to_string(plan), pairs);
        }
        const auto seeds = bestDistinctOf(pairs, 2, false);
        std::vector<Cand> advanced;
        for (const Cand *seed : seeds) {
            Func ir; std::string err;
            if (work + seed->p.instrCount() > 6000 || !buildSSA(seed->p, ir, err)) continue;
            work += seed->p.instrCount();
            Flags fl = seed->flags; fl.speculate = true; fl.specLoadsOnly = true;
            runPipeline(ir, m, opt.maxLevel, fl);
            emitPairs(ir, fl, seed->what + "/specL", advanced);
        }
        for (Cand &c : advanced) pairs.push_back(std::move(c));
        const size_t count = pairs.size();
        for (size_t i = 0; i < count; ++i) for (bool chains : {true,false}) {
            if (work + pairs[i].p.instrCount() > 6000) continue;
            work += pairs[i].p.instrCount();
            Cand c; c.p = traceLayout(pairs[i].p, inputs, chains); c.flags = pairs[i].flags;
            c.what = pairs[i].what + (chains ? "/trace" : "/hot"); quick(c); cands.push_back(std::move(c));
        }
        for (Cand &c : pairs) cands.push_back(std::move(c));
    }
    // Join hoisting: empty pure branch arms into the branch block and move
    // pure join work above the branch, so loop tests and counters no longer
    // wait behind an effectful arm. Final-only, own deterministic budget.
    if (effort == 2 && passEnabled("joinhoist")) {
        const auto seeds = bestDistinct(cands, 4);
        uint64_t incumbent = UINT64_MAX;
        for (const Cand &c : cands) if (c.ok) incumbent = std::min(incumbent, c.cycles);
        std::vector<Cand> hoisted;
        size_t work = 0;
        for (const Cand *seed : seeds) {
            // Decision graphs are tuned to the training distribution already.
            if (seed->what.rfind("wide-table", 0) == 0 || seed->what.rfind("finite-table", 0) == 0) continue;
            if (seed->p.instrCount() > 1500 || work + seed->p.instrCount() > 6000) continue;
            work += seed->p.instrCount();
            Func f; std::string err;
            if (!buildSSA(seed->p, f, err)) continue;
            instSimplify(f); dce(f);
            bool any = false;
            for (int round = 0; round < 3; ++round) {
                bool c = hoistPureArms(f, 12);
                c |= hoistToIdom(f, 64);
                if (!c) break;
                any = true;
                instSimplify(f); dce(f);
            }
            if (!any) continue;
            simplifyCFG(f); dce(f);
            const bool scratch = canSpillToScratch(f);
            std::vector<Cand> local;
            for (int mode = 0; mode < 4; ++mode) {
                if (mode == 3 && !scratch) continue;
                Func copy = f;
                BackendOptions bo;
                bo.preSchedule = mode != 0;
                bo.bottomUpSchedule = mode == 2;
                bo.spillToK = mode == 3;
                Cand c; c.p = lowerToProgram(copy, m, bo);
                c.flags = seed->flags;
                c.what = seed->what + "/joinhoist" + std::to_string(mode);
                quick(c); local.push_back(std::move(c));
            }
            int best = -1;
            for (size_t i = 0; i < local.size(); ++i)
                if (local[i].ok && (best < 0 || local[i].cycles < local[best].cycles)) best = static_cast<int>(i);
            if (best >= 0) {
                const Cand top = local[best];
                for (bool chains : {true, false}) {
                    Cand c; c.p = traceLayout(top.p, inputs, chains);
                    c.flags = top.flags; c.what = top.what + (chains ? "/trace" : "/hot");
                    quick(c); local.push_back(std::move(c));
                }
            }
            for (Cand &c : local) hoisted.push_back(std::move(c));
        }
        // Only a clear training win replaces the incumbent: sub-0.5% gains of a
        // final-only stage did not carry over to other inputs.
        for (Cand &c : hoisted)
            if (c.ok && (incumbent == UINT64_MAX || c.cycles * 1000 < incumbent * 995)) cands.push_back(std::move(c));
    }
    // Register-touch polishing when the program names more registers than the
    // machine keeps resident: commutative operand order and `mov r, r`
    // touches choose which value the hardware evicts. Exact-model search with
    // a deterministic evaluation budget.
    if (effort == 2 && passEnabled("lrupolish")) {
        const auto seeds = bestDistinct(cands, 2);
        std::vector<Cand> polished;
        size_t steps = 0;
        for (const Cand *seed : seeds) {
            if (registerNames(seed->p) <= static_cast<size_t>(m.registers)) continue;
            const size_t size = seed->p.instrCount();
            if (size > 400) continue;
            // Budget in candidate evaluations, scaled down for larger programs.
            const size_t evals = std::min<size_t>(1500, 60000 / (size + 20));
            if (steps + evals > 3000) continue;
            steps += evals;
            auto eval = [&](const Program &q) {
                Cand c; c.p = q; quick(c);
                return c.ok ? c.cycles : UINT64_MAX;
            };
            Program q = lruPolish(seed->p, eval, evals);
            if (printProgram(q) == printProgram(seed->p)) continue;
            Cand c; c.p = std::move(q); c.flags = seed->flags; c.what = seed->what + "/lru";
            quick(c); polished.push_back(std::move(c));
        }
        for (Cand &c : polished) cands.push_back(std::move(c));
    }
    if (const char *dump = getenv("KOPT_DUMP")) {   // developer: write every candidate
        for (size_t i = 0; i < cands.size(); i++) {
            std::string path = std::string(dump) + "/cand" + std::to_string(i) + ".kir";
            if (FILE *fp = fopen(path.c_str(), "w")) {
                fprintf(fp, "; %s score=%llu ok=%d\n%s", cands[i].what.c_str(),
                        static_cast<unsigned long long>(cands[i].cycles), cands[i].ok ? 1 : 0, printProgram(cands[i].p).c_str());
                fclose(fp);
            }
        }
    }
    // Fastest first; the first one that passes the full check wins.
    std::stable_sort(cands.begin(), cands.end(), [](const Cand &a, const Cand &b) {
        if (a.ok != b.ok) return a.ok;
        if (a.cycles != b.cycles) return a.cycles < b.cycles;
        return a.p.instrCount() < b.p.instrCount();   // tie: smaller code (less icache risk)
    });
    for (const Cand &c : cands) {
        if (!c.ok || c.cycles >= baseCycles) break;
        if (fullCheck(c)) {
            if (opt.verbose) fprintf(stderr, "kopt: chose %s\n", c.what.c_str());
            return printProgram(c.p);
        }
    }
    return usesUnsupported(orig, m) ? printProgram(base) : origText;
}

}  // namespace kopt
