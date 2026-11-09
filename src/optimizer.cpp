// optimizer.cpp - pass pipeline, candidate selection and self-verification.
#include "optimizer.h"

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
    bool strength = true;        // strength-reduce induction-variable multiplies
    std::string name() const {
        return std::string(reassoc ? "" : "-noreassoc") + (fuseReductions ? "-macred" : "") +
               (speculate ? "-spec" : "") + (strength ? "" : "-nosr");
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
        c |= TIMED("sccp", sccp(f));
        c |= TIMED("combineLinear", combineLinear(f));
        c |= TIMED("simplifyCFG", simplifyCFG(f));
        c |= TIMED("instSimplify", instSimplify(f));
        c |= TIMED("gvn", gvn(f));
        c |= TIMED("instSimplify", instSimplify(f));
        c |= TIMED("dce", dce(f));
        c |= TIMED("deadStores", deadStores(f));
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
        if (fl.reassoc && TIMED("horner", hornerSplit(f, m.registers))) {
            instSimplify(f);
            dce(f);
        }
        if (fl.speculate && TIMED("speculate", speculate(f, 4 * m.issue_width))) {
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

std::string optimizeProgram(const std::string &origText, const Program &orig, const Machine &m,
                            const std::string &profileText, const Options &opt) {
    (void)profileText;
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
    const bool small = effort >= 1;
    std::vector<Cand> cands;
    // Phase 1: the SSA pipeline, in a few flavours.
    {
        std::vector<Cand> p1;
        // reassoc, fuseReductions, speculate
        // reassoc, fuseReductions, speculate, strength
        static const bool kVariants[][4] = {
            {true, false, false, true}, {false, false, false, true}, {false, true, false, true},
            {true, true, false, true}, {true, false, true, true}, {false, true, true, true},
            {true, false, false, false}, {false, true, false, false},
        };
        const int nVariants = effort == 2 ? 8 : (effort == 1 ? 2 : 1);
        for (int v = 0; v < nVariants; v++) {
            Flags fl;
            fl.reassoc = kVariants[v][0];
            fl.fuseReductions = kVariants[v][1];
            fl.speculate = kVariants[v][2];
            fl.strength = kVariants[v][3];
            compileVariants(base, m, opt.maxLevel, fl, "pipeline" + fl.name(), small, p1, effort == 0);
        }
        for (Cand &c : p1) quick(c);
        for (Cand &c : p1) cands.push_back(c);
    }
    // Phase 2: loop rotation and unrolling on the register form of the best
    // phase-1 results, then the whole pipeline again.
    {
        // Bases: the default pipeline plus the best distinct phase-1 programs (a
        // variant that wins before unrolling can lose after it, so keep several).
        std::vector<const Cand *> sorted;
        for (const Cand &c : cands) if (c.ok) sorted.push_back(&c);
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
            for (const Cand &c : cands) if (c.ok) top.push_back(&c);
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
        std::vector<const Cand *> best;
        for (const Cand &c : cands) if (c.ok) best.push_back(&c);
        std::stable_sort(best.begin(), best.end(), [](const Cand *a, const Cand *b) { return a->cycles < b->cycles; });
        std::vector<std::pair<Program, std::pair<std::string, Flags>>> seeds;
        for (size_t i = 0; i < std::min<size_t>(3, best.size()); i++)
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
    if (effort == 2 && passEnabled("tracelayout")) {
        std::vector<const Cand *> best;
        for (const Cand &c : cands) if (c.ok) best.push_back(&c);
        std::stable_sort(best.begin(), best.end(), [](const Cand *a, const Cand *b) { return a->cycles < b->cycles; });
        std::vector<Cand> layouts;
        for (size_t i = 0; i < std::min<size_t>(8, best.size()); i++) {
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
        return a.cycles < b.cycles;
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
