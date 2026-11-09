// optimizer.cpp - pass pipeline, candidate selection and self-verification.
#include "optimizer.h"

#include <cstdio>

#include <algorithm>
#include <chrono>
#include <cstdlib>

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
    std::string name() const {
        return std::string(reassoc ? "" : "-noreassoc") + (fuseReductions ? "-macred" : "");
    }
};

// Per-pass wall time, printed with KOPT_TIMING=1 (developer diagnostics only;
// never influences the output).
struct PassTimer {
    const char *name;
    std::chrono::steady_clock::time_point t0;
    explicit PassTimer(const char *n) : name(n), t0(std::chrono::steady_clock::now()) {}
    ~PassTimer() {
        static const bool on = getenv("KOPT_TIMING") != nullptr;
        if (on) {
            double ms = std::chrono::duration<double, std::milli>(std::chrono::steady_clock::now() - t0).count();
            if (ms > 5) fprintf(stderr, "  %-14s %8.1f ms\n", name, ms);
        }
    }
};
#define TIMED(name, expr) ([&] { PassTimer pt_(name); return (expr); }())

void runPipeline(Func &f, const Machine &m, int level, const Flags &fl) {
    TIMED("simplifyCFG", simplifyCFG(f));
    if (level <= 0) return;
    for (int round = 0; round < 4; round++) {
        bool c = false;
        c |= TIMED("sccp", sccp(f));
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
        if (fl.reassoc && TIMED("reassociate", reassociate(f))) {
            instSimplify(f);
            gvn(f);
            licm(f);
            dce(f);
        }
        TIMED("fuseOps", fuseOps(f, m, fl.fuseReductions));
        TIMED("ifConvert", ifConvert(f, m));
        TIMED("instSimplify", instSimplify(f));
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

// Optimize `in` with the SSA pipeline and lower it; with both register
// allocators when the plain one needs more names than the machine has.
void compileVariants(const Program &in, const Machine &m, int level, const Flags &fl, const std::string &tag,
                     bool tryK, std::vector<Cand> &out) {
    Func f;
    std::string err;
    if (!buildSSA(in, f, err)) return;
    runPipeline(f, m, level, fl);
    Func copy;
    const bool scratch = tryK && canSpillToScratch(f);
    if (scratch) copy = f;
    BackendOptions bo;
    Cand c;
    c.p = TIMED("lower", lowerToProgram(f, m, bo));
    if (usesUnsupported(c.p, m)) c.p = legalize(c.p, m);
    c.what = tag;
    c.flags = fl;
    const bool overK = distinctRegisters(c.p) > m.registers;
    out.push_back(std::move(c));
    if (scratch && overK) {
        bo.spillToK = true;
        Cand k;
        k.p = lowerToProgram(copy, m, bo);
        if (usesUnsupported(k.p, m)) k.p = legalize(k.p, m);
        k.what = tag + "+K";
        k.flags = fl;
        out.push_back(std::move(k));
    }
}

}  // namespace

std::string optimizeProgram(const std::string &origText, const Program &orig, const Machine &m,
                            const std::string &profileText, const Options &opt) {
    (void)profileText;
    const Program base = usesUnsupported(orig, m) ? legalize(orig, m) : orig;
    SimProgram so(base);
    std::vector<Input> inputs = generateInputs(static_cast<int>(base.params.size()), opt.checkInputs, 0x6b6f7074ull);
    std::vector<Input> more = generateInputs(static_cast<int>(base.params.size()), opt.checkInputs / 2, 0x4b494c4eull);
    inputs.insert(inputs.end(), more.begin(), more.end());
    const size_t timingSample = 24;
    std::vector<RunResult> origRuns;
    uint64_t baseCycles = 0;
    for (size_t i = 0; i < inputs.size(); i++) {
        origRuns.push_back(so.run(inputs[i], 200000, i < timingSample));
        if (i < timingSample && origRuns.back().status != Status::TIMEOUT)
            baseCycles += so.cycles(origRuns.back().trace, m);
        origRuns.back().trace.clear();
        origRuns.back().trace.shrink_to_fit();
    }
    // Quick evaluation: behaviour and exact cycles on the timing sample.
    auto quick = [&](Cand &c) {
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

    // The variant search multiplies compile time; it runs only on programs small
    // enough to stay far inside the 5 s limit on a slower judging machine.
    const bool small = base.instrCount() <= 4000;
    std::vector<Cand> cands;
    // Phase 1: the SSA pipeline, in a few flavours.
    {
        std::vector<Cand> p1;
        for (int v = 0; v < (small ? 4 : 1); v++) {
            Flags fl;
            fl.reassoc = (v & 1) == 0;
            fl.fuseReductions = (v & 2) != 0;
            compileVariants(base, m, opt.maxLevel, fl, "pipeline" + fl.name(), small, p1);
        }
        for (Cand &c : p1) quick(c);
        for (Cand &c : p1) cands.push_back(c);
    }
    // Phase 2: loop rotation and unrolling on the register form of the best
    // phase-1 results, then the whole pipeline again.
    if (small) {
        std::vector<const Cand *> bases;
        for (const Cand &c : cands) if (c.ok) bases.push_back(&c);
        std::sort(bases.begin(), bases.end(), [](const Cand *a, const Cand *b) { return a->cycles < b->cycles; });
        if (bases.size() > 2) bases.resize(2);
        std::vector<Program> basePrograms;
        std::vector<std::string> baseNames;
        std::vector<Flags> baseFlags;
        for (const Cand *b : bases) { basePrograms.push_back(b->p); baseNames.push_back(b->what); baseFlags.push_back(b->flags); }
        const int budget = std::max(24, m.icache_size);
        const int factors[] = {1, 2, 4, 8};
        std::vector<Cand> p2;
        for (size_t bi = 0; bi < basePrograms.size(); bi++) {
            for (int u : factors) {
                std::vector<uint32_t> names;
                Func rf = toRegisterForm(basePrograms[bi], names);
                bool rot = rotateLoops(rf, 8);
                bool unr = unrollLoops(rf, u, budget);
                if (!rot && !unr) continue;
                Program transformed = fromRegisterForm(rf, names);
                compileVariants(transformed, m, opt.maxLevel, baseFlags[bi],
                                baseNames[bi] + "/unroll" + std::to_string(u), true, p2);
            }
        }
        for (Cand &c : p2) quick(c);
        for (Cand &c : p2) cands.push_back(std::move(c));
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
