// optimizer.cpp - pass pipeline, candidate selection and self-verification.
#include "optimizer.h"

#include <cstdio>

#include "backend.h"
#include "ir.h"
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

void runPipeline(Func &f, const Machine &m, int level) {
    simplifyCFG(f);
    if (level <= 0) return;
    for (int round = 0; round < 4; round++) {
        bool c = false;
        c |= sccp(f);
        c |= simplifyCFG(f);
        c |= instSimplify(f);
        c |= gvn(f);
        c |= instSimplify(f);
        c |= dce(f);
        c |= deadStores(f);
        c |= simplifyCFG(f);
        if (level >= 2) c |= licm(f);
        if (!c) break;
    }
    if (level >= 2) {
        fuseOps(f, m);
        ifConvert(f, m);
        instSimplify(f);
        dce(f);
        simplifyCFG(f);
    }
}

struct Checked {
    bool ok = false;
    uint64_t cycles = 0;   // summed over the timing sample
    std::string why;
};

// Run the original and the candidate on the same generated inputs.
Checked check(const SimProgram &orig, const std::vector<RunResult> &origRuns, const Program &cand,
              const std::vector<Input> &inputs, const Machine &m, size_t timingSample) {
    Checked r;
    SimProgram sc(cand);
    for (size_t i = 0; i < inputs.size(); i++) {
        const RunResult &a = origRuns[i];
        if (a.status == Status::TIMEOUT) continue;
        bool wantTrace = i < timingSample;
        RunResult b = sc.run(inputs[i], 20 * a.steps + 1000, wantTrace);
        std::string d = compareRuns(a, b);
        if (!d.empty()) { r.why = d + " on input " + std::to_string(i); return r; }
        if (wantTrace) r.cycles += sc.cycles(b.trace, m);
    }
    (void)orig;
    r.ok = true;
    return r;
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
    std::string best = usesUnsupported(orig, m) ? printProgram(base) : origText;
    uint64_t bestCycles = baseCycles;
    for (int level = opt.maxLevel; level >= 1; level--) {
        Func f;
        std::string err;
        if (!buildSSA(base, f, err)) break;
        runPipeline(f, m, level);
        BackendOptions bo;
        Program cand = lowerToProgram(f, m, bo);
        if (usesUnsupported(cand, m)) cand = legalize(cand, m);
        Checked c = check(so, origRuns, cand, inputs, m, timingSample);
        if (opt.verbose)
            fprintf(stderr, "kopt: level %d -> %s, cycles %llu (input %llu)\n", level,
                    c.ok ? "ok" : c.why.c_str(), static_cast<unsigned long long>(c.cycles),
                    static_cast<unsigned long long>(baseCycles));
        if (!c.ok) continue;
        if (c.cycles <= bestCycles) {
            best = printProgram(cand);
            bestCycles = c.cycles;
        }
        break;
    }
    return best;
}

}  // namespace kopt
