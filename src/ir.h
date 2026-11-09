// ir.h - the optimizer's SSA form.
//
// A Func is a control-flow graph of basic blocks. Every value (Val) is defined
// exactly once: by a parameter, a phi, or an instruction. Operands are either a
// value or a 32-bit constant. Registers that are read before any write hold 0
// (KIR_SPEC.md section 3), so such reads become the constant 0.
//
// Uses are rewritten lazily: replaceAll(v, x) records a forwarding entry and
// resolve() follows it, so passes never need explicit use lists.
#pragma once

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "kir.h"

namespace kopt {

using Val = int32_t;

struct Opnd {
    bool isConst = true;
    uint32_t c = 0;
    Val v = -1;
    static Opnd cst(uint32_t c) { Opnd o; o.isConst = true; o.c = c; o.v = -1; return o; }
    static Opnd val(Val v) { Opnd o; o.isConst = false; o.c = 0; o.v = v; return o; }
    bool operator==(const Opnd &o) const { return isConst == o.isConst && (isConst ? c == o.c : v == o.v); }
    bool operator!=(const Opnd &o) const { return !(*this == o); }
    bool isC(uint32_t x) const { return isConst && c == x; }
};

struct Inst {
    Op op = OP_RET;
    Val dst = -1;        // -1 when the instruction has no destination
    Opnd a[3];
    uint8_t n = 0;       // number of source operands
    uint8_t k = 0;       // addsh shift
    int tgt[2] = {-1, -1};
};

struct Phi {
    Val dst = -1;
    std::vector<std::pair<int, Opnd>> in;   // (predecessor block, incoming value)
};

struct BB {
    std::vector<int> preds;
    std::vector<Phi> phis;
    std::vector<Inst> insts;      // the last one is the terminator
    bool alive = true;
    std::string label;            // original label (for readable output), may be empty
    double freq = 1.0;            // estimated executions per run
    int loopDepth = 0;
    const Inst &term() const { return insts.back(); }
    Inst &term() { return insts.back(); }
};

struct Func {
    std::string name;
    std::vector<BB> bb;            // bb[0] is the entry block
    std::vector<Val> params;       // values of the parameters, header order
    int nvals = 0;
    std::vector<Opnd> fwd;         // forwarding table for replaced values

    Val newVal() { fwd.push_back(Opnd::val(nvals)); return nvals++; }
    Opnd resolve(Opnd o) {
        while (!o.isConst && fwd[o.v] != Opnd::val(o.v)) {
            Opnd n = fwd[o.v];
            if (!n.isConst && fwd[n.v] != n) fwd[o.v] = fwd[n.v];  // path halving
            o = n;
        }
        return o;
    }
    void replaceAll(Val v, Opnd with) {
        with = resolve(with);
        if (!with.isConst && with.v == v) return;
        fwd[v] = with;
    }
    // Successor block ids of block b (0, 1 or 2 entries).
    int succs(int b, int out[2]) const;
    void rebuildPreds();          // recompute preds from terminators; drops phi inputs of removed edges
    void resolveAll();            // apply the forwarding table to every operand
};

// Program <-> SSA.
bool buildSSA(const Program &p, Func &f, std::string &err);

// Structural checks (SSA single definition, dominance of uses, phi inputs match
// predecessors). Returns an empty string when the function is well formed.
std::string verifyFunc(Func &f);

// Debug dump.
std::string dumpFunc(Func &f);

}  // namespace kopt
