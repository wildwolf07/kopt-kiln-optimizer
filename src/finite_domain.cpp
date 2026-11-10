// Backward bit-demand proof for finite-domain specialization.
#include "passes.h"

#include <algorithm>
#include <vector>

namespace kopt {

bool finiteInputMasks(const Program &p, std::vector<uint32_t> &masks) {
    if (p.blocks.empty() || p.blocks.size() > 256 || p.params.size() > 8 || p.instrCount() > 8000) return false;
    for (const Block &b : p.blocks) for (const Instr &x : b.ins)
        if (isMemOp(x.op) || x.op == OP_TRAP) return false;
    Func f; std::string err;
    if (!buildSSA(p, f, err)) return false;
    // No cached ranges or cleanup proofs are used: derive dependence directly
    // from the fresh SSA graph, including all branch and trapping-divisor uses.
    std::vector<const Inst *> defs(f.nvals, nullptr);
    std::vector<const Phi *> phis(f.nvals, nullptr);
    std::vector<char> known(f.nvals, 0);
    std::vector<uint32_t> value(f.nvals, 0);
    for (const BB &b : f.bb) if (b.alive) {
        for (const Phi &ph : b.phis) phis[ph.dst] = &ph;
        for (const Inst &x : b.insts) if (x.dst >= 0) defs[x.dst] = &x;
    }
    auto literal = [&](Opnd o) { return !o.isConst && known[o.v] ? Opnd::cst(value[o.v]) : o; };
    // Exact constant evaluation only, with no interval or path facts. In raw
    // KIR a literal mask often arrives through one or more const/mov values.
    // A bounded scan can miss constants but cannot invent one.
    for (int round = 0; round < 8; round++) {
        bool change = false;
        for (Val v = 0; v < f.nvals; v++) {
            if (known[v]) continue;
            if (phis[v]) {
                bool allSame = !phis[v]->in.empty(); uint32_t c = 0; bool first = true;
                for (const auto &in : phis[v]->in) {
                    const Opnd o = literal(in.second);
                    if (!o.isConst || (!first && c != o.c)) { allSame = false; break; }
                    first = false; c = o.c;
                }
                if (allSame) { known[v] = 1; value[v] = c; change = true; }
            } else if (defs[v]) {
                const Inst &x = *defs[v]; uint32_t a[3] = {0, 0, 0}; bool allConst = true;
                for (int i = 0; i < x.n; i++) {
                    const Opnd o = literal(x.a[i]);
                    if (!o.isConst) { allConst = false; break; }
                    a[i] = o.c;
                }
                uint32_t c;
                if (allConst && foldConstant(x.op, a[0], a[1], a[2], x.k, c)) {
                    known[v] = 1; value[v] = c; change = true;
                }
            }
        }
        if (!change) break;
    }
    std::vector<uint32_t> demand(f.nvals, 0);
    std::vector<char> queued(f.nvals, 0);
    std::vector<Val> work;
    auto need = [&](Opnd o, uint32_t bits) {
        if (o.isConst || known[o.v] || !bits || (demand[o.v] & bits) == bits) return;
        demand[o.v] |= bits;
        if (!queued[o.v]) { queued[o.v] = 1; work.push_back(o.v); }
    };
    const uint32_t all = ~uint32_t{0};
    for (const BB &b : f.bb) if (b.alive) {
        for (const Phi &ph : b.phis) phis[ph.dst] = &ph;
        for (const Inst &x : b.insts) {
            if (x.dst >= 0) defs[x.dst] = &x;
            if (x.op == OP_BR || x.op == OP_RET) need(x.a[0], all);
            // Even an unused quotient can trap. Preserve the complete divisor.
            if (x.op == OP_DIV || x.op == OP_MOD) need(x.a[1], all);
        }
    }
    auto lowThrough = [](uint32_t d) {
        d |= d >> 1; d |= d >> 2; d |= d >> 4; d |= d >> 8; d |= d >> 16;
        return d;
    };
    while (!work.empty()) {
        const Val v = work.back(); work.pop_back(); queued[v] = 0;
        const uint32_t d = demand[v];
        if (phis[v]) {
            for (const auto &in : phis[v]->in) need(in.second, d);
            continue;
        }
        if (!defs[v]) continue;  // parameter; uninitialized registers are SSA zero
        Inst instruction = *defs[v];
        for (int i = 0; i < instruction.n; i++) instruction.a[i] = literal(instruction.a[i]);
        const Inst *x = &instruction;
        auto arg = [&](int a, uint32_t bits) { need(x->a[a], bits); };
        switch (x->op) {
        case OP_CONST: case OP_MOV: arg(0, d); break;
        case OP_AND:
            arg(0, x->a[1].isConst ? d & x->a[1].c : d);
            arg(1, x->a[0].isConst ? d & x->a[0].c : d); break;
        case OP_OR:
            arg(0, x->a[1].isConst ? d & ~x->a[1].c : d);
            arg(1, x->a[0].isConst ? d & ~x->a[0].c : d); break;
        case OP_XOR: arg(0, d); arg(1, d); break;
        case OP_SHL: case OP_SHR:
            if (x->a[1].isConst) {
                const unsigned shift = x->a[1].c & 31u;
                arg(0, x->op == OP_SHL ? d >> shift : d << shift);
            } else { arg(0, all); arg(1, 31); }
            break;
        case OP_ADD: case OP_SUB: case OP_MUL:
            arg(0, lowThrough(d)); arg(1, lowThrough(d)); break;
        case OP_MAC:
            arg(0, lowThrough(d)); arg(1, lowThrough(d)); arg(2, lowThrough(d)); break;
        case OP_ADDSH:
            arg(0, lowThrough(d)); arg(1, lowThrough(d) >> x->k); break;
        case OP_EQ: case OP_LT:
            if (d & 1u) { arg(0, all); arg(1, all); }
            break;
        case OP_SELECT:
            arg(0, all); arg(1, d); arg(2, d); break;
        case OP_DIV: case OP_MOD: arg(0, all); arg(1, all); break;
        default: return false;
        }
    }
    std::vector<uint32_t> result;
    unsigned bits = 0;
    for (Val v : f.params) {
        const uint32_t m = demand[v]; result.push_back(m);
        for (uint32_t b = m; b; b &= b - 1) if (++bits > 6) return false;
    }
    masks = std::move(result);
    return true;
}

}  // namespace kopt
