// Exact signed division/remainder by constant powers of two. Kept separate
// from the pipeline so the caller can offer this as a measured candidate.
#include "ir.h"
#include "sim.h"

namespace kopt {

bool signedPowerTwo(Func &f, const Machine &m) {
    // Each replacement has six ALU instructions, including the final select.
    // Use total instruction latency as a conservative profitability filter;
    // candidate scoring still accounts for issue width and register pressure.
    const int64_t cost = 6ll * m.latency(OP_SHR);
    bool changed = false;
    for (BB &block : f.bb) {
        if (!block.alive) continue;
        std::vector<Inst> out;
        out.reserve(block.insts.size());
        for (const Inst &original : block.insts) {
            // Copy before emitting: no instruction reference survives insertion.
            const Inst x = original;
            if ((x.op != OP_DIV && x.op != OP_MOD) || x.dst < 0 ||
                cost >= m.latency(x.op)) {
                out.push_back(x);
                continue;
            }
            const Opnd a = f.resolve(x.a[0]), b = f.resolve(x.a[1]);
            if (a.isConst || !b.isConst) {
                out.push_back(x);
                continue;
            }
            const bool negativeDivisor = (b.c & 0x80000000u) != 0;
            const uint32_t magnitude = negativeDivisor ? 0u - b.c : b.c;
            // Zero must retain its trap. +/-1 already have cheaper identities.
            if (magnitude <= 1 || (magnitude & (magnitude - 1)) != 0) {
                out.push_back(x);
                continue;
            }
            unsigned shift = 0;
            for (uint32_t bits = magnitude; bits > 1; bits >>= 1) ++shift;
            auto emit = [&](Op op, Opnd first, Opnd second, Opnd third = Opnd()) {
                Inst t;
                t.op = op;
                t.dst = f.newVal();
                t.n = op == OP_SELECT ? 3 : 2;
                t.a[0] = first;
                t.a[1] = second;
                t.a[2] = third;
                out.push_back(t);
                return Opnd::val(t.dst);
            };
            const Opnd sign = emit(OP_SHR, a, Opnd::cst(31));
            const Opnd negated = emit(OP_SUB, Opnd::cst(0), a);
            // Unsigned negation represents abs(INT_MIN) as 0x80000000,
            // so logical shift/mask works for every 32-bit dividend.
            const Opnd absolute = emit(OP_SELECT, sign, negated, a);
            const Opnd resultMagnitude = x.op == OP_DIV
                ? emit(OP_SHR, absolute, Opnd::cst(shift))
                : emit(OP_AND, absolute, Opnd::cst(magnitude - 1));
            const Opnd negativeResult = emit(OP_SUB, Opnd::cst(0), resultMagnitude);
            // Division truncates toward zero; remainder has the dividend's
            // sign regardless of the divisor. Even INT_MIN is a valid divisor.
            const bool flip = x.op == OP_DIV && negativeDivisor;
            Inst result;
            result.op = OP_SELECT;
            result.dst = x.dst;
            result.n = 3;
            result.a[0] = sign;
            result.a[1] = flip ? resultMagnitude : negativeResult;
            result.a[2] = flip ? negativeResult : resultMagnitude;
            out.push_back(result);
            changed = true;
        }
        block.insts.swap(out);
    }
    return changed;
}

}  // namespace kopt
