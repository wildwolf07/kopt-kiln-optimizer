// Exact arithmetic transformations on SSA values.
#include "passes.h"
#include <map>
#include <tuple>

namespace kopt {
// r = a - q*b modulo 2^32, including INT_MIN/-1. When remainder comes
// first, quotient executes at that exact point: same operands, same zero trap.
bool shareDivRem(Func &f, const Machine &m) {
    if (m.latency(OP_MUL) + m.latency(OP_SUB) >= m.latency(OP_MOD)) return false;
    f.resolveAll();
    using Key = std::tuple<bool, uint32_t, bool, uint32_t>;
    auto key = [](const Inst &x) {
        return Key{x.a[0].isConst, x.a[0].isConst ? x.a[0].c : static_cast<uint32_t>(x.a[0].v),
                   x.a[1].isConst, x.a[1].isConst ? x.a[1].c : static_cast<uint32_t>(x.a[1].v)};
    };
    bool changed = false;
    for (BB &b : f.bb) {
        if (!b.alive) continue;
        std::map<Key, bool> hasDiv;
        for (const Inst &x : b.insts) if (x.op == OP_DIV) hasDiv[key(x)] = true;
        if (hasDiv.empty()) continue;
        std::map<Key, Val> quotient;
        std::vector<Inst> out;
        for (Inst x : b.insts) {
            if (x.op != OP_DIV && x.op != OP_MOD) { out.push_back(x); continue; }
            const Key k = key(x);
            if (!hasDiv.count(k)) { out.push_back(x); continue; }
            auto known = quotient.find(k);
            if (x.op == OP_DIV) {
                if (known == quotient.end()) quotient[k] = x.dst;
                else { x.op = OP_MOV; x.n = 1; x.a[0] = Opnd::val(known->second); changed = true; }
                out.push_back(x);
                continue;
            }
            Val q;
            if (known != quotient.end()) q = known->second;
            else {
                Inst div = x;
                div.op = OP_DIV; div.dst = f.newVal();
                q = div.dst; quotient[k] = q;
                out.push_back(div);
            }
            Inst product;
            product.op = OP_MUL; product.dst = f.newVal(); product.n = 2;
            product.a[0] = Opnd::val(q); product.a[1] = x.a[1];
            out.push_back(product);
            x.op = OP_SUB; x.n = 2; x.a[1] = Opnd::val(product.dst);
            out.push_back(x);
            changed = true;
        }
        b.insts.swap(out);
    }
    return changed;
}
}  // namespace kopt
