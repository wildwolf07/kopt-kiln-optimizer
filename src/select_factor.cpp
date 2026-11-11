// Share an identical arithmetic operation across a select's two alternatives.
#include "passes.h"

#include <array>
#include <vector>

namespace kopt {
namespace {

bool canFactor(Op op) {
    switch (op) {
    case OP_ADD: case OP_SUB: case OP_MUL: case OP_AND: case OP_OR:
    case OP_XOR: case OP_SHL: case OP_SHR: case OP_LT: case OP_EQ:
    case OP_SELECT: case OP_MAC: case OP_ADDSH:
        return true;
    default:
        return false;
    }
}

bool commutative(Op op) {
    return op == OP_ADD || op == OP_MUL || op == OP_AND || op == OP_OR ||
           op == OP_XOR || op == OP_EQ || op == OP_MAC;
}

}  // namespace

bool factorSelects(Func &f) {
    if (f.bb.size() > 256 || f.nvals > 12000) return false;
    f.resolveAll();
    std::vector<Inst> definitions(f.nvals);
    std::vector<char> defined(f.nvals, 0);
    std::vector<unsigned> uses(f.nvals, 0);
    size_t instructions = 0;
    for (const BB &block : f.bb) {
        if (!block.alive) continue;
        instructions += block.insts.size();
        for (const Phi &phi : block.phis)
            for (const auto &edge : phi.in) if (!edge.second.isConst) ++uses[edge.second.v];
        for (const Inst &x : block.insts) {
            if (x.dst >= 0) {
                definitions[x.dst] = x;
                defined[x.dst] = 1;
            }
            for (int i = 0; i < x.n; ++i) if (!x.a[i].isConst) ++uses[x.a[i].v];
        }
    }
    if (instructions > 2000) return false;
    const int originalValues = f.nvals;
    const auto get = [&](Opnd value) -> const Inst * {
        return !value.isConst && value.v < originalValues && defined[value.v]
               ? &definitions[value.v] : nullptr;
    };
    unsigned changes = 0;
    for (BB &block : f.bb) {
        if (!block.alive) continue;
        std::vector<Inst> result;
        result.reserve(block.insts.size());
        for (Inst x : block.insts) {
            if (x.op != OP_SELECT || x.a[0].isConst || changes >= 64) {
                result.push_back(x);
                continue;
            }
            // The selected arm already establishes the same condition, so a
            // nested direct select on that condition has only one possible arm.
            for (int arm = 1; arm <= 2 && changes < 64; ++arm) {
                const Inst *nested = get(x.a[arm]);
                if (nested && nested->op == OP_SELECT && nested->a[0] == x.a[0] &&
                    uses[nested->dst] == 1) {
                    --uses[nested->dst];
                    x.a[arm] = nested->a[arm];
                    ++changes;
                }
            }
            const Inst *left = get(x.a[1]), *right = get(x.a[2]);
            if (!left || !right || left->op != right->op || !canFactor(left->op) ||
                left->n != right->n || left->k != right->k || left->dst == right->dst ||
                uses[left->dst] != 1 || uses[right->dst] != 1 || changes >= 64) {
                result.push_back(x);
                continue;
            }
            Inst shared = *left;
            std::array<Opnd, 3> alternative{right->a[0], right->a[1], right->a[2]};
            int varied = -1;
            for (int order = 0; order < (commutative(left->op) ? 2 : 1); ++order) {
                if (order != 0) std::swap(alternative[0], alternative[1]);
                int different = -1;
                bool match = true;
                for (int i = 0; i < left->n; ++i) {
                    if (left->a[i] == alternative[i]) continue;
                    if (different >= 0) { match = false; break; }
                    different = i;
                }
                if (match && different >= 0) { varied = different; break; }
            }
            if (varied < 0) {
                result.push_back(x);
                continue;
            }
            Inst choose;
            choose.op = OP_SELECT;
            choose.dst = f.newVal();
            choose.n = 3;
            choose.a[0] = x.a[0];
            choose.a[1] = left->a[varied];
            choose.a[2] = alternative[varied];
            shared.dst = x.dst;
            shared.a[varied] = Opnd::val(choose.dst);
            result.push_back(choose);
            result.push_back(shared);
            --uses[left->dst];
            --uses[right->dst];
            ++changes;
        }
        block.insts.swap(result);
    }
    if (changes == 0) return false;
    clearIVRanges();
    dce(f);
    return true;
}

}  // namespace kopt
