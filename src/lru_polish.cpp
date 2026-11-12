// Register-touch polishing for programs with more register names than the
// machine keeps resident.
//
// When a program names more registers than `registers`, the machine spills by
// itself: before each instruction it touches the registers it reads (left to
// right) and then its destination, evicting the least recently used one. Which
// value is evicted therefore depends on touch order. Two edits change touch
// order without changing any value:
//   * swapping the two read operands of a commutative operation;
//   * inserting `mov r, r`, which touches r and leaves every register unchanged.
// A deterministic first-improvement search applies an edit only when the exact
// cycle model improves on the training inputs.
#include "passes.h"

#include <algorithm>
#include <set>

namespace kopt {
namespace {

bool commutativeRead(Op op) {
    return op == OP_ADD || op == OP_MUL || op == OP_AND || op == OP_OR ||
           op == OP_XOR || op == OP_EQ || op == OP_MAC;
}

}  // namespace

size_t registerNames(const Program &p) {
    std::set<uint32_t> names(p.params.begin(), p.params.end());
    for (const Block &b : p.blocks)
        for (const Instr &x : b.ins) {
            if (hasDest(x.op)) names.insert(x.dst);
            for (int i = 0; i < x.nsrc; ++i) if (x.src[i].isReg) names.insert(x.src[i].v);
        }
    return names.size();
}

Program lruPolish(const Program &input, const std::function<uint64_t(const Program &)> &cost,
                  size_t evaluations) {
    Program best = input;
    uint64_t bestCost = cost(best);
    if (bestCost == UINT64_MAX || evaluations == 0) return input;
    std::set<uint32_t> nameSet(input.params.begin(), input.params.end());
    for (const Block &b : input.blocks)
        for (const Instr &x : b.ins) {
            if (hasDest(x.op)) nameSet.insert(x.dst);
            for (int i = 0; i < x.nsrc; ++i) if (x.src[i].isReg) nameSet.insert(x.src[i].v);
        }
    const std::vector<uint32_t> names(nameSet.begin(), nameSet.end());
    size_t used = 1;
    auto attempt = [&](const Program &q) {
        if (used >= evaluations) return false;
        ++used;
        const uint64_t c = cost(q);
        if (c < bestCost) { bestCost = c; best = q; return true; }
        return false;
    };
    for (int round = 0; round < 8 && used < evaluations; ++round) {
        bool improved = false;
        // Operand swaps first: they add no instructions.
        for (size_t b = 0; b < best.blocks.size(); ++b)
            for (size_t i = 0; i < best.blocks[b].ins.size(); ++i) {
                const Instr &x = best.blocks[b].ins[i];
                if (!commutativeRead(x.op) || !x.src[0].isReg || !x.src[1].isReg || x.src[0] == x.src[1]) continue;
                Program q = best;
                std::swap(q.blocks[b].ins[i].src[0], q.blocks[b].ins[i].src[1]);
                if (attempt(q)) improved = true;
            }
        // Swap two adjacent independent instructions (at most one of them
        // has an effect or may trap, and neither reads or writes the other's
        // destination), which reorders their register touches.
        auto effect = [](Op op) {
            return op == OP_LOAD || op == OP_STORE || op == OP_VLOAD || op == OP_VSTORE ||
                   op == OP_DIV || op == OP_MOD || isTerminator(op);
        };
        auto touches = [](const Instr &x, uint32_t r) {
            if (hasDest(x.op) && x.dst == r) return true;
            for (int k = 0; k < x.nsrc; ++k) if (x.src[k].isReg && x.src[k].v == r) return true;
            return false;
        };
        for (size_t b = 0; b < best.blocks.size(); ++b)
            for (size_t i = 0; i + 2 < best.blocks[b].ins.size(); ++i) {
                const Instr &x = best.blocks[b].ins[i], &y = best.blocks[b].ins[i + 1];
                if (isTerminator(x.op) || isTerminator(y.op)) continue;
                if (effect(x.op) && effect(y.op)) continue;
                if (hasDest(x.op) && touches(y, x.dst)) continue;
                if (hasDest(y.op) && touches(x, y.dst)) continue;
                Program q = best;
                std::swap(q.blocks[b].ins[i], q.blocks[b].ins[i + 1]);
                if (attempt(q)) improved = true;
            }
        for (size_t b = 0; b < best.blocks.size(); ++b)
            for (size_t i = 0; i < best.blocks[b].ins.size(); ++i)
                for (uint32_t r : names) {
                    if (i < best.blocks[b].ins.size()) {
                        const Instr &x = best.blocks[b].ins[i];
                        // Touching a register the next instruction touches first is a no-op.
                        if (x.nsrc > 0 && x.src[0].isReg && x.src[0].v == r) continue;
                        if (x.op == OP_MOV && x.dst == r && x.src[0].isReg && x.src[0].v == r) continue;
                    }
                    Program q = best;
                    Instr touch;
                    touch.op = OP_MOV; touch.dst = r; touch.nsrc = 1; touch.src[0] = Operand::reg(r);
                    q.blocks[b].ins.insert(q.blocks[b].ins.begin() + i, touch);
                    if (attempt(q)) improved = true;
                }
        if (!improved) break;
    }
    return best;
}

}  // namespace kopt
