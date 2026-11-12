// Boolean trees: rewrite a pure tree of and/or/xor (and add/sub that provably
// act bitwise) over at most three operands as a cheapest equivalent formula.
//
// Every bit of an and/or/xor result is the same boolean function of the same
// bit of each operand (the constants 0 and 0xFFFFFFFF are uniform too), so the
// tree is described exactly by an 8-entry truth table over its leaves. Two exact
// arithmetic rules extend the domain: when x and y never share a set bit,
// x + y = x | y (no carries); when every set bit of y is set in x,
// x - y = x & ~y (no borrows). The truth tables prove those conditions for
// all inputs. A formula-size table over all 256 functions (operators and, or,
// xor; "not" is xor with 0xFFFFFFFF) gives the replacement.
#include "passes.h"

#include <array>
#include <vector>

namespace kopt {
namespace {

constexpr uint8_t kVar[3] = {0xF0, 0xCC, 0xAA};
constexpr int kInf = 1 << 20;

struct Formula {
    int cost = kInf, depth = kInf;
    int op = -1;               // -1 leaf/constant, else OP_AND/OP_OR/OP_XOR
    uint8_t a = 0, b = 0;      // operand truth tables
};

const std::array<Formula, 256> &formulas() {
    static const std::array<Formula, 256> table = [] {
        std::array<Formula, 256> t{};
        for (uint8_t v : kVar) t[v] = Formula{0, 0, -1, 0, 0};
        t[0x00] = Formula{0, 0, -1, 0, 0};
        t[0xFF] = Formula{0, 0, -1, 0, 0};
        for (bool changed = true; changed;) {
            changed = false;
            for (int x = 0; x < 256; ++x) {
                if (t[x].cost >= kInf) continue;
                for (int y = x; y < 256; ++y) {
                    if (t[y].cost >= kInf) continue;
                    const int cost = t[x].cost + t[y].cost + 1;
                    const int depth = std::max(t[x].depth, t[y].depth) + 1;
                    const int ops[3] = {OP_AND, OP_OR, OP_XOR};
                    const int res[3] = {x & y, x | y, x ^ y};
                    for (int k = 0; k < 3; ++k) {
                        Formula &r = t[res[k]];
                        if (cost < r.cost || (cost == r.cost && depth < r.depth)) {
                            r = Formula{cost, depth, ops[k], static_cast<uint8_t>(x), static_cast<uint8_t>(y)};
                            changed = true;
                        }
                    }
                }
            }
        }
        return t;
    }();
    return table;
}

struct Tree {
    std::vector<Opnd> leaves;
    std::vector<Val> nodes;     // internal values of the tree (root first)
    bool ok = true;
};

}  // namespace

bool booleanTrees(Func &f) {
    if (f.nvals > 60000) return false;
    f.resolveAll();
    // Copies: block instruction lists are replaced while scanning. A rewritten
    // root keeps its value, so a copied definition stays a true equation.
    std::vector<Inst> defs(f.nvals);
    std::vector<char> has(f.nvals, 0);
    std::vector<int> uses(f.nvals, 0);
    const int known = f.nvals;
    for (const BB &b : f.bb) {
        if (!b.alive) continue;
        for (const Phi &p : b.phis) for (const auto &in : p.in) if (!in.second.isConst) ++uses[in.second.v];
        for (const Inst &x : b.insts) {
            if (x.dst >= 0) { defs[x.dst] = x; has[x.dst] = 1; }
            for (int i = 0; i < x.n; ++i) if (!x.a[i].isConst) ++uses[x.a[i].v];
        }
    }
    const auto &table = formulas();
    // Truth table of operand o, adding leaves to t. Returns -1 when o is not
    // expressible within three leaves.
    std::function<int(Opnd, Tree &, int, bool)> tt = [&](Opnd o, Tree &t, int depth, bool top) -> int {
        if (o.isConst && o.c == 0) return 0x00;
        if (o.isConst && o.c == 0xFFFFFFFFu) return 0xFF;
        const Inst *x = (o.isConst || o.v >= known || !has[o.v]) ? nullptr : &defs[o.v];
        const bool inner = x && depth > 0 && x->n == 2 &&
                           (x->op == OP_AND || x->op == OP_OR || x->op == OP_XOR ||
                            x->op == OP_ADD || x->op == OP_SUB);
        if (inner) {
            Tree save = t;
            const int a = tt(x->a[0], t, depth - 1, false);
            const int b = a < 0 ? -1 : tt(x->a[1], t, depth - 1, false);
            int r = -1;
            if (a >= 0 && b >= 0) {
                switch (x->op) {
                case OP_AND: r = a & b; break;
                case OP_OR: r = a | b; break;
                case OP_XOR: r = a ^ b; break;
                case OP_ADD: if ((a & b) == 0) r = a | b; break;
                case OP_SUB: if ((b & ~a & 0xFF) == 0) r = a & ~b & 0xFF; break;
                default: break;
                }
            }
            if (r >= 0) {
                if (!top) t.nodes.push_back(o.v);
                return r;
            }
            t = save;
            if (top) return -1;
        }
        for (size_t i = 0; i < t.leaves.size(); ++i) if (t.leaves[i] == o) return kVar[i];
        if (t.leaves.size() == 3) return -1;
        t.leaves.push_back(o);
        return kVar[t.leaves.size() - 1];
    };
    bool changed = false;
    for (BB &b : f.bb) {
        if (!b.alive) continue;
        std::vector<Inst> out;
        out.reserve(b.insts.size());
        for (const Inst &x : b.insts) {
            const bool cand = x.dst >= 0 && x.n == 2 &&
                              (x.op == OP_AND || x.op == OP_OR || x.op == OP_XOR || x.op == OP_ADD || x.op == OP_SUB);
            if (!cand) { out.push_back(x); continue; }
            Tree t;
            const int r = tt(Opnd::val(x.dst), t, 6, true);
            if (r < 0) { out.push_back(x); continue; }
            // Restrict to the variables actually present.
            int current = 1;   // the root itself
            for (Val v : t.nodes) if (v < known && uses[v] == 1) ++current;
            const Formula &best = table[r];
            if (best.cost >= current) { out.push_back(x); continue; }
            // Emit the formula; operand truth tables map to leaves/constants.
            std::function<Opnd(uint8_t, bool)> build = [&](uint8_t v, bool root) -> Opnd {
                if (v == 0x00) return Opnd::cst(0);
                if (v == 0xFF) return Opnd::cst(0xFFFFFFFFu);
                for (int i = 0; i < 3; ++i)
                    if (v == kVar[i]) return i < static_cast<int>(t.leaves.size()) ? t.leaves[i] : Opnd::cst(0);
                const Formula &g = table[v];
                Inst y;
                y.op = static_cast<Op>(g.op);
                y.n = 2;
                y.a[0] = build(g.a, false);
                y.a[1] = build(g.b, false);
                y.dst = root ? x.dst : f.newVal();
                out.push_back(y);
                return Opnd::val(y.dst);
            };
            const Formula &g = table[r];
            if (g.op < 0) {
                Inst y; y.op = OP_MOV; y.n = 1; y.dst = x.dst; y.a[0] = build(static_cast<uint8_t>(r), false);
                out.push_back(y);
            } else {
                build(static_cast<uint8_t>(r), true);
            }
            changed = true;
        }
        b.insts.swap(out);
    }
    if (changed) {
        clearIVRanges();
        dce(f);
    }
    return changed;
}

}  // namespace kopt
