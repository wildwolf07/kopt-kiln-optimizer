// Bounded SSA rematerialization. Call late, after simplification/DCE, and do
// not run GVN afterwards: it would recreate the long shared live ranges.
#include "passes.h"

#include <unordered_map>
#include <vector>

namespace kopt {
namespace {

bool rematAlu(const Inst &x, const Machine &m) {
    switch (x.op) {
    case OP_ADD: case OP_SUB: case OP_AND: case OP_OR: case OP_XOR:
    case OP_SHL: case OP_SHR: case OP_LT: case OP_EQ: case OP_SELECT:
        break;
    case OP_ADDSH:
        if (!m.fused_addsh) return false;
        break;
    default:
        return false;  // No memory, traps, multiply/divide, or recursive recipes.
    }
    return x.dst >= 0 && m.latency(x.op) <= m.lat_alu &&
           m.latency(x.op) < m.lat_load;
}

struct RematUse { int block, index; };
struct RematRecipe {
    Inst inst;
    std::vector<RematUse> uses;
    bool phiUse = false;
    bool chosen = false;
};

}  // namespace

// One ALU instruction with immutable parameter/literal leaves is safe to
// recompute immediately before any instruction use: its operands dominate
// every block, its result is bit-identical, and it has no effects or traps.
// Phi users are excluded, so no edge insertion or CFG changes are necessary.
bool rematerialize(Func &f, const Machine &m) {
    f.resolveAll();
    const int nv = f.nvals;
    const int maxUses = 8, minGap = 8, maxClones = 64;
    std::vector<char> param(nv, 0);
    for (Val p : f.params) param[p] = 1;
    std::vector<int> recipeOf(nv, -1);
    std::vector<RematRecipe> recipes;
    for (const BB &b : f.bb) {
        if (!b.alive) continue;
        for (const Inst &x : b.insts) {
            if (!rematAlu(x, m) || f.resolve(Opnd::val(x.dst)) != Opnd::val(x.dst)) continue;
            bool ok = true, hasParam = false;
            for (int a = 0; a < x.n; a++) if (!x.a[a].isConst) {
                if (!param[x.a[a].v]) ok = false;
                hasParam = true;
            }
            if (!ok || !hasParam) continue;
            recipeOf[x.dst] = static_cast<int>(recipes.size());
            RematRecipe r;
            r.inst = x;
            recipes.push_back(r);
        }
    }
    if (recipes.empty()) return false;

    // An anchor is an existing parameter read at/after a proposed clone in
    // the same block. Exclude ALL recipe definitions, even unselected ones:
    // moving two recipes must not invalidate each other's lifetime proof.
    std::vector<std::unordered_map<Val, int>> anchor(f.bb.size());
    for (int bi = 0; bi < static_cast<int>(f.bb.size()); bi++) {
        const BB &b = f.bb[bi];
        if (!b.alive) continue;
        for (const Phi &ph : b.phis) for (const auto &in : ph.in)
            if (!in.second.isConst && recipeOf[in.second.v] >= 0)
                recipes[recipeOf[in.second.v]].phiUse = true;
        for (int i = 0; i < static_cast<int>(b.insts.size()); i++) {
            const Inst &x = b.insts[i];
            const bool isRecipe = x.dst >= 0 && recipeOf[x.dst] >= 0;
            for (int a = 0; a < x.n; a++) {
                const Opnd o = x.a[a];
                if (o.isConst) continue;
                if (param[o.v] && !isRecipe) anchor[bi][o.v] = i;
                const int ri = recipeOf[o.v];
                if (ri < 0) continue;
                auto &uses = recipes[ri].uses;
                // Count instruction sites, not repeated operands of one use.
                if (!uses.empty() && uses.back().block == bi && uses.back().index == i) continue;
                if (uses.size() <= static_cast<size_t>(maxUses)) uses.push_back({bi, i});
            }
        }
    }

    int clones = 0;
    for (RematRecipe &r : recipes) {
        if (r.phiUse || r.uses.size() < 2 || r.uses.size() > static_cast<size_t>(maxUses)) continue;
        const RematUse first = r.uses.front(), last = r.uses.back();
        if (first.block == last.block && last.index - first.index < minGap) continue;
        bool available = true;
        for (const RematUse u : r.uses) for (int a = 0; a < r.inst.n; a++) {
            const Opnd o = r.inst.a[a];
            if (o.isConst) continue;
            const auto it = anchor[u.block].find(o.v);
            if (it == anchor[u.block].end() || it->second < u.index) available = false;
        }
        if (!available || clones + static_cast<int>(r.uses.size()) > maxClones) continue;
        r.chosen = true;
        clones += static_cast<int>(r.uses.size());
    }
    if (clones == 0) return false;

    // Only visit the original instructions. New definitions are fresh SSA
    // values; repeated references in a single instruction share one clone.
    for (BB &b : f.bb) {
        if (!b.alive) continue;
        std::vector<Inst> out;
        out.reserve(b.insts.size());
        for (Inst x : b.insts) {
            int seen[3] = {-1, -1, -1};
            Val temp[3] = {-1, -1, -1};
            int count = 0;
            for (int a = 0; a < x.n; a++) {
                if (x.a[a].isConst) continue;
                const int ri = recipeOf[x.a[a].v];
                if (ri < 0 || !recipes[ri].chosen) continue;
                int at = 0;
                while (at < count && seen[at] != ri) at++;
                if (at == count) {
                    Inst copy = recipes[ri].inst;
                    copy.dst = f.newVal();
                    out.push_back(copy);
                    seen[count] = ri;
                    temp[count++] = copy.dst;
                }
                x.a[a] = Opnd::val(temp[at]);
            }
            out.push_back(x);
        }
        b.insts.swap(out);
    }
    dce(f);  // Remove the now-unused original expressions; never GVN here.
    return true;
}

}  // namespace kopt
