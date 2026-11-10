// Late, bounded live-range splitting for immutable ordinary constant loads.
#include "passes.h"

#include <array>
#include <vector>

namespace kopt {
namespace {

struct LoadRecipe {
    Inst load;
    int block = -1, barrier = 0, version = 0;
    bool safe = true, selected = false;
    std::vector<int> uses;  // Instruction sites; duplicate operands count once.
};

bool validAddress(Opnd o) { return o.isConst && o.c < kMemWords; }

}  // namespace

// Requires SSA. A clone can move only later within the defining block, and
// only over nontrapping work or ordinary constant accesses to other words.
// Same-address writes, unknown/trapping accesses, divisions that may trap,
// explicit traps and all volatile operations invalidate the entire recipe.
// No GVN after this pass: it would recreate the shared long live ranges.
bool rematerializeLoads(Func &f) {
    if (f.bb.size() > 256 || f.nvals > 20000) return false;
    size_t instructions = 0;
    for (const BB &b : f.bb) if (b.alive) instructions += b.insts.size();
    if (instructions > 4096) return false;
    f.resolveAll();
    const int nv = f.nvals;
    const int maxUses = 8, maxClones = 64, reuse = 16;
    std::vector<LoadRecipe> recipes(nv);
    for (int bi = 0; bi < static_cast<int>(f.bb.size()); bi++) {
        const BB &b = f.bb[bi];
        if (!b.alive) continue;
        for (const Inst &x : b.insts)
            if (x.op == OP_LOAD && x.dst >= 0 && validAddress(x.a[0])) {
                recipes[x.dst].load = x;
                recipes[x.dst].block = bi;
            }
    }
    for (const BB &b : f.bb) if (b.alive)
        for (const Phi &p : b.phis) for (const auto &in : p.in)
            if (!in.second.isConst) recipes[in.second.v].safe = false;

    // Version/barrier snapshots prove every def-to-use interval in one scan.
    // The consuming instruction reads its operands before its own effect, so
    // update versions AFTER inspecting uses (including store address/value).
    for (int bi = 0; bi < static_cast<int>(f.bb.size()); bi++) {
        const BB &b = f.bb[bi];
        if (!b.alive) continue;
        std::array<int, kMemWords> versions{};
        int barrier = 0;
        for (int i = 0; i < static_cast<int>(b.insts.size()); i++) {
            const Inst &x = b.insts[i];
            if (x.dst >= 0 && recipes[x.dst].block == bi) {
                LoadRecipe &r = recipes[x.dst];
                r.barrier = barrier; r.version = versions[r.load.a[0].c];
            }
            for (int a = 0; a < x.n; a++) {
                if (x.a[a].isConst) continue;
                LoadRecipe &r = recipes[x.a[a].v];
                if (r.block < 0) continue;
                if (r.block != bi) { r.safe = false; continue; }
                if (barrier != r.barrier || versions[r.load.a[0].c] != r.version) r.safe = false;
                if (r.uses.empty() || r.uses.back() != i)
                    if (r.uses.size() <= static_cast<size_t>(maxUses)) r.uses.push_back(i);
            }
            if (x.op == OP_STORE && validAddress(x.a[0])) versions[x.a[0].c]++;
            else if (x.op == OP_VLOAD || x.op == OP_VSTORE || x.op == OP_TRAP ||
                     ((x.op == OP_LOAD || x.op == OP_STORE) && !validAddress(x.a[0])) ||
                     ((x.op == OP_DIV || x.op == OP_MOD) && (!x.a[1].isConst || x.a[1].c == 0))) barrier++;
        }
    }
    int clones = 0;
    for (LoadRecipe &r : recipes) {
        if (r.block < 0 || !r.safe || r.uses.size() < 2 || r.uses.size() > static_cast<size_t>(maxUses)) continue;
        int groups = 0, first = -1000000;
        for (int i : r.uses) if (i - first > reuse) { groups++; first = i; }
        if (groups < 2 || clones + groups > maxClones) continue;
        clones += groups; r.selected = true;
    }
    if (clones == 0) return false;
    std::vector<Val> held(nv, -1);
    std::vector<int> at(nv, -1000000);
    for (BB &b : f.bb) {
        if (!b.alive) continue;
        std::vector<Inst> out;
        out.reserve(b.insts.size());
        for (int i = 0; i < static_cast<int>(b.insts.size()); i++) {
            Inst x = b.insts[i];
            for (int a = 0; a < x.n; a++) {
                if (x.a[a].isConst) continue;
                const int v = x.a[a].v;
                if (!recipes[v].selected) continue;
                if (held[v] < 0 || i - at[v] > reuse) {
                    Inst load = recipes[v].load;
                    load.dst = f.newVal(); out.push_back(load);
                    held[v] = load.dst; at[v] = i;
                }
                x.a[a] = Opnd::val(held[v]);
            }
            out.push_back(x);
        }
        b.insts.swap(out);
    }
    dce(f);
    return true;
}

}  // namespace kopt
