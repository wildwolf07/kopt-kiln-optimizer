// Conservative late SSA sinking. No CFG edits, cloning, or value rewriting.
#include "cfg.h"

#include <vector>

namespace kopt {
namespace {

bool sinkPure(const Inst &x) {
    switch (x.op) {
    case OP_CONST: case OP_MOV: case OP_ADD: case OP_SUB: case OP_MUL:
    case OP_AND: case OP_OR: case OP_XOR: case OP_SHL: case OP_SHR:
    case OP_LT: case OP_EQ: case OP_SELECT: case OP_MAC: case OP_ADDSH:
        return x.dst >= 0;
    default:
        return false;  // Deliberately exclude even proven-safe div/load.
    }
}

struct SinkSite { int block = -1, index = -1; };

}  // namespace

// Only one instruction user is allowed (duplicate operands count as one
// user). Phi inputs pin their definitions. Moving a nontrapping pure op past
// effects, traps or branches cannot alter an observable result; it is either
// recomputed with the same immutable SSA operands or skipped on an unused path.
// Call before SSA destruction, preferably as an optional measured candidate.
bool sinkInstructions(Func &f) {
    // Existing dominance/natural-loop analyses have superlinear CFG costs.
    // Cap blocks independently of instruction count, then all value/use scans
    // and the iterative rewrite are O(instructions + values + phi inputs).
    if (f.bb.empty() || f.bb.size() > 256 || f.nvals > 300000) return false;
    size_t count = 0;
    for (const BB &b : f.bb) if (b.alive) count += b.insts.size();
    if (count > 100000) return false;
    f.resolveAll();
    f.rebuildPreds();
    const DomInfo dom = computeDominators(f);
    const LoopInfo loops = computeLoops(f, dom);
    const std::vector<bool> irr = irreducibleBlocks(f, dom);

    std::vector<Inst> inst;
    std::vector<SinkSite> site;
    std::vector<std::vector<int>> ids(f.bb.size());
    std::vector<SinkSite> def(f.nvals);
    std::vector<char> parameter(f.nvals, 0), phiUse(f.nvals, 0);
    std::vector<int> user(f.nvals, -1);
    for (Val p : f.params) parameter[p] = 1;
    for (int b : dom.rpo) {
        const BB &bb = f.bb[b];
        for (const Phi &ph : bb.phis) {
            def[ph.dst] = {b, -1};  // Phi is available at block entry.
            for (const auto &in : ph.in) if (!in.second.isConst) phiUse[in.second.v] = 1;
        }
        for (int i = 0; i < static_cast<int>(bb.insts.size()); i++) {
            const Inst &x = bb.insts[i];
            const int id = static_cast<int>(inst.size());
            ids[b].push_back(id);
            inst.push_back(x);
            site.push_back({b, i});
            if (x.dst >= 0) def[x.dst] = {b, i};
            for (int a = 0; a < x.n; a++) if (!x.a[a].isConst) {
                int &u = user[x.a[a].v];
                if (u == -1) u = id;
                else if (u != id) u = -2;
            }
        }
    }

    // Each moved instruction has exactly one parent (its user). Parents
    // follow children in dominance/RPO and instruction order, so this forest
    // has no cycles, including loop-carried values (their phi uses are pinned).
    std::vector<char> moved(inst.size(), 0);
    std::vector<std::vector<int>> before(inst.size());
    for (int id = 0; id < static_cast<int>(inst.size()); id++) {
        const Inst &x = inst[id];
        if (!sinkPure(x) || phiUse[x.dst] || user[x.dst] < 0) continue;
        const int u = user[x.dst];
        const SinkSite from = site[id], to = site[u];
        if (from.block == to.block) {
            if (from.index >= to.index) continue;  // Never move past an old use.
        } else {
            if (!dom.dominates(from.block, to.block) || irr[from.block] || irr[to.block]) continue;
            if (loops.depth[to.block] > loops.depth[from.block]) continue;
            const int targetLoop = loops.innermost[to.block];
            if (targetLoop >= 0 && !loops.inLoop(from.block, targetLoop)) continue;
        }
        bool available = true;
        for (int a = 0; a < x.n; a++) {
            const Opnd o = x.a[a];
            if (o.isConst || parameter[o.v]) continue;
            const SinkSite ds = def[o.v];
            if (ds.block < 0 || !dom.dominates(ds.block, to.block) ||
                (ds.block == to.block && ds.index >= to.index)) available = false;
        }
        if (!available) continue;
        moved[id] = 1;
        before[u].push_back(id);  // Original order is the deterministic tie-break.
    }

    bool changed = false;
    std::vector<int> stack;
    for (int b : dom.rpo) {
        std::vector<Inst> out;
        out.reserve(ids[b].size());
        for (int root : ids[b]) {
            if (moved[root]) continue;
            stack.push_back(root);
            while (!stack.empty()) {
                const int id = stack.back();
                stack.pop_back();
                if (id < 0) {
                    const int emit = -id - 1;
                    if (site[emit].block != b || site[emit].index != static_cast<int>(out.size())) changed = true;
                    out.push_back(inst[emit]);
                } else {
                    stack.push_back(-id - 1);
                    for (auto it = before[id].rbegin(); it != before[id].rend(); ++it) stack.push_back(*it);
                }
            }
        }
        f.bb[b].insts.swap(out);
    }
    return changed;
}

}  // namespace kopt
