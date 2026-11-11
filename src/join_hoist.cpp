// Hoist total pure work above branches whose other side has visible effects.
//
// hoistPureArms: a branch arm that holds only pure work and jumps to a join is
// emptied into the branch block; the branch then targets the join directly and
// the join's phis receive the hoisted values on the new edge. The arm's work now
// also runs on the other path, where nothing reads it. Only total operations
// (no division, memory or volatile access) move, so no trap or effect changes.
//
// hoistToIdom: pure work of a block whose immediate dominator ends in a branch
// moves into that dominator when its operands are already available there. The
// dominator reaches every use, so every value is unchanged where it is read.
#include "passes.h"
#include "cfg.h"

#include <algorithm>
#include <vector>

namespace kopt {
namespace {

bool totalOp(Op op) {
    switch (op) {
    case OP_CONST: case OP_MOV: case OP_ADD: case OP_SUB: case OP_MUL: case OP_AND:
    case OP_OR: case OP_XOR: case OP_SHL: case OP_SHR: case OP_LT: case OP_EQ:
    case OP_SELECT: case OP_MAC: case OP_ADDSH:
        return true;
    default:
        return false;
    }
}

}  // namespace

bool hoistPureArms(Func &f, int budget) {
    if (f.bb.size() > 512) return false;
    f.resolveAll();
    f.rebuildPreds();
    bool changed = false;
    for (int d = 0; d < static_cast<int>(f.bb.size()); ++d) {
        if (!f.bb[d].alive || f.bb[d].insts.empty() || f.bb[d].term().op != OP_BR) continue;
        for (int side = 0; side < 2; ++side) {
            const Inst &br = f.bb[d].term();
            const int s = br.tgt[side], o = br.tgt[1 - side];
            if (s == o || s == 0 || s == d) continue;
            const BB &S = f.bb[s];
            if (!S.alive || S.preds != std::vector<int>{d} || !S.phis.empty() || S.term().op != OP_JMP) continue;
            const int j = S.term().tgt[0];
            if (j == s || j == d || j == o) continue;
            const BB &J = f.bb[j];
            if (std::find(J.preds.begin(), J.preds.end(), d) != J.preds.end()) continue;
            if (static_cast<int>(S.insts.size()) - 1 > budget) continue;
            bool pure = true;
            for (size_t i = 0; i + 1 < S.insts.size(); ++i)
                if (!totalOp(S.insts[i].op) || S.insts[i].dst < 0) pure = false;
            if (!pure) continue;
            BB &D = f.bb[d];
            std::vector<Inst> moved(S.insts.begin(), S.insts.end() - 1);
            D.insts.insert(D.insts.end() - 1, moved.begin(), moved.end());
            D.term().tgt[side] = j;
            for (Phi &phi : f.bb[j].phis)
                for (auto &edge : phi.in) if (edge.first == s) edge.first = d;
            BB &dead = f.bb[s];
            dead.alive = false;
            dead.phis.clear();
            Inst jump; jump.op = OP_JMP; jump.tgt[0] = j;
            dead.insts.assign(1, jump);
            f.rebuildPreds();
            changed = true;
            break;
        }
    }
    if (changed) clearIVRanges();
    return changed;
}

bool hoistToIdom(Func &f, int budget) {
    if (f.bb.size() > 512 || f.nvals > 50000) return false;
    f.resolveAll();
    f.rebuildPreds();
    const DomInfo dom = computeDominators(f);
    const LoopInfo loops = computeLoops(f, dom);
    std::vector<char> local(f.nvals, 0);
    bool changed = false;
    int total = 0;
    for (size_t r = 1; r < dom.rpo.size(); ++r) {
        const int j = dom.rpo[r];
        const int d = dom.idom[j];
        if (d < 0 || d == j || !f.bb[j].alive || !f.bb[d].alive) continue;
        if (f.bb[d].term().op != OP_BR) continue;
        if (loops.innermost[j] != loops.innermost[d]) continue;
        BB &J = f.bb[j];
        for (const Phi &phi : J.phis) local[phi.dst] = 1;
        for (const Inst &x : J.insts) if (x.dst >= 0) local[x.dst] = 1;
        std::vector<Inst> keep, moved;
        for (size_t i = 0; i + 1 < J.insts.size(); ++i) {
            const Inst &x = J.insts[i];
            bool ok = x.dst >= 0 && totalOp(x.op) && x.op != OP_CONST && total < budget;
            for (int a = 0; ok && a < x.n; ++a)
                if (!x.a[a].isConst && x.a[a].v < static_cast<int>(local.size()) && local[x.a[a].v]) ok = false;
            if (ok) { moved.push_back(x); local[x.dst] = 0; ++total; }
            else keep.push_back(x);
        }
        for (const Phi &phi : J.phis) local[phi.dst] = 0;
        for (const Inst &x : J.insts) if (x.dst >= 0) local[x.dst] = 0;
        if (moved.empty()) continue;
        keep.push_back(J.term());
        J.insts.swap(keep);
        BB &D = f.bb[d];
        D.insts.insert(D.insts.end() - 1, moved.begin(), moved.end());
        changed = true;
    }
    if (changed) clearIVRanges();
    return changed;
}

}  // namespace kopt
