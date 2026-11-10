// Exact distance-one load reuse across a two-block counted loop.
#include "passes.h"
#include "cfg.h"

#include <algorithm>
#include <vector>

namespace kopt {
namespace {

bool ordinaryPure(Op op) {
    switch (op) {
        case OP_CONST: case OP_MOV: case OP_ADD: case OP_SUB: case OP_MUL:
        case OP_AND: case OP_OR: case OP_XOR: case OP_SHL: case OP_SHR:
        case OP_LT: case OP_EQ: case OP_SELECT: case OP_MAC: case OP_ADDSH:
            return true;
        default: return false;
    }
}

struct Affine {
    bool known = false, variable = false;
    uint32_t offset = 0;
};

}  // namespace

// Returns after one promotion, so every analysis is fresh on the next call.
// Stores are retained. A successful preceding access establishes both the
// carried value and validity of the next iteration's eliminated load.
bool promoteRollingLoad(Func &f) {
    if (f.bb.size() > 256 || f.nvals > 10000) return false;
    size_t size = 0;
    for (const BB &b : f.bb) if (b.alive) size += b.insts.size();
    if (size > 2000) return false;
    f.resolveAll(); f.rebuildPreds();
    const DomInfo dom = computeDominators(f);
    const LoopInfo loops = computeLoops(f, dom);
    std::vector<int> defBlock(f.nvals, -1), defAt(f.nvals, -1);
    for (int b = 0; b < static_cast<int>(f.bb.size()); ++b) if (f.bb[b].alive)
        for (int i = 0; i < static_cast<int>(f.bb[b].insts.size()); ++i) {
            const Inst &x = f.bb[b].insts[i];
            if (x.dst >= 0) { defBlock[x.dst] = b; defAt[x.dst] = i; }
        }
    unsigned proofWork = 50000;
    for (const auto &loop : loops.loops) {
        if (loop.blocks.size() != 2 || loop.latches.size() != 1) continue;
        const int h = loop.header, b = loop.latches[0];
        if (b == h || f.bb[h].preds.size() != 2 || f.bb[b].preds != std::vector<int>{h} ||
            !f.bb[b].phis.empty() || f.bb[b].term().op != OP_JMP || f.bb[b].term().tgt[0] != h ||
            f.bb[h].term().op != OP_BR) continue;
        const Inst ht = f.bb[h].term();
        if ((ht.tgt[0] == b) == (ht.tgt[1] == b)) continue;
        const int outside = f.bb[h].preds[0] == b ? f.bb[h].preds[1] : f.bb[h].preds[0];
        if (outside == h || outside == b || loops.inLoop(outside, static_cast<int>(&loop - loops.loops.data()))) continue;
        bool pureHeader = true, ordinaryBody = true;
        for (size_t i = 0; i + 1 < f.bb[h].insts.size(); ++i)
            if (!ordinaryPure(f.bb[h].insts[i].op)) pureHeader = false;
        for (size_t i = 0; i + 1 < f.bb[b].insts.size(); ++i) {
            const Op op = f.bb[b].insts[i].op;
            if (!ordinaryPure(op) && op != OP_LOAD && op != OP_STORE) ordinaryBody = false;
        }
        if (!pureHeader || !ordinaryBody) continue;
        for (const Phi &iv : f.bb[h].phis) {
            if (iv.in.size() != 2) continue;
            Opnd initial, back;
            bool haveInitial = false, haveBack = false;
            for (const auto &in : iv.in) {
                if (in.first == outside) { initial = in.second; haveInitial = true; }
                if (in.first == b) { back = in.second; haveBack = true; }
            }
            if (!haveInitial || !haveBack || !initial.isConst) continue;
            auto form = [&](auto &&self, Opnd o, int depth) -> Affine {
                if (proofWork == 0) return {};
                --proofWork;
                if (o.isConst) return {true, false, o.c};
                if (o.v == iv.dst) return {true, true, 0};
                if (depth == 0 || defBlock[o.v] < 0) return {};
                const Inst x = f.bb[defBlock[o.v]].insts[defAt[o.v]];
                if (x.op == OP_CONST || x.op == OP_MOV) return self(self, x.a[0], depth - 1);
                if (x.op != OP_ADD && x.op != OP_SUB) return {};
                const Affine a = self(self, x.a[0], depth - 1), c = self(self, x.a[1], depth - 1);
                if (!a.known || !c.known || (a.variable && c.variable) || (x.op == OP_SUB && c.variable)) return {};
                return {true, a.variable || c.variable, x.op == OP_ADD ? a.offset + c.offset : a.offset - c.offset};
            };
            const Affine next = form(form, back, 12);
            if (!next.known || !next.variable || next.offset == 0) continue;
            for (size_t at = 0; at + 1 < f.bb[b].insts.size(); ++at) {
                const Inst load = f.bb[b].insts[at];
                if (load.op != OP_LOAD) {
                    if (!ordinaryPure(load.op)) break;  // First effect is the load being removed.
                    continue;
                }
                const Affine address = form(form, load.a[0], 12);
                if (!address.known || !address.variable) break;
                const uint32_t first = initial.c + address.offset;
                if (first >= kMemWords) break;  // Zero-trip speculative initial read must be valid.
                const uint32_t wanted = address.offset + next.offset;
                Opnd carried; bool found = false, blocked = false;
                for (size_t j = f.bb[b].insts.size() - 1; j-- > at + 1;) {
                    const Inst x = f.bb[b].insts[j];
                    if (x.op != OP_LOAD && x.op != OP_STORE) continue;
                    const Affine a = form(form, x.a[0], 12);
                    if (a.known && a.variable && a.offset == wanted) {
                        carried = x.op == OP_LOAD ? Opnd::val(x.dst) : x.a[1]; found = true; break;
                    }
                    if (x.op == OP_STORE && !(a.known && a.variable && a.offset != wanted)) { blocked = true; break; }
                }
                if (!found || blocked) break;
                Inst pre; pre.op = OP_LOAD; pre.dst = f.newVal(); pre.n = 1; pre.a[0] = Opnd::cst(first);
                Phi memory; memory.dst = f.newVal(); memory.in = {{outside, Opnd::val(pre.dst)}, {b, carried}};
                f.bb[outside].insts.insert(f.bb[outside].insts.end() - 1, pre);
                f.bb[h].phis.push_back(memory);
                f.replaceAll(load.dst, Opnd::val(memory.dst));
                Inst &old = f.bb[b].insts[at]; old.op = OP_MOV; old.n = 1; old.a[0] = Opnd::val(memory.dst);
                clearIVRanges(); dce(f);
                return true;
            }
        }
    }
    return false;
}

}  // namespace kopt
