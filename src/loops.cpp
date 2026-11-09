#include "loops.h"

#include <algorithm>
#include <unordered_map>

#include "cfg.h"

namespace kopt {

Func toRegisterForm(const Program &p, std::vector<uint32_t> &regNames) {
    Func f;
    f.name = p.name;
    std::unordered_map<uint32_t, int> rid;
    regNames.clear();
    auto reg = [&](uint32_t r) {
        auto it = rid.find(r);
        if (it != rid.end()) return it->second;
        int id = static_cast<int>(regNames.size());
        rid.emplace(r, id);
        regNames.push_back(r);
        return id;
    };
    for (uint32_t r : p.params) f.params.push_back(reg(r));
    f.bb.resize(p.blocks.size());
    for (size_t b = 0; b < p.blocks.size(); b++) {
        BB &B = f.bb[b];
        B.label = p.blocks[b].label;
        for (const Instr &in : p.blocks[b].ins) {
            Inst x;
            x.op = in.op;
            x.k = static_cast<uint8_t>(in.k);
            x.n = static_cast<uint8_t>(in.nsrc);
            for (int s = 0; s < in.nsrc; s++)
                x.a[s] = in.src[s].isReg ? Opnd::val(reg(in.src[s].v)) : Opnd::cst(in.src[s].v);
            x.dst = hasDest(in.op) ? reg(in.dst) : -1;
            x.tgt[0] = in.target[0];
            x.tgt[1] = in.target[1];
            B.insts.push_back(x);
        }
    }
    f.nvals = static_cast<int>(regNames.size());
    f.fwd.clear();
    for (int v = 0; v < f.nvals; v++) f.fwd.push_back(Opnd::val(v));
    f.rebuildPreds();
    return f;
}

Program fromRegisterForm(Func &f, const std::vector<uint32_t> &regNames) {
    // Keep the entry first; drop unreachable blocks.
    f.rebuildPreds();
    DomInfo d = computeDominators(f);
    std::vector<int> order;
    for (int b = 0; b < static_cast<int>(f.bb.size()); b++)
        if (f.bb[b].alive && d.reachable(b)) order.push_back(b);
    std::vector<int> outIndex(f.bb.size(), -1);
    for (size_t i = 0; i < order.size(); i++) outIndex[order[i]] = static_cast<int>(i);
    Program p;
    p.name = f.name;
    uint32_t next = 0;
    for (uint32_t r : regNames) next = std::max(next, r + 1);
    auto name = [&](int v) { return regNames[v]; };
    for (Val v : f.params) p.params.push_back(name(v));
    for (size_t i = 0; i < order.size(); i++) {
        Block blk;
        blk.label = "R" + std::to_string(i);
        for (const Inst &x : f.bb[order[i]].insts) {
            Instr y;
            y.op = x.op;
            y.k = x.k;
            y.nsrc = x.n;
            if (x.dst >= 0) y.dst = name(x.dst);
            for (int a = 0; a < x.n; a++)
                y.src[a] = x.a[a].isConst ? Operand::imm(x.a[a].c) : Operand::reg(name(x.a[a].v));
            if (x.op == OP_JMP) y.target[0] = outIndex[x.tgt[0]];
            if (x.op == OP_BR) { y.target[0] = outIndex[x.tgt[0]]; y.target[1] = outIndex[x.tgt[1]]; }
            blk.ins.push_back(y);
        }
        p.blocks.push_back(blk);
    }
    (void)next;
    return p;
}

bool rotateLoops(Func &f, int maxHeaderSize) {
    f.rebuildPreds();
    DomInfo d = computeDominators(f);
    LoopInfo li = computeLoops(f, d);
    bool changed = false;
    for (const LoopInfo::Loop &L : li.loops) {
        const int h = L.header;
        if (h == 0) continue;
        const BB &H = f.bb[h];
        if (H.term().op != OP_BR || static_cast<int>(H.insts.size()) > maxHeaderSize) continue;
        std::vector<char> in(f.bb.size(), 0);
        for (int b : L.blocks) in[b] = 1;
        bool t0 = in[H.term().tgt[0]], t1 = in[H.term().tgt[1]];
        if (t0 == t1) continue;   // not an exit test
        for (int latch : L.latches) {
            BB &T = f.bb[latch];
            if (latch == h || T.term().op != OP_JMP || T.term().tgt[0] != h) continue;
            T.insts.pop_back();
            for (const Inst &x : f.bb[h].insts) T.insts.push_back(x);
            changed = true;
        }
    }
    if (changed) f.rebuildPreds();
    return changed;
}

bool unrollLoops(Func &f, int factor, int sizeBudget) {
    if (factor < 2) return false;
    f.rebuildPreds();
    DomInfo d = computeDominators(f);
    LoopInfo li = computeLoops(f, d);
    std::vector<bool> irr = irreducibleBlocks(f, d);
    bool changed = false;
    // Innermost loops only: no other loop's header inside them.
    for (size_t l = 0; l < li.loops.size(); l++) {
        const LoopInfo::Loop &L = li.loops[l];
        bool innermost = true;
        for (size_t o = 0; o < li.loops.size(); o++)
            if (o != l && li.loops[o].parent == static_cast<int>(l)) innermost = false;
        if (!innermost || irr[L.header] || L.header == 0) continue;
        int size = 0;
        for (int b : L.blocks) size += static_cast<int>(f.bb[b].insts.size());
        if (size * factor > sizeBudget) continue;
        const int n0 = static_cast<int>(f.bb.size());
        std::vector<char> in(n0, 0);
        for (int b : L.blocks) in[b] = 1;
        // clone[k][b] = index of the copy k of block b (copy 0 is the original).
        std::vector<std::unordered_map<int, int>> clone(factor);
        for (int b : L.blocks) clone[0][b] = b;
        for (int k = 1; k < factor; k++)
            for (int b : L.blocks) {
                clone[k][b] = static_cast<int>(f.bb.size());
                BB copy = f.bb[b];
                copy.label.clear();
                f.bb.push_back(copy);
            }
        for (int k = 0; k < factor; k++) {
            for (int b : L.blocks) {
                Inst &t = f.bb[clone[k][b]].term();
                int nt = (t.op == OP_JMP) ? 1 : (t.op == OP_BR ? 2 : 0);
                for (int s = 0; s < nt; s++) {
                    int target = t.tgt[s];
                    if (target >= n0 || !in[target]) continue;          // exit edge: unchanged
                    if (target == L.header) t.tgt[s] = clone[(k + 1) % factor][L.header];   // back edge
                    else t.tgt[s] = clone[k][target];
                }
            }
        }
        changed = true;
    }
    if (changed) f.rebuildPreds();
    return changed;
}

}  // namespace kopt
