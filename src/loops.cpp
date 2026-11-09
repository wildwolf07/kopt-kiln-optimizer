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

bool peelLoops(Func &f, int count, int sizeBudget) {
    if (count < 1) return false;
    f.rebuildPreds();
    DomInfo d = computeDominators(f);
    LoopInfo li = computeLoops(f, d);
    std::vector<bool> irr = irreducibleBlocks(f, d);
    bool changed = false;
    for (size_t l = 0; l < li.loops.size(); l++) {
        const LoopInfo::Loop &L = li.loops[l];
        bool innermost = true;
        for (size_t o = 0; o < li.loops.size(); o++)
            if (o != l && li.loops[o].parent == static_cast<int>(l)) innermost = false;
        if (!innermost || irr[L.header] || L.header == 0) continue;
        int size = 0;
        for (int b : L.blocks) size += static_cast<int>(f.bb[b].insts.size());
        if (size * count > sizeBudget) continue;
        const int n0 = static_cast<int>(f.bb.size());
        std::vector<char> in(n0, 0);
        for (int b : L.blocks) in[b] = 1;
        // clone[k][b]: peeled copy k (1..count) of block b.
        std::vector<std::unordered_map<int, int>> clone(count + 1);
        for (int k = 1; k <= count; k++)
            for (int b : L.blocks) {
                clone[k][b] = static_cast<int>(f.bb.size());
                BB copy = f.bb[b];
                copy.label.clear();
                f.bb.push_back(copy);
            }
        for (int k = 1; k <= count; k++)
            for (int b : L.blocks) {
                Inst &t = f.bb[clone[k][b]].term();
                int nt = (t.op == OP_JMP) ? 1 : (t.op == OP_BR ? 2 : 0);
                for (int s2 = 0; s2 < nt; s2++) {
                    int target = t.tgt[s2];
                    if (target >= n0 || !in[target]) continue;   // exit: unchanged
                    if (target == L.header) t.tgt[s2] = (k < count) ? clone[k + 1][L.header] : L.header;
                    else t.tgt[s2] = clone[k][target];
                }
            }
        // Entries from outside the loop go to the first peeled copy.
        for (int b = 0; b < n0; b++) {
            if (in[b] || !f.bb[b].alive) continue;
            Inst &t = f.bb[b].term();
            int nt = (t.op == OP_JMP) ? 1 : (t.op == OP_BR ? 2 : 0);
            for (int s2 = 0; s2 < nt; s2++)
                if (t.tgt[s2] == L.header) t.tgt[s2] = clone[1][L.header];
        }
        changed = true;
    }
    if (changed) f.rebuildPreds();
    return changed;
}

// Loop unswitching: a branch inside a loop on a register the loop never
// writes takes the same side in every round. Copy the loop, test the register
// once before it, and turn the branch into a jump in each copy. Then each copy
// is simpler (in one, a guarded division can leave the loop; in both, the
// branch and its taken-jump cost disappear).
bool unswitchLoops(Func &f, int sizeBudget) {
    f.rebuildPreds();
    DomInfo d = computeDominators(f);
    LoopInfo li = computeLoops(f, d);
    std::vector<bool> irr = irreducibleBlocks(f, d);
    std::vector<char> done(f.bb.size(), 0);   // blocks already copied in this call
    bool changed = false;
    // Innermost loops first (deepest), one unswitch per loop.
    std::vector<int> order(li.loops.size());
    for (size_t i = 0; i < order.size(); i++) order[i] = static_cast<int>(i);
    std::stable_sort(order.begin(), order.end(), [&](int a, int b) { return li.loops[a].depth > li.loops[b].depth; });
    for (int l : order) {
        const LoopInfo::Loop L = li.loops[l];
        const int h = L.header;
        if (irr[h] || h == 0) continue;
        bool touched = false;
        for (int b : L.blocks) if (done[b]) touched = true;
        if (touched) continue;
        const int n0 = static_cast<int>(f.bb.size());
        std::vector<char> in(n0, 0);
        int size = 0;
        for (int b : L.blocks) { in[b] = 1; size += static_cast<int>(f.bb[b].insts.size()); }
        if (size * 2 > sizeBudget) continue;
        int cb = -1;
        for (int b : L.blocks) {
            const Inst &t = f.bb[b].term();
            if (t.op != OP_BR || t.a[0].isConst || t.tgt[0] == t.tgt[1]) continue;
            const int r = t.a[0].v;
            bool written = false;
            for (int c : L.blocks)
                for (const Inst &x : f.bb[c].insts) if (x.dst == r) written = true;
            if (!written) { cb = b; break; }
        }
        if (cb < 0) continue;
        const Opnd cond = f.bb[cb].term().a[0];
        std::unordered_map<int, int> clone;
        for (int b : L.blocks) {
            clone[b] = static_cast<int>(f.bb.size());
            BB copy = f.bb[b];
            copy.label.clear();
            f.bb.push_back(copy);
        }
        for (int b : L.blocks) {
            Inst &t = f.bb[clone[b]].term();
            int nt = (t.op == OP_JMP) ? 1 : (t.op == OP_BR ? 2 : 0);
            for (int s2 = 0; s2 < nt; s2++)
                if (t.tgt[s2] < n0 && in[t.tgt[s2]]) t.tgt[s2] = clone[t.tgt[s2]];
        }
        // Original: the condition is true. Copy: it is false.
        {
            Inst &t = f.bb[cb].term();
            int tg = t.tgt[0];
            t.op = OP_JMP; t.n = 0; t.tgt[0] = tg; t.tgt[1] = -1;
            Inst &u = f.bb[clone[cb]].term();
            int fg = u.tgt[1];
            u.op = OP_JMP; u.n = 0; u.tgt[0] = fg; u.tgt[1] = -1;
        }
        const int U = static_cast<int>(f.bb.size());
        {
            BB ub;
            Inst br;
            br.op = OP_BR; br.n = 1; br.a[0] = cond; br.tgt[0] = h; br.tgt[1] = clone[h];
            ub.insts.push_back(br);
            f.bb.push_back(ub);
        }
        for (int b = 0; b < n0; b++) {
            if (in[b] || !f.bb[b].alive) continue;
            Inst &t = f.bb[b].term();
            int nt = (t.op == OP_JMP) ? 1 : (t.op == OP_BR ? 2 : 0);
            for (int s2 = 0; s2 < nt; s2++) if (t.tgt[s2] == h) t.tgt[s2] = U;
        }
        for (int b : L.blocks) done[b] = 1;
        done.resize(f.bb.size(), 1);
        changed = true;
    }
    if (changed) f.rebuildPreds();
    return changed;
}

namespace {

// Does `b` write register r?
bool writes(const BB &b, int r) {
    for (const Inst &x : b.insts) if (x.dst == r) return true;
    return false;
}

// Known truth of register r at the end of block p, or -1 if unknown.
int knownAtEnd(const Func &f, int p, int r, int depth) {
    const BB &P = f.bb[p];
    for (int i = static_cast<int>(P.insts.size()) - 1; i >= 0; i--) {
        const Inst &x = P.insts[i];
        if (x.dst != r) continue;
        if (x.op == OP_MOV && x.a[0].isConst) return x.a[0].c != 0 ? 1 : 0;
        return -1;
    }
    if (depth <= 0 || P.preds.size() != 1) return -1;
    const int q = P.preds[0];
    const Inst &t = f.bb[q].term();
    // q's branch reads r at q's very end, and p does not write r: same value.
    if (t.op == OP_BR && !t.a[0].isConst && t.a[0].v == r && t.tgt[0] != t.tgt[1])
        return t.tgt[0] == p ? 1 : 0;
    return knownAtEnd(f, q, r, depth - 1);
}

}  // namespace

bool threadJumps(Func &f, int maxBlockSize, int maxNewInstrs) {
    f.rebuildPreds();
    bool changed = false;
    int added = 0;
    for (int round = 0; round < 8 && added < maxNewInstrs; round++) {
        bool any = false;
        const int n0 = static_cast<int>(f.bb.size());
        for (int b = 1; b < n0 && added < maxNewInstrs; b++) {
            BB &B = f.bb[b];
            if (!B.alive || B.term().op != OP_BR || B.term().a[0].isConst) continue;
            if (static_cast<int>(B.insts.size()) > maxBlockSize) continue;
            const int r = B.term().a[0].v;
            if (writes(B, r)) continue;   // the tested value is computed in B itself
            std::vector<int> preds = f.bb[b].preds;
            for (int p : preds) {
                if (p == b) continue;
                int known = -1;
                const Inst &pt = f.bb[p].term();
                if (pt.op == OP_BR && !pt.a[0].isConst && pt.a[0].v == r && pt.tgt[0] != pt.tgt[1])
                    known = (pt.tgt[0] == b) ? 1 : 0;   // p just tested r and came here
                else
                    known = knownAtEnd(f, p, r, 4);
                if (known < 0) continue;
                const int nb = static_cast<int>(f.bb.size());
                BB copy = f.bb[b];
                copy.label.clear();
                Inst &t = copy.term();
                const int target = known ? t.tgt[0] : t.tgt[1];
                t.op = OP_JMP;
                t.n = 0;
                t.tgt[0] = target;
                t.tgt[1] = -1;
                added += static_cast<int>(copy.insts.size());
                f.bb.push_back(copy);
                Inst &ptm = f.bb[p].term();
                int nt = (ptm.op == OP_JMP) ? 1 : (ptm.op == OP_BR ? 2 : 0);
                for (int s2 = 0; s2 < nt; s2++) if (ptm.tgt[s2] == b) ptm.tgt[s2] = nb;
                any = changed = true;
                f.rebuildPreds();
            }
        }
        if (!any) break;
    }
    if (changed) f.rebuildPreds();
    return changed;
}

bool countedUnroll(Func &f, std::vector<uint32_t> &regNames, int factor, int sizeBudget, bool chainRemainder) {
    if (factor < 2) return false;
    f.rebuildPreds();
    DomInfo d = computeDominators(f);
    LoopInfo li = computeLoops(f, d);
    std::vector<bool> irr = irreducibleBlocks(f, d);
    bool changed = false;
    uint32_t nextName = 0;
    for (uint32_t r : regNames) nextName = std::max(nextName, r + 1);
    auto freshReg = [&]() {
        int v = f.newVal();
        regNames.push_back(nextName++);
        return v;
    };
    for (size_t l = 0; l < li.loops.size(); l++) {
        const LoopInfo::Loop L = li.loops[l];
        bool innermost = true;
        for (size_t o = 0; o < li.loops.size(); o++)
            if (o != l && li.loops[o].parent == static_cast<int>(l)) innermost = false;
        const int h = L.header;
        if (!innermost || irr[h] || h == 0 || L.latches.size() != 1) continue;
        const int t = L.latches[0];
        std::vector<char> in(f.bb.size(), 0);
        for (int b : L.blocks) in[b] = 1;
        const BB &T = f.bb[t];
        const Inst br = T.term();   // a copy: f.bb grows below
        if (br.op != OP_BR || br.a[0].isConst || br.tgt[0] != h || in[br.tgt[1]]) continue;
        const int c = br.a[0].v;
        // Find "lt c, i, n" and "add i, i, s" in T: the add before the lt, and
        // no other write of i, n or c after them in T.
        int ltPos = -1, addPos = -1;
        for (int k = static_cast<int>(T.insts.size()) - 2; k >= 0; k--)
            if (T.insts[k].dst == c) { ltPos = k; break; }
        if (ltPos < 0 || T.insts[ltPos].op != OP_LT || T.insts[ltPos].a[0].isConst) continue;
        const int iv = T.insts[ltPos].a[0].v;
        const Opnd n = T.insts[ltPos].a[1];
        if (!n.isConst && n.v == iv) continue;
        for (int k = ltPos - 1; k >= 0; k--)
            if (T.insts[k].dst == iv) { addPos = k; break; }
        if (addPos < 0) continue;
        const Inst &add = T.insts[addPos];
        // Step: a positive constant, or a register not written in the loop
        // (then checked at run time: 0 < s < 2^31 / (factor-1)).
        Opnd stepOp;
        bool haveStep = false;
        if (add.op == OP_ADD && !add.a[0].isConst && add.a[0].v == iv) { stepOp = add.a[1]; haveStep = true; }
        else if (add.op == OP_ADD && !add.a[1].isConst && add.a[1].v == iv) { stepOp = add.a[0]; haveStep = true; }
        if (!haveStep || (!stepOp.isConst && stepOp.v == iv)) continue;
        uint64_t K = 0;
        if (stepOp.isConst) {
            if (stepOp.c == 0 || stepOp.c > 65536) continue;
            K = static_cast<uint64_t>(factor - 1) * stepOp.c;
            if (K >= 0x7fffffffull) continue;
        }
        // i written exactly once in the loop; n not written in the loop.
        int ivWrites = 0;
        bool nWritten = false;
        int size = 0;
        for (int b : L.blocks) {
            size += static_cast<int>(f.bb[b].insts.size());
            for (const Inst &x : f.bb[b].insts) {
                if (x.dst == iv) ivWrites++;
                if (!n.isConst && x.dst == n.v) nWritten = true;
                if (!stepOp.isConst && x.dst == stepOp.v) nWritten = true;
            }
        }
        if (ivWrites != 1 || nWritten) continue;
        // No write of c between lt and br (it is the last write by construction).
        if (size * (factor + 1) > sizeBudget) continue;

        const int n0 = static_cast<int>(f.bb.size());
        std::vector<std::unordered_map<int, int>> clone(factor);
        for (int k = 0; k < factor; k++)
            for (int b : L.blocks) {
                clone[k][b] = static_cast<int>(f.bb.size());
                BB copy = f.bb[b];
                copy.label.clear();
                f.bb.push_back(copy);
            }
        // P (once, before the loop):  m = n - K ; f0 = m < n   (f0: no wrap)
        // D (per group):              q = i < m ; q = q & f0 ; br q, group, R
        // R (leaving the groups):     c = i < n ; br c, original loop, EXIT
        // i < m with no wrap means i + (factor-1)*s < n, so every test inside
        // the group would have been true.
        // Two guard blocks: D1 for entries from outside (the original loop runs
        // its body at least once, so its "no" side is the original header) and
        // D2 after a group (its "no" side re-tests i < n in R).
        const int m = freshReg(), f0 = freshReg(), q = freshReg();
        const int P = static_cast<int>(f.bb.size());
        const int D = P + 1, R = P + 2, D1 = P + 3;
        const int exitBlock = br.tgt[1];
        auto mk = [](Op op, int dst, Opnd a, Opnd b) {
            Inst x;
            x.op = op; x.dst = dst; x.n = 2; x.a[0] = a; x.a[1] = b;
            return x;
        };
        {
            BB pb, db, rb;
            Inst j;
            j.op = OP_JMP; j.tgt[0] = D;
            j.tgt[0] = D1;
            if (stepOp.isConst) {
                pb.insts = {mk(OP_SUB, m, n, Opnd::cst(static_cast<uint32_t>(K))), mk(OP_LT, f0, Opnd::val(m), n), j};
            } else {
                // k = s*(factor-1) is exact when 0 < s < lim; then m = n - k must not wrap.
                const int k = freshReg(), g1 = freshReg(), g2 = freshReg();
                const uint32_t lim = static_cast<uint32_t>(0x7fffffffu / static_cast<uint32_t>(factor - 1));
                pb.insts = {mk(OP_MUL, k, stepOp, Opnd::cst(static_cast<uint32_t>(factor - 1))),
                            mk(OP_SUB, m, n, Opnd::val(k)),
                            mk(OP_LT, f0, Opnd::val(m), n),
                            mk(OP_LT, g1, Opnd::cst(0), stepOp),
                            mk(OP_LT, g2, stepOp, Opnd::cst(lim)),
                            mk(OP_AND, g1, Opnd::val(g1), Opnd::val(g2)),
                            mk(OP_AND, f0, Opnd::val(f0), Opnd::val(g1)),
                            j};
            }
            Inst b1;
            b1.op = OP_BR; b1.n = 1; b1.a[0] = Opnd::val(q); b1.tgt[0] = clone[0][h]; b1.tgt[1] = R;
            db.insts = {mk(OP_LT, q, Opnd::val(iv), Opnd::val(m)), mk(OP_AND, q, Opnd::val(q), Opnd::val(f0)), b1};
            Inst b2;
            b2.op = OP_BR; b2.n = 1; b2.a[0] = Opnd::val(c); b2.tgt[0] = h; b2.tgt[1] = exitBlock;
            rb.insts = {mk(OP_LT, c, Opnd::val(iv), n), b2};
            BB d1 = db;
            d1.insts.back().tgt[1] = h;
            f.bb.push_back(pb);
            f.bb.push_back(db);
            f.bb.push_back(rb);
            f.bb.push_back(d1);
        }
        for (int k = 0; k < factor; k++) {
            for (int b : L.blocks) {
                Inst &tt = f.bb[clone[k][b]].term();
                int nt = (tt.op == OP_JMP) ? 1 : (tt.op == OP_BR ? 2 : 0);
                for (int s2 = 0; s2 < nt; s2++) {
                    int target = tt.tgt[s2];
                    if (target >= n0 || !in[target]) continue;
                    if (target != h) tt.tgt[s2] = clone[k][target];
                }
            }
            Inst &term = f.bb[clone[k][t]].term();   // br c, h, EXIT  ->  jump on
            term.op = OP_JMP; term.n = 0; term.tgt[0] = (k + 1 < factor) ? clone[k + 1][h] : D; term.tgt[1] = -1;
        }
        // The remainder (the original loop) runs fewer than `factor` times
        // whenever the groups ran, so unroll it into factor-1 copies in a chain:
        // each copy keeps its exit test, and the back edge is taken only when
        // the guard f0 was false.
        if (chainRemainder && factor > 2 && size * (2 * factor) <= sizeBudget) {
            const int rf = factor - 1;
            std::vector<std::unordered_map<int, int>> rc(rf);
            for (int b : L.blocks) rc[0][b] = b;
            for (int k = 1; k < rf; k++)
                for (int b : L.blocks) {
                    rc[k][b] = static_cast<int>(f.bb.size());
                    BB copy = f.bb[b];
                    copy.label.clear();
                    f.bb.push_back(copy);
                }
            for (int k = 0; k < rf; k++)
                for (int b : L.blocks) {
                    Inst &tt = f.bb[rc[k][b]].term();
                    int nt = (tt.op == OP_JMP) ? 1 : (tt.op == OP_BR ? 2 : 0);
                    for (int s2 = 0; s2 < nt; s2++) {
                        int target = tt.tgt[s2];
                        if (target >= n0 || !in[target]) continue;   // exit edge
                        if (target == h) tt.tgt[s2] = rc[(k + 1) % rf][h];
                        else tt.tgt[s2] = rc[k][target];
                    }
                }
        }
        // Entries from outside the loop go through P. The original loop stays as
        // the remainder (entered from R, or from D's false side through R).
        for (int b = 0; b < n0; b++) {
            if (in[b] || !f.bb[b].alive) continue;
            Inst &tt = f.bb[b].term();
            int nt = (tt.op == OP_JMP) ? 1 : (tt.op == OP_BR ? 2 : 0);
            for (int s2 = 0; s2 < nt; s2++) if (tt.tgt[s2] == h) tt.tgt[s2] = P;
        }
        changed = true;
    }
    if (changed) f.rebuildPreds();
    return changed;
}

}  // namespace kopt
