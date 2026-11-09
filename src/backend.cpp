// backend.cpp - SSA destruction, register allocation, layout, emission and
// list scheduling.
#include "backend.h"

#include <algorithm>
#include <cmath>
#include <set>
#include <unordered_map>
#include <unordered_set>

#include "cfg.h"
#include "passes.h"

namespace kopt {

namespace {

// ---------------------------------------------------------------------------
// SSA destruction: phis become parallel copies on incoming edges. A critical
// edge (from a block with two successors) gets its own block for the copies.
// ---------------------------------------------------------------------------

void emitParallelCopies(Func &f, std::vector<Inst> &out, std::vector<std::pair<Val, Opnd>> copies) {
    // Drop identity copies.
    copies.erase(std::remove_if(copies.begin(), copies.end(), [](const std::pair<Val, Opnd> &c) {
        return !c.second.isConst && c.second.v == c.first;
    }), copies.end());
    auto mov = [&](Val d, Opnd s) {
        Inst x;
        x.op = OP_MOV;
        x.dst = d;
        x.n = 1;
        x.a[0] = s;
        out.push_back(x);
    };
    while (!copies.empty()) {
        bool progress = false;
        for (size_t i = 0; i < copies.size();) {
            Val d = copies[i].first;
            bool isSource = false;
            for (size_t j = 0; j < copies.size(); j++)
                if (j != i && !copies[j].second.isConst && copies[j].second.v == d) { isSource = true; break; }
            if (!isSource) {
                mov(d, copies[i].second);
                copies.erase(copies.begin() + i);
                progress = true;
            } else {
                i++;
            }
        }
        if (!progress) {
            // Every remaining destination is still needed as a source: a cycle.
            Val d = copies[0].first;
            Val t = f.newVal();
            mov(t, Opnd::val(d));
            for (auto &c : copies)
                if (!c.second.isConst && c.second.v == d) c.second = Opnd::val(t);
        }
    }
}

void destructSSA(Func &f) {
    f.resolveAll();
    f.rebuildPreds();
    const int nb0 = static_cast<int>(f.bb.size());
    for (int b = 0; b < nb0; b++) {
        if (!f.bb[b].alive || f.bb[b].phis.empty()) continue;
        std::vector<int> preds = f.bb[b].preds;
        for (int p : preds) {
            std::vector<std::pair<Val, Opnd>> copies;
            for (Phi &ph : f.bb[b].phis)
                for (auto &in : ph.in)
                    if (in.first == p) copies.push_back({ph.dst, f.resolve(in.second)});
            int s[2];
            int ns = f.succs(p, s);
            std::vector<Inst> seq;
            emitParallelCopies(f, seq, copies);
            if (seq.empty()) continue;
            if (ns == 1) {
                BB &P = f.bb[p];
                P.insts.insert(P.insts.end() - 1, seq.begin(), seq.end());
            } else {
                int e = static_cast<int>(f.bb.size());
                f.bb.emplace_back();
                BB &E = f.bb[e];
                BB &P = f.bb[p];
                E.insts = seq;
                Inst j;
                j.op = OP_JMP;
                j.tgt[0] = b;
                E.insts.push_back(j);
                E.freq = std::min(P.freq, f.bb[b].freq);
                E.loopDepth = std::min(P.loopDepth, f.bb[b].loopDepth);
                Inst &t = P.term();
                for (int k = 0; k < 2; k++) if (t.tgt[k] == b) t.tgt[k] = e;
            }
        }
    }
    for (BB &B : f.bb) B.phis.clear();
    f.rebuildPreds();
}

// ---------------------------------------------------------------------------
// Liveness (path exploration from uses; works for the non-SSA form)
// ---------------------------------------------------------------------------

struct Liveness {
    std::vector<std::vector<int>> liveIn, liveOut;
};

Liveness computeLiveness(Func &f) {
    const int nb = static_cast<int>(f.bb.size());
    const int nv = f.nvals;
    Liveness L;
    L.liveIn.assign(nb, {});
    L.liveOut.assign(nb, {});
    std::vector<std::vector<int>> ueBlocks(nv), defBlocks(nv);
    std::vector<int> defStamp(nv, -1), ueStamp(nv, -1);
    for (int b = 0; b < nb; b++) {
        BB &B = f.bb[b];
        if (!B.alive) continue;
        for (Inst &x : B.insts) {
            for (int a = 0; a < x.n; a++) {
                if (x.a[a].isConst) continue;
                int v = x.a[a].v;
                if (defStamp[v] != b && ueStamp[v] != b) { ueStamp[v] = b; ueBlocks[v].push_back(b); }
            }
            if (x.dst >= 0 && defStamp[x.dst] != b) { defStamp[x.dst] = b; defBlocks[x.dst].push_back(b); }
        }
    }
    std::vector<int> defMark(nb, -1), inMark(nb, -1), outMark(nb, -1);
    std::vector<int> work;
    for (int v = 0; v < nv; v++) {
        if (ueBlocks[v].empty()) continue;
        for (int b : defBlocks[v]) defMark[b] = v;
        work.clear();
        for (int b : ueBlocks[v]) { inMark[b] = v; L.liveIn[b].push_back(v); work.push_back(b); }
        while (!work.empty()) {
            int x = work.back();
            work.pop_back();
            for (int p : f.bb[x].preds) {
                if (outMark[p] != v) { outMark[p] = v; L.liveOut[p].push_back(v); }
                if (defMark[p] != v && inMark[p] != v) {
                    inMark[p] = v;
                    L.liveIn[p].push_back(v);
                    work.push_back(p);
                }
            }
        }
    }
    return L;
}

// ---------------------------------------------------------------------------
// Register allocation: interference graph + coalescing + coloring.
// The Kiln has no fixed register file to spill from: any number of names is
// legal, but once a program uses more than K names every touch of an evicted
// (least recently used) name costs reg_spill_penalty. So the allocator's job is
// to use as few names as possible, and above all to keep each hot loop's
// working set within K names.
// ---------------------------------------------------------------------------

struct Graph {
    std::vector<std::vector<int>> adj;
    void add(int a, int b) {
        if (a == b) return;
        adj[a].push_back(b);
        adj[b].push_back(a);
    }
    void finish() {
        for (auto &v : adj) {
            std::sort(v.begin(), v.end());
            v.erase(std::unique(v.begin(), v.end()), v.end());
        }
    }
};

struct Allocation {
    std::vector<int> color;   // per value; -1 if unused
    int ncolors = 0;
};

Allocation allocate(Func &f, const Machine &m, bool coalesce) {
    const int nv = f.nvals;
    Liveness L = computeLiveness(f);
    Graph g;
    g.adj.assign(nv, {});
    std::vector<char> used(nv, 0);
    for (Val p : f.params) used[p] = 1;
    for (size_t i = 0; i < f.params.size(); i++)
        for (size_t j = i + 1; j < f.params.size(); j++) g.add(f.params[i], f.params[j]);
    struct Move { int a, b; double w; };
    std::vector<Move> moves;
    std::vector<char> isLive(nv, 0);
    std::vector<int> liveList;
    for (int b = 0; b < static_cast<int>(f.bb.size()); b++) {
        BB &B = f.bb[b];
        if (!B.alive) continue;
        liveList.clear();
        for (int v : L.liveOut[b]) { isLive[v] = 1; liveList.push_back(v); }
        int liveCount = static_cast<int>(liveList.size());
        for (int i = static_cast<int>(B.insts.size()) - 1; i >= 0; i--) {
            Inst &x = B.insts[i];
            for (int a = 0; a < x.n; a++) if (!x.a[a].isConst) used[x.a[a].v] = 1;
            if (x.dst >= 0) {
                int d = x.dst;
                used[d] = 1;
                int movSrc = (x.op == OP_MOV && !x.a[0].isConst) ? x.a[0].v : -1;
                for (int l : liveList)
                    if (isLive[l] && l != d && l != movSrc) g.add(d, l);
                if (movSrc >= 0) moves.push_back({d, movSrc, B.freq});
                if (isLive[d]) { isLive[d] = 0; liveCount--; }
            }
            for (int a = 0; a < x.n; a++) {
                if (x.a[a].isConst) continue;
                int u = x.a[a].v;
                if (!isLive[u]) { isLive[u] = 1; liveList.push_back(u); liveCount++; }
            }
            if (static_cast<int>(liveList.size()) > 2 * liveCount + 16) {
                std::vector<int> c;
                for (int l : liveList) if (isLive[l]) c.push_back(l);
                liveList.swap(c);
            }
        }
        for (int l : liveList) isLive[l] = 0;
    }
    g.finish();

    // Union-find coalescing of copy-related values that never interfere.
    std::vector<int> parent(nv);
    for (int i = 0; i < nv; i++) parent[i] = i;
    auto find = [&](int x) {
        while (parent[x] != x) { parent[x] = parent[parent[x]]; x = parent[x]; }
        return x;
    };
    std::vector<std::unordered_set<int>> nbr(nv);
    for (int v = 0; v < nv; v++)
        if (used[v]) nbr[v].insert(g.adj[v].begin(), g.adj[v].end());
    if (coalesce) {
        std::stable_sort(moves.begin(), moves.end(), [](const Move &a, const Move &b) { return a.w > b.w; });
        for (const Move &mv : moves) {
            int a = find(mv.a), b = find(mv.b);
            // Parameters interfere pairwise, so two of them are never merged.
            if (a == b || nbr[a].count(b)) continue;
            if (nbr[a].size() < nbr[b].size()) std::swap(a, b);
            parent[b] = a;
            for (int n : nbr[b]) {
                nbr[n].erase(b);
                nbr[n].insert(a);
                nbr[a].insert(n);
            }
            nbr[b].clear();
        }
    }
    // Smallest-last ordering, then greedy coloring.
    std::vector<int> nodes;
    for (int v = 0; v < nv; v++) if (used[v] && find(v) == v) nodes.push_back(v);
    std::vector<int> deg(nv, 0);
    int maxDeg = 0;
    for (int v : nodes) { deg[v] = static_cast<int>(nbr[v].size()); maxDeg = std::max(maxDeg, deg[v]); }
    std::vector<std::vector<int>> bucket(maxDeg + 1);
    std::vector<int> pos(nv, -1);
    for (int v : nodes) bucket[deg[v]].push_back(v);
    std::vector<char> removed(nv, 0);
    std::vector<int> order;
    order.reserve(nodes.size());
    int cur = 0;
    for (size_t step = 0; step < nodes.size(); step++) {
        cur = std::max(0, cur - 1);
        int v = -1;
        while (v < 0) {
            while (cur <= maxDeg && bucket[cur].empty()) cur++;
            if (cur > maxDeg) break;
            int cand = bucket[cur].back();
            bucket[cur].pop_back();
            if (!removed[cand] && deg[cand] == cur) v = cand;
        }
        if (v < 0) break;
        removed[v] = 1;
        order.push_back(v);
        for (int n : nbr[v]) {
            if (removed[n]) continue;
            deg[n]--;
            bucket[deg[n]].push_back(n);
        }
    }
    Allocation A;
    A.color.assign(nv, -1);
    std::vector<int> repColor(nv, -1);
    std::vector<int> mark;
    for (int i = static_cast<int>(order.size()) - 1; i >= 0; i--) {
        int v = order[i];
        mark.assign(nbr[v].size() + 2, 0);
        for (int n : nbr[v]) {
            int c = repColor[n];
            if (c >= 0 && c < static_cast<int>(mark.size())) mark[c] = 1;
        }
        int c = 0;
        while (mark[c]) c++;
        repColor[v] = c;
        A.ncolors = std::max(A.ncolors, c + 1);
    }
    for (int v = 0; v < nv; v++) if (used[v]) A.color[v] = repColor[find(v)];
    (void)m;
    return A;
}

// ---------------------------------------------------------------------------
// K-register allocation with spilling (Chaitin-Briggs with conservative
// coalescing). Used when the scratch region is free: a value that does not fit
// lives in a scratch word, loaded before each use and stored after each
// definition. With at most K names the machine never spills by itself.
// ---------------------------------------------------------------------------

bool allocateK(Func &f, int K, Allocation &A) {
    std::vector<int> slotOf;          // per value: scratch slot index or -1
    std::vector<char> noSpill;        // short temps created by spilling
    int nextSlot = 0;
    const int maxSlots = 1024;
    for (Val p : f.params) (void)p;
    for (int iter = 0; iter < 40; iter++) {
        const int nv = f.nvals;
        slotOf.resize(nv, -1);
        noSpill.resize(nv, 0);
        Liveness L = computeLiveness(f);
        Graph g;
        g.adj.assign(nv, {});
        std::vector<char> used(nv, 0);
        std::vector<double> cost(nv, 0.0);
        for (Val p : f.params) used[p] = 1;
        for (size_t i = 0; i < f.params.size(); i++)
            for (size_t j = i + 1; j < f.params.size(); j++) g.add(f.params[i], f.params[j]);
        struct Move { int a, b; double w; };
        std::vector<Move> moves;
        std::vector<char> isLive(nv, 0);
        std::vector<int> liveList;
        for (int b = 0; b < static_cast<int>(f.bb.size()); b++) {
            BB &B = f.bb[b];
            if (!B.alive) continue;
            liveList.clear();
            for (int v : L.liveOut[b]) { isLive[v] = 1; liveList.push_back(v); }
            for (int i = static_cast<int>(B.insts.size()) - 1; i >= 0; i--) {
                Inst &x = B.insts[i];
                if (x.dst >= 0) {
                    int d = x.dst;
                    used[d] = 1;
                    cost[d] += B.freq;
                    int movSrc = (x.op == OP_MOV && !x.a[0].isConst) ? x.a[0].v : -1;
                    for (int l : liveList)
                        if (isLive[l] && l != d && l != movSrc) g.add(d, l);
                    if (movSrc >= 0) moves.push_back({d, movSrc, B.freq});
                    isLive[d] = 0;
                }
                for (int a = 0; a < x.n; a++) {
                    if (x.a[a].isConst) continue;
                    int u = x.a[a].v;
                    used[u] = 1;
                    cost[u] += B.freq;
                    if (!isLive[u]) { isLive[u] = 1; liveList.push_back(u); }
                }
            }
            for (int l : liveList) isLive[l] = 0;
        }
        g.finish();
        // Conservative (Briggs) coalescing: merge only if the merged node has
        // fewer than K neighbours of significant degree.
        std::vector<int> parent(nv);
        for (int i = 0; i < nv; i++) parent[i] = i;
        auto find = [&](int x) {
            while (parent[x] != x) { parent[x] = parent[parent[x]]; x = parent[x]; }
            return x;
        };
        std::vector<std::unordered_set<int>> nbr(nv);
        for (int v = 0; v < nv; v++) if (used[v]) nbr[v].insert(g.adj[v].begin(), g.adj[v].end());
        std::stable_sort(moves.begin(), moves.end(), [](const Move &a, const Move &b) { return a.w > b.w; });
        for (const Move &mv : moves) {
            int a = find(mv.a), b = find(mv.b);
            if (a == b || nbr[a].count(b)) continue;
            std::unordered_set<int> merged = nbr[a];
            merged.insert(nbr[b].begin(), nbr[b].end());
            int significant = 0;
            for (int n : merged) if (static_cast<int>(nbr[n].size()) >= K) significant++;
            if (significant >= K) continue;
            if (nbr[a].size() < nbr[b].size()) std::swap(a, b);
            parent[b] = a;
            cost[a] += cost[b];
            noSpill[a] = noSpill[a] && noSpill[b];
            for (int n : nbr[b]) { nbr[n].erase(b); nbr[n].insert(a); nbr[a].insert(n); }
            nbr[b].clear();
        }
        // Simplify / select with optimistic coloring.
        std::vector<int> nodes;
        for (int v = 0; v < nv; v++) if (used[v] && find(v) == v) nodes.push_back(v);
        std::vector<int> deg(nv, 0);
        for (int v : nodes) deg[v] = static_cast<int>(nbr[v].size());
        std::vector<char> removed(nv, 0);
        std::vector<int> stack;
        size_t left = nodes.size();
        while (left > 0) {
            int pick = -1;
            for (int v : nodes) if (!removed[v] && deg[v] < K) { pick = v; break; }
            if (pick < 0) {
                double best = 1e300;
                for (int v : nodes) {
                    if (removed[v]) continue;
                    double c = noSpill[v] ? 1e200 : cost[v] / (deg[v] + 1);
                    if (c < best) { best = c; pick = v; }
                }
            }
            removed[pick] = 1;
            stack.push_back(pick);
            left--;
            for (int n : nbr[pick]) if (!removed[n]) deg[n]--;
        }
        std::vector<int> repColor(nv, -1);
        std::vector<int> spilled;
        for (int i = static_cast<int>(stack.size()) - 1; i >= 0; i--) {
            int v = stack[i];
            std::vector<char> taken(K, 0);
            for (int n : nbr[v]) if (repColor[n] >= 0) taken[repColor[n]] = 1;
            int c = 0;
            while (c < K && taken[c]) c++;
            if (c < K) repColor[v] = c;
            else spilled.push_back(v);
        }
        if (spilled.empty()) {
            A.color.assign(nv, -1);
            A.ncolors = 0;
            for (int v = 0; v < nv; v++)
                if (used[v]) { A.color[v] = repColor[find(v)]; A.ncolors = std::max(A.ncolors, A.color[v] + 1); }
            return true;
        }
        // Spill every member of each spilled class to one slot.
        std::vector<int> classSlot(nv, -1);
        for (int r : spilled) {
            if (noSpill[r]) return false;           // cannot make progress
            if (nextSlot >= maxSlots) return false;
            classSlot[r] = nextSlot++;
        }
        for (int v = 0; v < nv; v++)
            if (used[v] && classSlot[find(v)] >= 0) slotOf[v] = classSlot[find(v)];
        auto slotAddr = [&](int s) { return Opnd::cst(static_cast<uint32_t>(4095 - s)); };
        for (int b = 0; b < static_cast<int>(f.bb.size()); b++) {
            BB &B = f.bb[b];
            if (!B.alive) continue;
            std::vector<Inst> out;
            out.reserve(B.insts.size() * 2);
            if (b == 0)
                for (Val p : f.params)
                    if (slotOf[p] >= 0) {
                        Inst st;
                        st.op = OP_STORE; st.n = 2; st.a[0] = slotAddr(slotOf[p]); st.a[1] = Opnd::val(p);
                        out.push_back(st);
                    }
            for (Inst x : B.insts) {
                std::vector<std::pair<int, int>> loaded;
                for (int a = 0; a < x.n; a++) {
                    if (x.a[a].isConst || slotOf[x.a[a].v] < 0) continue;
                    int v = x.a[a].v, t = -1;
                    for (auto &l : loaded) if (l.first == v) t = l.second;
                    if (t < 0) {
                        t = f.newVal();
                        Inst ld;
                        ld.op = OP_LOAD; ld.dst = t; ld.n = 1; ld.a[0] = slotAddr(slotOf[v]);
                        out.push_back(ld);
                        loaded.push_back({v, t});
                    }
                    x.a[a] = Opnd::val(t);
                }
                if (x.dst >= 0 && slotOf[x.dst] >= 0) {
                    int d = x.dst;
                    if (x.op == OP_MOV) {
                        // mov d, s  ->  store slot(d), s
                        Inst st;
                        st.op = OP_STORE; st.n = 2; st.a[0] = slotAddr(slotOf[d]); st.a[1] = x.a[0];
                        out.push_back(st);
                        continue;
                    }
                    int t = f.newVal();
                    x.dst = t;
                    out.push_back(x);
                    Inst st;
                    st.op = OP_STORE; st.n = 2; st.a[0] = slotAddr(slotOf[d]); st.a[1] = Opnd::val(t);
                    out.push_back(st);
                    continue;
                }
                out.push_back(x);
            }
            B.insts.swap(out);
        }
        for (Val p : f.params) if (slotOf[p] >= 0) { slotOf[p] = -1; }
        slotOf.resize(f.nvals, -1);
        noSpill.resize(f.nvals, 1);   // all temps created above are short
        for (Val p : f.params) noSpill[p] = 1;
        // Values now living in memory never appear again.
    }
    return false;
}

// ---------------------------------------------------------------------------
// Block frequency estimate (loop nesting) and layout.
// ---------------------------------------------------------------------------

void estimateFrequencies(Func &f) {
    f.rebuildPreds();
    DomInfo d = computeDominators(f);
    LoopInfo li = computeLoops(f, d);
    for (int b = 0; b < static_cast<int>(f.bb.size()); b++) {
        f.bb[b].loopDepth = li.depth[b];
        f.bb[b].freq = std::pow(8.0, std::min(li.depth[b], 6));
    }
}

std::vector<int> layoutBlocks(Func &f) {
    DomInfo d = computeDominators(f);
    LoopInfo li = computeLoops(f, d);
    const int nb = static_cast<int>(f.bb.size());
    std::vector<char> placed(nb, 0);
    std::vector<int> order;
    auto pickNext = [&](int b) -> int {
        int s[2];
        int ns = f.succs(b, s);
        int best = -1;
        double bestScore = -1;
        for (int i = 0; i < ns; i++) {
            int t = s[i];
            if (placed[t] || !f.bb[t].alive) continue;
            double score = f.bb[t].freq;
            // Prefer staying inside the current loop; leaving it is the rare edge.
            if (li.innermost[b] >= 0 && !li.inLoop(t, li.innermost[b])) score *= 0.01;
            if (score > bestScore) { bestScore = score; best = t; }
        }
        return best;
    };
    int b = 0;
    while (true) {
        placed[b] = 1;
        order.push_back(b);
        int n = pickNext(b);
        if (n < 0) {
            for (int c : d.rpo) if (!placed[c]) { n = c; break; }
        }
        if (n < 0) break;
        b = n;
    }
    return order;
}

}  // namespace

// ---------------------------------------------------------------------------
// Lowering
// ---------------------------------------------------------------------------

bool canSpillToScratch(Func &f) { return memoryAccessesBelow(f, kScratchBase); }

Program lowerToProgram(Func &f, const Machine &m, const BackendOptions &opt) {
    const bool scratchFree = opt.spillToK && canSpillToScratch(f);
    estimateFrequencies(f);
    destructSSA(f);
    Allocation A;
    bool haveK = false;
    if (scratchFree) {
        Func backup = f;
        haveK = allocateK(f, m.registers, A);
        if (!haveK) f = backup;
    }
    if (!haveK) A = allocate(f, m, opt.coalesce);
    // Rewrite values to their colors (kept as values for the CFG passes below),
    // and drop copies that became "mov r, r".
    for (BB &B : f.bb) {
        if (!B.alive) continue;
        std::vector<Inst> out;
        out.reserve(B.insts.size());
        for (Inst &x : B.insts) {
            if (x.op == OP_MOV && !x.a[0].isConst && A.color[x.a[0].v] == A.color[x.dst]) continue;
            out.push_back(x);
        }
        B.insts.swap(out);
    }
    // Jump threading / block merging on the copy-free CFG.
    simplifyCFG(f);
    std::vector<int> order = layoutBlocks(f);

    Program p;
    p.name = f.name;
    for (Val v : f.params) p.params.push_back(static_cast<uint32_t>(A.color[v] < 0 ? 0 : A.color[v]));
    std::vector<int> outIndex(f.bb.size(), -1);
    for (size_t i = 0; i < order.size(); i++) outIndex[order[i]] = static_cast<int>(i);
    std::set<std::string> usedLabels;
    for (size_t i = 0; i < order.size(); i++) {
        Block blk;
        std::string lab = f.bb[order[i]].label;
        bool ok = !lab.empty() && !usedLabels.count(lab) && !(lab[0] == 'v' && lab.size() > 1 && isdigit(static_cast<unsigned char>(lab[1])));
        if (!ok) {
            int k = static_cast<int>(i);
            do { lab = "L" + std::to_string(k++); } while (usedLabels.count(lab));
        }
        usedLabels.insert(lab);
        blk.label = lab;
        p.blocks.push_back(blk);
    }
    auto reg = [&](Val v) { return static_cast<uint32_t>(A.color[v] < 0 ? 0 : A.color[v]); };
    for (size_t i = 0; i < order.size(); i++) {
        BB &B = f.bb[order[i]];
        Block &out = p.blocks[i];
        for (Inst &x : B.insts) {
            Instr y;
            y.op = x.op;
            y.k = x.k;
            y.nsrc = x.n;
            if (x.dst >= 0) y.dst = reg(x.dst);
            for (int a = 0; a < x.n; a++)
                y.src[a] = x.a[a].isConst ? Operand::imm(x.a[a].c) : Operand::reg(reg(x.a[a].v));
            if (x.op == OP_JMP) y.target[0] = outIndex[x.tgt[0]];
            if (x.op == OP_BR) { y.target[0] = outIndex[x.tgt[0]]; y.target[1] = outIndex[x.tgt[1]]; }
            out.ins.push_back(y);
        }
    }
    if (opt.schedule) scheduleProgram(p, m);
    return p;
}

// ---------------------------------------------------------------------------
// List scheduling (per block) against the exact issue model.
// ---------------------------------------------------------------------------

void scheduleProgram(Program &p, const Machine &m) {
    for (Block &blk : p.blocks) {
        const int n = static_cast<int>(blk.ins.size());
        if (n <= 2) continue;
        const int body = n - 1;   // the terminator stays last
        std::vector<std::vector<int>> succ(body);
        std::vector<std::vector<std::pair<int, int>>> predLat(body);   // (pred, latency)
        std::vector<int> npred(body, 0);
        auto addDep = [&](int i, int j, int lat) {
            succ[i].push_back(j);
            predLat[j].push_back({i, lat});
            npred[j]++;
        };
        // Ordering rules (KIR_SPEC.md section 7):
        //  * effects (observable store, vload, vstore, trap) keep their order;
        //  * an instruction that may trap (div/mod by a non-constant, load or
        //    store at a non-constant address) never crosses an effect;
        //  * may-trap divisions and may-trap memory ops (different trap kinds)
        //    keep their relative order; two of the same kind may swap;
        //  * memory reads and writes that may touch the same word keep their
        //    order (two different constant addresses never alias).
        // A store to a constant scratch address (>= 3072) is not observable and
        // cannot trap, so it is ordered only by the memory rule.
        std::unordered_map<uint32_t, int> lastWriter;
        std::unordered_map<uint32_t, std::vector<int>> readersSinceWrite;
        int lastEffect = -1;
        std::vector<int> trapLoadsSinceEffect, trapDivsSinceEffect;
        std::vector<int> memOps;   // earlier loads and stores, for the alias rule
        auto mayAlias = [&](const Instr &a, const Instr &b) {
            const Operand &x = a.src[0], &y = b.src[0];
            if (!x.isReg && !y.isReg) return x.v == y.v;
            return true;
        };
        for (int j = 0; j < body; j++) {
            const Instr &x = blk.ins[j];
            for (int a = 0; a < x.nsrc; a++) {
                if (!x.src[a].isReg) continue;
                uint32_t r = x.src[a].v;
                auto it = lastWriter.find(r);
                if (it != lastWriter.end()) addDep(it->second, j, m.latency(blk.ins[it->second].op));
                readersSinceWrite[r].push_back(j);
            }
            if (hasDest(x.op)) {
                uint32_t r = x.dst;
                auto it = lastWriter.find(r);
                if (it != lastWriter.end()) addDep(it->second, j, 0);
                for (int rd : readersSinceWrite[r]) if (rd != j) addDep(rd, j, 0);
                readersSinceWrite[r].clear();
                lastWriter[r] = j;
            }
            const bool isMem = x.op == OP_LOAD || x.op == OP_STORE;
            const bool constAddr = isMem && !x.src[0].isReg && x.src[0].v < kMemWords;
            const bool memTrap = isMem && !constAddr;
            const bool scratchStore = x.op == OP_STORE && constAddr && x.src[0].v >= kScratchBase;
            const bool isEffect = (x.op == OP_STORE && !scratchStore) || x.op == OP_VLOAD ||
                                  x.op == OP_VSTORE || x.op == OP_TRAP;
            const bool isDivTrap = (x.op == OP_DIV || x.op == OP_MOD) && !(x.src[1].isReg == false && x.src[1].v != 0);
            if (isMem) {
                // Memory dependences: any earlier access to a word this one may touch,
                // where at least one of the two writes.
                for (int k : memOps) {
                    const Instr &y = blk.ins[k];
                    if ((y.op == OP_STORE || x.op == OP_STORE) && mayAlias(x, y)) addDep(k, j, 0);
                }
                memOps.push_back(j);
            }
            if (isEffect || (memTrap && x.op == OP_STORE)) {
                if (lastEffect >= 0) addDep(lastEffect, j, 0);
                for (int d : trapDivsSinceEffect) addDep(d, j, 0);
                for (int l : trapLoadsSinceEffect) addDep(l, j, 0);
                trapLoadsSinceEffect.clear();
                trapDivsSinceEffect.clear();
                lastEffect = j;
            } else if (isDivTrap) {
                if (lastEffect >= 0) addDep(lastEffect, j, 0);
                for (int l : trapLoadsSinceEffect) addDep(l, j, 0);
                trapDivsSinceEffect.push_back(j);
            } else if (memTrap) {   // a load that may trap
                if (lastEffect >= 0) addDep(lastEffect, j, 0);
                for (int d : trapDivsSinceEffect) addDep(d, j, 0);
                trapLoadsSinceEffect.push_back(j);
            }
        }
        // Critical-path heights.
        std::vector<int> height(body, 0);
        for (int i = body - 1; i >= 0; i--) {
            int h = 0;
            for (int s : succ[i]) h = std::max(h, height[s]);
            height[i] = h + (hasDest(blk.ins[i].op) ? m.latency(blk.ins[i].op) : 1);
        }
        std::unordered_map<uint32_t, long> ready;   // register -> cycle its value is ready
        std::vector<long> doneAt(body, 0);          // issue cycle of scheduled instructions
        std::vector<char> scheduled(body, 0);
        std::vector<int> avail;
        for (int i = 0; i < body; i++) if (npred[i] == 0) avail.push_back(i);
        long last = 0;
        int used = 0, memused = 0;
        std::vector<Instr> out;
        out.reserve(n);
        std::vector<int> remaining = npred;
        while (!avail.empty()) {
            int best = -1;
            long bestT = 0;
            for (int j : avail) {
                const Instr &x = blk.ins[j];
                long t = last;
                for (auto &pl : predLat[j]) t = std::max(t, doneAt[pl.first] + pl.second);
                for (int a = 0; a < x.nsrc; a++)
                    if (x.src[a].isReg) {
                        auto it = ready.find(x.src[a].v);
                        if (it != ready.end()) t = std::max(t, it->second);
                    }
                if (hasDest(x.op)) {
                    auto it = ready.find(x.dst);
                    if (it != ready.end()) t = std::max(t, it->second);
                }
                bool mem = isMemOp(x.op);
                if (t == last && (used >= m.issue_width || (mem && memused >= m.mem_ports))) t++;
                if (best < 0 || t < bestT || (t == bestT && (height[j] > height[best] || (height[j] == height[best] && j < best)))) {
                    best = j;
                    bestT = t;
                }
            }
            const Instr &x = blk.ins[best];
            if (bestT > last) { used = 0; memused = 0; }
            used++;
            if (isMemOp(x.op)) memused++;
            last = bestT;
            doneAt[best] = bestT;
            if (hasDest(x.op)) ready[x.dst] = bestT + m.latency(x.op);
            scheduled[best] = 1;
            out.push_back(x);
            avail.erase(std::find(avail.begin(), avail.end(), best));
            for (int s : succ[best])
                if (--remaining[s] == 0) avail.push_back(s);
        }
        if (static_cast<int>(out.size()) != body) continue;   // should not happen; keep original order
        out.push_back(blk.ins[body]);
        blk.ins.swap(out);
    }
}

}  // namespace kopt
