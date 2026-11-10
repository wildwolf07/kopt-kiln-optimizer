// backend.cpp - SSA destruction, register allocation, layout, emission and
// list scheduling.
#include "backend.h"

#include <algorithm>
#include <iterator>
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
    size_t edges = 0;
    bool exhausted = false;
    void add(int a, int b) {
        if (a == b) return;
        // Dense live sets can have quadratic interference. Bound construction
        // before it threatens the judge's memory/time limit; unique names are
        // always semantically valid in KIR and need no interference graph.
        if (edges >= 8000000) { exhausted = true; return; }
        edges++;
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

Allocation allocate(Func &f, const Machine &m, bool coalesce, bool spreadColors) {
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
                if (g.exhausted) {
                    Allocation unique;
                    unique.ncolors = nv;
                    unique.color.resize(nv);
                    for (int v = 0; v < nv; v++) unique.color[v] = v;
                    return unique;
                }
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
    // Neighbour lists as vectors (hash sets cost several times the memory on
    // dense 100k-instruction functions). During coalescing a list may name
    // values that have since been merged into another class, so every lookup
    // goes through find(); nothing rewrites the neighbours' lists (rewriting
    // them was quadratic around values with very many neighbours).
    std::vector<std::vector<int>> nbr = std::move(g.adj);
    // Small-program tie order is part of the candidate search trajectory.
    // Preserve it; use lazy class edges only for large value universes.
    const bool lazyCoalesce = nv > 4096;
    auto replaceIn = [&](int n, int from, int to) {
        std::vector<int> &l = nbr[n];
        auto it = std::lower_bound(l.begin(), l.end(), from);
        if (it != l.end() && *it == from) l.erase(it);
        auto jt = std::lower_bound(l.begin(), l.end(), to);
        if (jt == l.end() || *jt != to) l.insert(jt, to);
    };
    auto interfere = [&](int a, int b) {   // class a and class b share an edge
        const std::vector<int> &l = nbr[a].size() <= nbr[b].size() ? nbr[a] : nbr[b];
        const int other = nbr[a].size() <= nbr[b].size() ? b : a;
        for (int x : l) if (find(x) == other) return true;
        return false;
    };
    if (coalesce) {
        std::stable_sort(moves.begin(), moves.end(), [](const Move &a, const Move &b) { return a.w > b.w; });
        for (const Move &mv : moves) {
            int a = find(mv.a), b = find(mv.b);
            // Parameters interfere pairwise, so two of them are never merged.
            if (a == b || (lazyCoalesce ? interfere(a, b) : std::binary_search(nbr[a].begin(), nbr[a].end(), b))) continue;
            if (nbr[a].size() < nbr[b].size()) std::swap(a, b);
            parent[b] = a;
            if (!lazyCoalesce) {
                std::vector<int> merged;
                merged.reserve(nbr[a].size() + nbr[b].size());
                std::set_union(nbr[a].begin(), nbr[a].end(), nbr[b].begin(), nbr[b].end(), std::back_inserter(merged));
                for (int n : nbr[b]) replaceIn(n, b, a);
                nbr[a].swap(merged);
                std::vector<int>().swap(nbr[b]);
                continue;
            }
            nbr[a].insert(nbr[a].end(), nbr[b].begin(), nbr[b].end());
            std::vector<int>().swap(nbr[b]);
        }
        // Class-level lists: representatives only, sorted, without duplicates.
        if (lazyCoalesce) for (int v = 0; v < nv; v++) {
            if (!used[v] || find(v) != v) { std::vector<int>().swap(nbr[v]); continue; }
            bool increasing = true;   // most lists are untouched by merging
            int prev = -1;
            for (int &x : nbr[v]) { x = find(x); if (x <= prev) increasing = false; prev = x; }
            if (increasing) continue;
            std::sort(nbr[v].begin(), nbr[v].end());
            nbr[v].erase(std::unique(nbr[v].begin(), nbr[v].end()), nbr[v].end());
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
    int colorCursor = 0;
    const int spreadLimit = std::min(32, m.registers);
    for (int i = static_cast<int>(order.size()) - 1; i >= 0; i--) {
        int v = order[i];
        mark.assign(std::max(nbr[v].size() + 2, static_cast<size_t>(spreadColors ? spreadLimit : 0)), 0);
        for (int n : nbr[v]) {
            int c = repColor[n];
            if (c >= 0 && c < static_cast<int>(mark.size())) mark[c] = 1;
        }
        int c = 0;
        while (mark[c]) c++;
        if (spreadColors && c < spreadLimit) {
            for (int j = 0; j < spreadLimit; j++) {
                int candidate = (colorCursor + j) % spreadLimit;
                if (!mark[candidate]) { c = candidate; colorCursor = (c + 1) % spreadLimit; break; }
            }
        }
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

bool allocateK(Func &f, int K, Allocation &A, int reuse, bool spreadColors) {
    std::vector<int> slotOf;          // per value: scratch slot index or -1
    std::vector<char> noSpill;        // short temps created by spilling
    std::vector<int> web;             // spill web: copy-related values that may share a slot
    int nextSlot = 0;
    const int maxSlots = 1024;
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
            int liveCount = static_cast<int>(liveList.size());
            for (int i = static_cast<int>(B.insts.size()) - 1; i >= 0; i--) {
                Inst &x = B.insts[i];
                if (x.dst >= 0) {
                    int d = x.dst;
                    used[d] = 1;
                    cost[d] += B.freq;
                    int movSrc = (x.op == OP_MOV && !x.a[0].isConst) ? x.a[0].v : -1;
                    // Drop dead entries once they outnumber the live ones (the
                    // same edges are added; long blocks stay near-linear).
                    if (liveList.size() > 64 && liveList.size() > 2 * static_cast<size_t>(liveCount)) {
                        size_t w = 0;
                        for (int l : liveList) if (isLive[l]) liveList[w++] = l;
                        liveList.resize(w);
                    }
                    for (int l : liveList)
                        if (isLive[l] && l != d && l != movSrc) g.add(d, l);
                    if (g.exhausted) return false;
                    if (movSrc >= 0) moves.push_back({d, movSrc, B.freq});
                    if (isLive[d]) liveCount--;
                    isLive[d] = 0;
                }
                for (int a = 0; a < x.n; a++) {
                    if (x.a[a].isConst) continue;
                    int u = x.a[a].v;
                    used[u] = 1;
                    cost[u] += B.freq;
                    if (!isLive[u]) { isLive[u] = 1; liveList.push_back(u); liveCount++; }
                }
            }
            for (int l : liveList) isLive[l] = 0;
        }
        g.finish();
        // Reject before building the more expensive web/hash representations.
        if (g.edges > 1500000) return false;
        if (iter == 0) {
            // Spill webs: copy-related values that never interfere may live in one
            // scratch word, so a copy between two spilled values disappears.
            web.assign(nv, 0);
            for (int i = 0; i < nv; i++) web[i] = i;
            auto wfind = [&](int x) {
                while (web[x] != x) { web[x] = web[web[x]]; x = web[x]; }
                return x;
            };
            std::vector<std::vector<int>> members(nv);
            for (int i = 0; i < nv; i++) members[i].push_back(i);
            std::vector<std::unordered_set<int>> wn(nv);
            for (int v = 0; v < nv; v++) if (used[v]) wn[v].insert(g.adj[v].begin(), g.adj[v].end());
            std::vector<Move> ms = moves;
            std::stable_sort(ms.begin(), ms.end(), [](const Move &a, const Move &b) { return a.w > b.w; });
            for (const Move &mv : ms) {
                int a = wfind(mv.a), b = wfind(mv.b);
                if (a == b || wn[a].count(b)) continue;
                bool clash = false;   // any member of b interferes with a member of a
                for (int x : members[b]) { if (wn[a].count(x)) { clash = true; break; } }
                if (clash) continue;
                web[b] = a;
                for (int x : members[b]) members[a].push_back(x);
                members[b].clear();
                for (int n : wn[b]) wn[a].insert(n);
            }
            for (int i = 0; i < nv; i++) web[i] = wfind(i);
            // Values whose whole life is a few instructions inside one block gain
            // nothing from spilling (the reload would be just as long).
            std::vector<int> liveOutStamp(nv, -1);
            for (BB &B : f.bb) {
                if (!B.alive) continue;
                std::unordered_map<int, int> defAt;
                std::unordered_map<int, int> lastUse;
                const int block = static_cast<int>(&B - &f.bb[0]);
                for (int u : L.liveOut[block]) liveOutStamp[u] = block;
                for (int i = 0; i < static_cast<int>(B.insts.size()); i++) {
                    if (B.insts[i].dst >= 0) defAt[B.insts[i].dst] = i;
                    for (int a = 0; a < B.insts[i].n; a++)
                        if (!B.insts[i].a[a].isConst) lastUse[B.insts[i].a[a].v] = i;
                }
                for (auto &kv : defAt) {
                    int v = kv.first;
                    if (liveOutStamp[v] == block) continue;
                    int last = kv.second;
                    const auto use = lastUse.find(v);
                    if (use != lastUse.end()) last = std::max(last, use->second);
                    if (last - kv.second <= 2 && wfind(v) == v && members[v].size() <= 1) noSpill[v] = 1;
                }
            }
        }
        web.resize(nv, -1);
        for (int i = 0; i < nv; i++) if (web[i] < 0) web[i] = i;
        // Conservative (Briggs) coalescing: merge only if the merged node has
        // fewer than K neighbours of significant degree.
        std::vector<int> parent(nv);
        for (int i = 0; i < nv; i++) parent[i] = i;
        auto find = [&](int x) {
            while (parent[x] != x) { parent[x] = parent[parent[x]]; x = parent[x]; }
            return x;
        };
        // Per-class neighbour sets cost far more memory than the edge lists;
        // very dense functions keep the plain allocation instead.
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
        // Picks: the first node (in `nodes` order) with degree < K; if there is
        // none, the cheapest spill candidate (cost / (degree + 1), ties by
        // position). Two ordered sets keep this O(E log n) for big functions.
        std::vector<int> posOf(nv, -1);
        for (size_t i = 0; i < nodes.size(); i++) posOf[nodes[i]] = static_cast<int>(i);
        auto spillKey = [&](int v) { return noSpill[v] ? 1e200 : cost[v] / (deg[v] + 1); };
        std::set<int> low;                          // positions with degree < K
        std::set<std::pair<double, int>> high;      // (spill key, position)
        for (int v : nodes) {
            if (deg[v] < K) low.insert(posOf[v]);
            else high.insert({spillKey(v), posOf[v]});
        }
        size_t left = nodes.size();
        while (left > 0) {
            int pick;
            if (!low.empty()) {
                pick = nodes[*low.begin()];
                low.erase(low.begin());
            } else {
                pick = nodes[high.begin()->second];
                high.erase(high.begin());
            }
            removed[pick] = 1;
            stack.push_back(pick);
            left--;
            for (int n : nbr[pick]) {
                if (removed[n]) continue;
                if (deg[n] >= K) {
                    high.erase({spillKey(n), posOf[n]});
                    deg[n]--;
                    if (deg[n] < K) low.insert(posOf[n]);
                    else high.insert({spillKey(n), posOf[n]});
                } else {
                    deg[n]--;
                }
            }
        }
        std::vector<int> repColor(nv, -1);
        std::vector<int> spilled;
        int colorCursor = 0;
        for (int i = static_cast<int>(stack.size()) - 1; i >= 0; i--) {
            int v = stack[i];
            std::vector<char> taken(K, 0);
            for (int n : nbr[v]) if (repColor[n] >= 0) taken[repColor[n]] = 1;
            int c = 0;
            while (c < K && taken[c]) c++;
            if (spreadColors && c < K) {
                for (int j = 0; j < K; j++) {
                    int candidate = (colorCursor + j) % K;
                    if (!taken[candidate]) { c = candidate; colorCursor = (c + 1) % K; break; }
                }
            }
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
        // Spill every member of each spilled class, and of its spill web, to
        // one slot per web.
        std::vector<int> webSlot(nv, -1);
        std::vector<char> spillRep(nv, 0);
        for (int r : spilled) {
            if (noSpill[r]) return false;           // cannot make progress
            spillRep[r] = 1;
        }
        // Webs that are never live at the same time share a slot (greedy
        // colouring over the interference graph of their members). A slot then
        // always holds the one web that is live, exactly as a register would.
        {
            // A web goes to scratch when any member's class is spilled; then
            // every member of the web (spilled class or not) uses the slot.
            std::vector<char> webSpilled(nv, 0);
            for (int v = 0; v < nv; v++)
                if (used[v] && spillRep[find(v)]) webSpilled[web[v]] = 1;
            std::vector<int> webs;
            std::vector<std::vector<int>> members(nv);
            for (int v = 0; v < nv; v++) {
                if (!used[v] || noSpill[v] || !webSpilled[web[v]]) continue;
                const int w = web[v];
                if (members[w].empty()) webs.push_back(w);
                members[w].push_back(v);
            }
            for (int v = 0; v < nv; v++)   // a spilled member that is noSpill still needs its web's slot listed
                if (used[v] && spillRep[find(v)] && members[web[v]].empty()) { webs.push_back(web[v]); members[web[v]].push_back(v); }
            std::vector<int> color(nv, -1);
            int ncol = 0;
            std::vector<int> mark;
            for (int w : webs) {
                mark.assign(static_cast<size_t>(ncol) + 1, 0);
                for (int v : members[w])
                    for (int u : g.adj[v]) {
                        if (!used[u] || !webSpilled[web[u]] || web[u] == w) continue;
                        const int cu = color[web[u]];
                        if (cu >= 0) mark[static_cast<size_t>(cu)] = 1;
                    }
                int c = 0;
                while (c < ncol && mark[static_cast<size_t>(c)]) c++;
                color[w] = c;
                if (c == ncol) ncol++;
            }
            if (nextSlot + ncol > maxSlots) return false;
            for (int w : webs) webSlot[w] = nextSlot + color[w];
            nextSlot += ncol;
        }
        for (int v = 0; v < nv; v++) {
            if (!used[v] || noSpill[v]) continue;
            int w = web[v];
            if (webSlot[w] >= 0) slotOf[v] = webSlot[w];
        }
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
            // Per block: which temp still holds each scratch word, and where it
            // was last used. Within `reuse` instructions a use takes that temp
            // instead of loading again. (Only spill code touches scratch: the
            // program provably stays below it.)
            struct Held { int slot, temp, last; };
            std::vector<Held> held;
            int pos = 0;
            auto findHeld = [&](int slot) -> Held * {
                for (Held &h : held) if (h.slot == slot) return &h;
                return nullptr;
            };
            auto setHeld = [&](int slot, int temp) {
                if (reuse <= 0) return;
                Held *h = findHeld(slot);
                if (h) { h->temp = temp; h->last = pos; }
                else held.push_back({slot, temp, pos});
            };
            for (Inst x : B.insts) {
                pos++;
                // A copy between two values in the same scratch word does nothing.
                if (x.op == OP_MOV && x.dst >= 0 && slotOf[x.dst] >= 0 && !x.a[0].isConst &&
                    slotOf[x.a[0].v] == slotOf[x.dst])
                    continue;
                std::vector<std::pair<int, int>> loaded;
                for (int a = 0; a < x.n; a++) {
                    if (x.a[a].isConst || slotOf[x.a[a].v] < 0) continue;
                    int v = x.a[a].v, t = -1;
                    for (auto &l : loaded) if (l.first == v) t = l.second;
                    if (t < 0) {
                        Held *h = findHeld(slotOf[v]);
                        if (h && pos - h->last <= reuse) {
                            t = h->temp;
                            h->last = pos;
                        } else {
                            t = f.newVal();
                            Inst ld;
                            ld.op = OP_LOAD; ld.dst = t; ld.n = 1; ld.a[0] = slotAddr(slotOf[v]);
                            out.push_back(ld);
                            setHeld(slotOf[v], t);
                        }
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
                        Held *h = findHeld(slotOf[d]);
                        if (h) *h = held.back(), held.pop_back();
                        continue;
                    }
                    int t = f.newVal();
                    x.dst = t;
                    out.push_back(x);
                    Inst st;
                    st.op = OP_STORE; st.n = 2; st.a[0] = slotAddr(slotOf[d]); st.a[1] = Opnd::val(t);
                    out.push_back(st);
                    Held *h = findHeld(slotOf[d]);
                    if (h) *h = held.back(), held.pop_back();
                    setHeld(slotOf[d], t);
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

void preScheduleFunc(Func &f, const Machine &m, const std::vector<BlockMemInfo> &mf, bool pressure, bool bottomUp);

// Copy a tiny return block (at most 3 instructions) into each block that
// jumps to it: the jump and its taken-branch fence disappear. Then fold
// "mov a, s; ret a" into "ret s" (a is not read again after ret) and drop
// blocks nothing reaches any more. Pure copying of a block's text: the path
// executes the same instructions minus one jmp, so behaviour is unchanged.
static void duplicateReturns(Program &p) {
    const int nb = static_cast<int>(p.blocks.size());
    auto isTinyRet = [&](int t) {
        const Block &b = p.blocks[static_cast<size_t>(t)];
        return t >= 0 && t < nb && !b.ins.empty() && b.ins.size() <= 3 && b.ins.back().op == OP_RET;
    };
    bool changed = false;
    // A branch whose two targets are identical tiny return blocks is a jump.
    auto sameInstr = [](const Instr &a, const Instr &b) {
        if (a.op != b.op || a.nsrc != b.nsrc || a.k != b.k || (hasDest(a.op) && a.dst != b.dst)) return false;
        for (int s2 = 0; s2 < a.nsrc; s2++) if (a.src[s2] != b.src[s2]) return false;
        return true;
    };
    for (Block &b : p.blocks) {
        if (b.ins.empty() || b.ins.back().op != OP_BR) continue;
        Instr &t = b.ins.back();
        const int x = t.target[0], y = t.target[1];
        if (x == y || !isTinyRet(x) || !isTinyRet(y)) continue;
        const auto &bx = p.blocks[static_cast<size_t>(x)].ins, &by = p.blocks[static_cast<size_t>(y)].ins;
        if (bx.size() != by.size()) continue;
        bool same = true;
        for (size_t i = 0; i < bx.size() && same; i++) same = sameInstr(bx[i], by[i]);
        if (!same) continue;
        t.op = OP_JMP;
        t.nsrc = 0;
        t.target[1] = -1;
        changed = true;
    }
    for (int i = 0; i < nb; i++) {
        Block &b = p.blocks[static_cast<size_t>(i)];
        if (b.ins.empty() || b.ins.back().op != OP_JMP) continue;
        const int t = b.ins.back().target[0];
        if (t == i || !isTinyRet(t)) continue;
        std::vector<Instr> tail = p.blocks[static_cast<size_t>(t)].ins;   // copy: t may alias b's vector growth
        b.ins.pop_back();
        for (const Instr &x : tail) b.ins.push_back(x);
        changed = true;
    }
    for (Block &b : p.blocks) {
        const size_t n = b.ins.size();
        if (n >= 2 && b.ins[n - 1].op == OP_RET && b.ins[n - 1].nsrc == 1 && b.ins[n - 1].src[0].isReg &&
            b.ins[n - 2].op == OP_MOV && b.ins[n - 2].dst == b.ins[n - 1].src[0].v) {
            b.ins[n - 1].src[0] = b.ins[n - 2].src[0];
            b.ins.erase(b.ins.begin() + static_cast<long>(n - 2));
        }
    }
    if (!changed) return;
    std::vector<char> seen(static_cast<size_t>(nb), 0);
    std::vector<int> stack{0};
    seen[0] = 1;
    while (!stack.empty()) {
        const int x = stack.back();
        stack.pop_back();
        const Instr &term = p.blocks[static_cast<size_t>(x)].ins.back();
        for (int k = 0; k < 2; k++) {
            const int t = term.target[k];
            if ((term.op == OP_JMP && k == 0) || term.op == OP_BR) {
                if (t >= 0 && !seen[static_cast<size_t>(t)]) { seen[static_cast<size_t>(t)] = 1; stack.push_back(t); }
            }
        }
    }
    std::vector<int> remap(static_cast<size_t>(nb), -1);
    std::vector<Block> kept;
    for (int i = 0; i < nb; i++)
        if (seen[static_cast<size_t>(i)]) { remap[static_cast<size_t>(i)] = static_cast<int>(kept.size()); kept.push_back(std::move(p.blocks[static_cast<size_t>(i)])); }
    for (Block &b : kept) {
        Instr &term = b.ins.back();
        if (term.op == OP_JMP) term.target[0] = remap[static_cast<size_t>(term.target[0])];
        if (term.op == OP_BR) {
            term.target[0] = remap[static_cast<size_t>(term.target[0])];
            term.target[1] = remap[static_cast<size_t>(term.target[1])];
        }
    }
    p.blocks.swap(kept);
}

// Spill stores to a scratch word that no instruction ever loads are dead.
// Only called when every address of the program itself was proven below the
// scratch region, so the only scratch accesses are our constant-address
// spill slots.
static void dropUnreadSpillStores(Program &p) {
    std::set<uint32_t> read;
    for (const Block &b : p.blocks)
        for (const Instr &x : b.ins)
            if (x.op == OP_LOAD && !x.src[0].isReg) read.insert(x.src[0].v);
    for (Block &b : p.blocks) {
        std::vector<Instr> out;
        out.reserve(b.ins.size());
        for (const Instr &x : b.ins) {
            if (x.op == OP_STORE && !x.src[0].isReg && x.src[0].v >= kScratchBase && x.src[0].v < kMemWords &&
                !read.count(x.src[0].v))
                continue;
            out.push_back(x);
        }
        b.ins.swap(out);
    }
}

Program lowerToProgram(Func &f, const Machine &m, const BackendOptions &opt) {
    const bool scratchFree = opt.spillToK && canSpillToScratch(f);
    estimateFrequencies(f);
    std::vector<BlockMemInfo> memFacts;
    if (opt.preSchedule) memFacts = memoryFacts(f);
    destructSSA(f);
    // Optional: list-schedule on values before allocation, so independent
    // long-latency results get different registers (in-order issue waits for
    // a register's old value before writing it again).
    if (opt.preSchedule) preScheduleFunc(f, m, memFacts, opt.pressureSchedule, opt.bottomUpSchedule);
    Allocation A;
    bool haveK = false;
    if (scratchFree) {
        Func backup = f;
        // First with reloads shared inside a block; if the longer temps cannot
        // be coloured, again with one reload per use.
        haveK = allocateK(f, m.registers, A, opt.spillReuse, opt.spreadColors);
        if (!haveK && opt.spillReuse > 0) {
            f = backup;
            haveK = allocateK(f, m.registers, A, 0, opt.spreadColors);
        }
        if (!haveK) f = backup;
    }
    if (!haveK) A = allocate(f, m, opt.coalesce, opt.spreadColors);
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
    if (haveK) dropUnreadSpillStores(p);
    duplicateReturns(p);
    if (opt.schedule) scheduleProgram(p, m);
    return p;
}

// ---------------------------------------------------------------------------
// List scheduling (per block) against the exact issue model.
// ---------------------------------------------------------------------------

namespace {

// Schedule one block (its last instruction is the terminator and stays last).
// mi (pre-allocation scheduling only): facts about the block's memory
// instructions; each one carries its ordinal in target[1].
void scheduleBlock(Block &blk, const Machine &m, const BlockMemInfo *mi = nullptr, bool pressure = false,
                   const std::vector<int> *exported = nullptr, bool bottomUp = false) {
    {
        const int n = static_cast<int>(blk.ins.size());
        if (n <= 2) return;
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
        auto ordOf = [&](const Instr &a) -> int {
            if (!mi || a.target[1] < 0 || a.target[1] >= static_cast<int>(mi->safe.size())) return -1;
            return a.target[1];
        };
        auto mayAlias = [&](const Instr &a, const Instr &b) {
            const Operand &x = a.src[0], &y = b.src[0];
            if (!x.isReg && !y.isReg) return x.v == y.v;
            const int oa = ordOf(a), ob = ordOf(b);
            if (oa >= 0 && ob >= 0 && mi->disjoint[oa][ob]) return false;
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
            const int ord = isMem ? ordOf(x) : -1;
            const bool memTrap = isMem && !constAddr && !(ord >= 0 && mi->safe[ord]);
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
        if (bottomUp) {
            // Use the SAME register/effect/trap/memory graph, but select sinks
            // and construct a reverse topological order. This keeps producers
            // near their users without copying or speculating instructions.
            std::vector<int> left(body), depth(body, 0), available;
            std::vector<long> reverseAt(body, 0);
            std::vector<std::vector<std::pair<int, int>>> outEdges(body);
            for (int j = 0; j < body; j++) for (const auto &p : predLat[j]) {
                outEdges[p.first].push_back({j, p.second});
                depth[j] = std::max(depth[j], depth[p.first] + p.second);
            }
            for (int i = 0; i < body; i++) {
                left[i] = static_cast<int>(succ[i].size());
                if (!left[i]) available.push_back(i);
            }
            std::unordered_set<uint32_t> needed;
            if (exported) for (int v : *exported) needed.insert(static_cast<uint32_t>(v));
            for (int a = 0; a < blk.ins.back().nsrc; a++)
                if (blk.ins.back().src[a].isReg) needed.insert(blk.ins.back().src[a].v);
            auto increase = [&](const Instr &x) {
                int d = hasDest(x.op) && needed.count(x.dst) ? -1 : 0;
                for (int a = 0; a < x.nsrc; a++) if (x.src[a].isReg) {
                    const uint32_t r = x.src[a].v;
                    bool first = true;
                    for (int z = 0; z < a; z++) if (x.src[z].isReg && x.src[z].v == r) first = false;
                    if (first && (!needed.count(r) || (hasDest(x.op) && x.dst == r))) d++;
                }
                return d;
            };
            std::vector<Instr> reverse;
            long cycle = 0;
            int issued = 0, memIssued = 0;
            while (!available.empty()) {
                int best = -1; long bestTime = 0, bestCost = 0; int bestDelta = 0;
                for (int j : available) {
                    const Instr &x = blk.ins[j];
                    long t = cycle;
                    for (const auto &s : outEdges[j]) t = std::max(t, reverseAt[s.first] + s.second);
                    const bool mem = isMemOp(x.op);
                    if (t == cycle && (issued >= m.issue_width || (mem && memIssued >= m.mem_ports))) t++;
                    const int delta = increase(x);
                    const int excess = std::max(0, static_cast<int>(needed.size()) + delta - m.registers);
                    const long cost = t + static_cast<long>(excess) * std::max(1, m.reg_spill_penalty);
                    if (best < 0 || cost < bestCost || (cost == bestCost &&
                        (delta < bestDelta || (delta == bestDelta &&
                         (depth[j] > depth[best] || (depth[j] == depth[best] && j > best)))))) {
                        best = j; bestTime = t; bestCost = cost; bestDelta = delta;
                    }
                }
                const Instr &x = blk.ins[best];
                if (bestTime > cycle) { issued = 0; memIssued = 0; }
                cycle = bestTime; issued++; if (isMemOp(x.op)) memIssued++;
                reverseAt[best] = bestTime;
                if (hasDest(x.op)) needed.erase(x.dst);
                for (int a = 0; a < x.nsrc; a++) if (x.src[a].isReg) needed.insert(x.src[a].v);
                reverse.push_back(x);
                available.erase(std::find(available.begin(), available.end(), best));
                for (const auto &p : predLat[best]) if (--left[p.first] == 0) available.push_back(p.first);
            }
            if (static_cast<int>(reverse.size()) == body) {
                std::reverse(reverse.begin(), reverse.end());
                reverse.push_back(blk.ins.back());
                blk.ins.swap(reverse);
            }
            return;
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
        // This changes priorities only. All register, memory, trap and effect
        // edges are identical to the original scheduler. Count operand uses
        // through the terminator; repeated sources die only after their last
        // occurrence. A sentinel use preserves values needed after this block
        // or scheduling window. Correctness still follows from dependencies.
        std::unordered_map<uint32_t, int> uses;
        std::unordered_set<uint32_t> live, defined;
        if (pressure) for (const Instr &x : blk.ins) {
            for (int a = 0; a < x.nsrc; a++) if (x.src[a].isReg) {
                uses[x.src[a].v]++;
                if (!defined.count(x.src[a].v)) live.insert(x.src[a].v);
            }
            if (hasDest(x.op)) defined.insert(x.dst);
        }
        if (pressure && exported) for (int r : *exported) {
            uses[static_cast<uint32_t>(r)]++;
            if (!defined.count(static_cast<uint32_t>(r))) live.insert(static_cast<uint32_t>(r));
        }
        auto delta = [&](const Instr &x) {
            int change = hasDest(x.op) && !live.count(x.dst) ? 1 : 0;
            for (int a = 0; a < x.nsrc; a++) {
                if (!x.src[a].isReg) continue;
                const uint32_t r = x.src[a].v;
                bool first = true; int occurrences = 0;
                for (int z = 0; z < x.nsrc; z++) if (x.src[z].isReg && x.src[z].v == r) {
                    occurrences++; if (z < a) first = false;
                }
                if (first && uses[r] == occurrences && !(hasDest(x.op) && x.dst == r)) change--;
            }
            return change;
        };
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
                const bool constrained = pressure && live.size() >= static_cast<size_t>(std::max(1, m.registers - 1));
                const int rank = constrained ? delta(x) : 0;
                const int bestRank = constrained && best >= 0 ? delta(blk.ins[best]) : 0;
                if (best < 0 || t < bestT || (t == bestT && (rank < bestRank ||
                    (rank == bestRank && (height[j] > height[best] || (height[j] == height[best] && j < best)))))) {
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
            if (pressure) {
                for (int a = 0; a < x.nsrc; a++) if (x.src[a].isReg)
                    if (--uses[x.src[a].v] == 0) live.erase(x.src[a].v);
                if (hasDest(x.op)) live.insert(x.dst);
            }
            scheduled[best] = 1;
            out.push_back(x);
            avail.erase(std::find(avail.begin(), avail.end(), best));
            for (int s : succ[best])
                if (--remaining[s] == 0) avail.push_back(s);
        }
        if (static_cast<int>(out.size()) != body) return;   // should not happen; keep original order
        out.push_back(blk.ins[body]);
        blk.ins.swap(out);
    }
}

}  // namespace

void scheduleProgram(Program &p, const Machine &m) {
    // Long blocks are scheduled in windows so the cost stays linear; windows
    // keep their order, so every dependence between windows is respected.
    const int window = 96;
    for (Block &blk : p.blocks) {
        const int n = static_cast<int>(blk.ins.size());
        if (n <= window + 1) {
            scheduleBlock(blk, m);
            continue;
        }
        const int body = n - 1;
        for (int start = 0; start < body; start += window) {
            const int end = std::min(body, start + window);
            Block w;
            w.ins.assign(blk.ins.begin() + start, blk.ins.begin() + end);
            Instr stop;
            stop.op = OP_RET;
            stop.nsrc = 1;
            stop.src[0] = Operand::imm(0);
            w.ins.push_back(stop);
            scheduleBlock(w, m);
            std::copy(w.ins.begin(), w.ins.end() - 1, blk.ins.begin() + start);
        }
    }
}

// Pre-allocation scheduling: the same list scheduler, run on value numbers.
// Each instruction carries its index in target[0] so the order maps back, and
// memory instructions carry their ordinal in target[1] for the memory facts.
void preScheduleFunc(Func &f, const Machine &m, const std::vector<BlockMemInfo> &mf, bool pressure, bool bottomUp) {
    Liveness live;
    if (pressure || bottomUp) live = computeLiveness(f);
    for (int bi = 0; bi < static_cast<int>(f.bb.size()); bi++) {
        BB &B = f.bb[bi];
        if (!B.alive || B.insts.size() <= 2) continue;
        const BlockMemInfo *mi = bi < static_cast<int>(mf.size()) && !mf[bi].safe.empty() ? &mf[bi] : nullptr;
        Block w;
        int ord = 0;
        for (size_t i = 0; i < B.insts.size(); i++) {
            const Inst &x = B.insts[i];
            Instr y;
            y.op = x.op;
            y.k = x.k;
            y.nsrc = x.n;
            if (x.dst >= 0) y.dst = static_cast<uint32_t>(x.dst);
            for (int a = 0; a < x.n; a++)
                y.src[a] = x.a[a].isConst ? Operand::imm(x.a[a].c) : Operand::reg(static_cast<uint32_t>(x.a[a].v));
            y.target[0] = static_cast<int>(i);
            y.target[1] = (x.op == OP_LOAD || x.op == OP_STORE) ? ord++ : -1;
            w.ins.push_back(y);
        }
        if (mi && ord != static_cast<int>(mi->safe.size())) mi = nullptr;   // order changed: no facts
        // Windows of 96 keep long blocks linear (as in scheduleProgram).
        const int window = 96;
        const int n = static_cast<int>(w.ins.size());
        if (n <= window + 1) {
            scheduleBlock(w, m, mi, pressure, (pressure || bottomUp) ? &live.liveOut[bi] : nullptr, bottomUp);
        } else {
            const int body = n - 1;
            std::vector<std::vector<int>> boundary;
            if (pressure || bottomUp) {
                boundary.resize((body + window - 1) / window);
                std::unordered_set<int> future(live.liveOut[bi].begin(), live.liveOut[bi].end());
                for (int a = 0; a < w.ins.back().nsrc; a++)
                    if (w.ins.back().src[a].isReg) future.insert(static_cast<int>(w.ins.back().src[a].v));
                for (int i = body - 1; i >= 0; i--) {
                    if (i == body - 1 || (i + 1) % window == 0)
                        boundary[i / window].assign(future.begin(), future.end());
                    const Instr &x = w.ins[i];
                    if (hasDest(x.op)) future.erase(static_cast<int>(x.dst));
                    for (int a = 0; a < x.nsrc; a++)
                        if (x.src[a].isReg) future.insert(static_cast<int>(x.src[a].v));
                }
            }
            for (int start = 0; start < body; start += window) {
                const int end = std::min(body, start + window);
                Block part;
                part.ins.assign(w.ins.begin() + start, w.ins.begin() + end);
                Instr stop;
                stop.op = OP_RET;
                stop.nsrc = 1;
                stop.src[0] = Operand::imm(0);
                part.ins.push_back(stop);
                scheduleBlock(part, m, mi, pressure, (pressure || bottomUp) ? &boundary[start / window] : nullptr, bottomUp);
                std::copy(part.ins.begin(), part.ins.end() - 1, w.ins.begin() + start);
            }
        }
        std::vector<Inst> out;
        out.reserve(B.insts.size());
        for (const Instr &y : w.ins) out.push_back(B.insts[static_cast<size_t>(y.target[0])]);
        B.insts.swap(out);
    }
}

}  // namespace kopt
