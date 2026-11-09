#include "cfg.h"

#include <algorithm>

namespace kopt {

DomInfo computeDominators(const Func &f) {
    const int n = static_cast<int>(f.bb.size());
    DomInfo d;
    d.rpoIndex.assign(n, -1);
    d.idom.assign(n, -1);
    d.children.assign(n, {});
    d.pre.assign(n, -1);
    d.post.assign(n, -1);

    // Iterative DFS for postorder (programs can have tens of thousands of blocks).
    std::vector<int> post;
    std::vector<char> seen(n, 0);
    std::vector<std::pair<int, int>> stack;
    stack.push_back({0, 0});
    seen[0] = 1;
    while (!stack.empty()) {
        auto &top = stack.back();
        int b = top.first;
        int s[2];
        int ns = f.succs(b, s);
        if (top.second < ns) {
            int t = s[top.second++];
            if (!seen[t] && f.bb[t].alive) {
                seen[t] = 1;
                stack.push_back({t, 0});
            }
        } else {
            post.push_back(b);
            stack.pop_back();
        }
    }
    d.rpo.assign(post.rbegin(), post.rend());
    for (int i = 0; i < static_cast<int>(d.rpo.size()); i++) d.rpoIndex[d.rpo[i]] = i;

    // Cooper-Harvey-Kennedy.
    d.idom[0] = 0;
    bool changed = true;
    auto intersect = [&](int a, int b) {
        while (a != b) {
            while (d.rpoIndex[a] > d.rpoIndex[b]) a = d.idom[a];
            while (d.rpoIndex[b] > d.rpoIndex[a]) b = d.idom[b];
        }
        return a;
    };
    while (changed) {
        changed = false;
        for (size_t i = 1; i < d.rpo.size(); i++) {
            int b = d.rpo[i];
            int nidom = -1;
            for (int p : f.bb[b].preds) {
                if (d.rpoIndex[p] < 0 || d.idom[p] < 0) continue;
                nidom = (nidom < 0) ? p : intersect(p, nidom);
            }
            if (nidom >= 0 && d.idom[b] != nidom) {
                d.idom[b] = nidom;
                changed = true;
            }
        }
    }
    d.idom[0] = -1;
    for (int b : d.rpo)
        if (d.idom[b] >= 0) d.children[d.idom[b]].push_back(b);
    // Dominator tree numbering.
    int clock = 0;
    std::vector<std::pair<int, size_t>> st;
    st.push_back({0, 0});
    d.pre[0] = clock++;
    while (!st.empty()) {
        auto &top = st.back();
        if (top.second < d.children[top.first].size()) {
            int c = d.children[top.first][top.second++];
            d.pre[c] = clock++;
            st.push_back({c, 0});
        } else {
            d.post[top.first] = clock++;
            st.pop_back();
        }
    }
    return d;
}

std::vector<std::vector<int>> dominanceFrontiers(const Func &f, const DomInfo &d) {
    const int n = static_cast<int>(f.bb.size());
    std::vector<std::vector<int>> df(n);
    for (int b : d.rpo) {
        const auto &preds = f.bb[b].preds;
        if (preds.size() < 2) continue;
        for (int p : preds) {
            if (!d.reachable(p)) continue;
            int runner = p;
            while (runner != d.idom[b] && runner >= 0) {
                auto &v = df[runner];
                if (v.empty() || v.back() != b) v.push_back(b);
                if (runner == d.idom[runner]) break;
                runner = d.idom[runner];
            }
        }
    }
    for (auto &v : df) {
        std::sort(v.begin(), v.end());
        v.erase(std::unique(v.begin(), v.end()), v.end());
    }
    return df;
}

bool LoopInfo::inLoop(int block, int loop) const {
    for (int l = innermost[block]; l >= 0; l = loops[l].parent)
        if (l == loop) return true;
    return false;
}

LoopInfo computeLoops(const Func &f, const DomInfo &d) {
    const int n = static_cast<int>(f.bb.size());
    LoopInfo li;
    li.innermost.assign(n, -1);
    li.depth.assign(n, 0);
    std::vector<int> loopOfHeader(n, -1);
    // Back edges: t -> h where h dominates t.
    for (int b : d.rpo) {
        int s[2];
        int ns = f.succs(b, s);
        for (int i = 0; i < ns; i++) {
            int h = s[i];
            if (!d.reachable(h) || !d.dominates(h, b)) continue;
            if (loopOfHeader[h] < 0) {
                loopOfHeader[h] = static_cast<int>(li.loops.size());
                li.loops.push_back(LoopInfo::Loop{h, {}, {}, -1, 1});
            }
            auto &lat = li.loops[loopOfHeader[h]].latches;
            if (std::find(lat.begin(), lat.end(), b) == lat.end()) lat.push_back(b);
        }
    }
    // Bodies: walk predecessors back from the latches up to the header.
    std::vector<int> mark(n, -1);
    for (int l = 0; l < static_cast<int>(li.loops.size()); l++) {
        auto &L = li.loops[l];
        std::vector<int> work;
        mark[L.header] = l;
        L.blocks.push_back(L.header);
        for (int t : L.latches)
            if (mark[t] != l) { mark[t] = l; L.blocks.push_back(t); work.push_back(t); }
        while (!work.empty()) {
            int b = work.back();
            work.pop_back();
            for (int p : f.bb[b].preds) {
                if (!d.reachable(p) || mark[p] == l) continue;
                mark[p] = l;
                L.blocks.push_back(p);
                work.push_back(p);
            }
        }
    }
    // Nesting: a loop's parent is the smallest other loop containing its header.
    std::vector<int> order(li.loops.size());
    for (size_t i = 0; i < order.size(); i++) order[i] = static_cast<int>(i);
    std::sort(order.begin(), order.end(), [&](int a, int b) {
        return li.loops[a].blocks.size() > li.loops[b].blocks.size();
    });
    for (int l : order) {   // big loops first, so inner loops overwrite
        for (int b : li.loops[l].blocks) {
            int prev = li.innermost[b];
            if (prev >= 0 && prev != l && b == li.loops[l].header) li.loops[l].parent = prev;
            li.innermost[b] = l;
        }
    }
    for (int l : order) {
        int p = li.loops[l].parent;
        li.loops[l].depth = (p >= 0) ? li.loops[p].depth + 1 : 1;
    }
    for (int b = 0; b < n; b++)
        li.depth[b] = (li.innermost[b] >= 0) ? li.loops[li.innermost[b]].depth : 0;
    return li;
}

std::vector<bool> irreducibleBlocks(const Func &f, const DomInfo &d) {
    // Retreating edges (to an earlier block in RPO) whose target does not
    // dominate the source make the region irreducible. Mark both ends and every
    // block that reaches the source while staying after the target in RPO.
    const int n = static_cast<int>(f.bb.size());
    std::vector<bool> irr(n, false);
    for (int b : d.rpo) {
        int s[2];
        int ns = f.succs(b, s);
        for (int i = 0; i < ns; i++) {
            int t = s[i];
            if (!d.reachable(t)) continue;
            if (d.rpoIndex[t] <= d.rpoIndex[b] && !d.dominates(t, b)) {
                std::vector<int> work{b};
                std::vector<char> seen(n, 0);
                seen[b] = 1;
                irr[t] = true;
                while (!work.empty()) {
                    int x = work.back();
                    work.pop_back();
                    irr[x] = true;
                    if (x == t) continue;
                    for (int p : f.bb[x].preds)
                        if (d.reachable(p) && !seen[p] && d.rpoIndex[p] >= d.rpoIndex[t]) {
                            seen[p] = 1;
                            work.push_back(p);
                        }
                }
            }
        }
    }
    return irr;
}

}  // namespace kopt
