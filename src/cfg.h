// cfg.h - control-flow analyses on Func: reverse postorder, dominator tree
// (Cooper, Harvey and Kennedy, "A Simple, Fast Dominance Algorithm"),
// dominance frontiers, and natural loops with nesting depth.
#pragma once

#include <vector>

#include "ir.h"

namespace kopt {

struct DomInfo {
    std::vector<int> rpo;          // reachable blocks in reverse postorder (entry first)
    std::vector<int> rpoIndex;     // position in rpo, -1 if unreachable
    std::vector<int> idom;         // immediate dominator, -1 for entry and unreachable blocks
    std::vector<std::vector<int>> children;
    std::vector<int> pre, post;    // dominator-tree DFS numbers (for O(1) dominance tests)
    bool reachable(int b) const { return rpoIndex[b] >= 0; }
    bool dominates(int a, int b) const { return pre[a] <= pre[b] && post[b] <= post[a]; }
};

DomInfo computeDominators(const Func &f);

std::vector<std::vector<int>> dominanceFrontiers(const Func &f, const DomInfo &d);

struct LoopInfo {
    // A natural loop per back edge target (header); bodies of loops that share a
    // header are merged. Irreducible cycles are not loops here.
    struct Loop {
        int header;
        std::vector<int> blocks;    // includes the header
        std::vector<int> latches;   // sources of back edges
        int parent = -1;            // enclosing loop index or -1
        int depth = 1;
    };
    std::vector<Loop> loops;
    std::vector<int> innermost;     // per block: innermost loop index or -1
    std::vector<int> depth;         // per block: loop nesting depth
    bool inLoop(int block, int loop) const;
};

LoopInfo computeLoops(const Func &f, const DomInfo &d);

// Blocks that sit on a cycle the natural-loop analysis does not see
// (irreducible control flow). Used to stay conservative.
std::vector<bool> irreducibleBlocks(const Func &f, const DomInfo &d);

}  // namespace kopt
