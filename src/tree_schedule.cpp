// Pressure-oriented scheduling across long straight-line pure regions.
#include "passes.h"
#include <algorithm>
#include <array>

namespace kopt {
bool schedulePureTrees(Func &f) {
    f.resolveAll();
    auto pure = [](Op op) {
        switch (op) {
        case OP_MOV: case OP_ADD: case OP_SUB: case OP_MUL: case OP_AND: case OP_OR:
        case OP_XOR: case OP_SHL: case OP_SHR: case OP_LT: case OP_EQ: case OP_SELECT:
        case OP_MAC: case OP_ADDSH: return true;
        default: return false;
        }
    };
    // No shared global analysis state: this is an ordering-only transform.
    std::vector<int> location(f.nvals, -1), stamp(f.nvals, -1);
    int region = 0;
    bool changed = false;
    for (BB &block : f.bb) {
        if (!block.alive) continue;
        for (size_t begin = 0; begin < block.insts.size();) {
            if (!pure(block.insts[begin].op) || block.insts[begin].dst < 0) { begin++; continue; }
            size_t end = begin;
            while (end < block.insts.size() && pure(block.insts[end].op) && block.insts[end].dst >= 0) end++;
            const int n = static_cast<int>(end - begin);
            if (n < 6) { begin = end; continue; }
            region++;
            std::vector<std::array<int, 3>> children(n);
            std::vector<int> count(n, 0), need(n, 1), uses(n, 0);
            bool valid = true;
            for (int i = 0; i < n; i++) {
                const Val v = block.insts[begin + i].dst;
                if (stamp[v] == region) valid = false;  // require true SSA
                stamp[v] = region; location[v] = i;
            }
            for (int i = 0; i < n && valid; i++) {
                const Inst &x = block.insts[begin + i];
                for (int a = 0; a < x.n; a++) {
                    if (x.a[a].isConst || stamp[x.a[a].v] != region) continue;
                    const int child = location[x.a[a].v];
                    if (child >= i) { valid = false; break; }
                    bool duplicate = false;
                    for (int k = 0; k < count[i]; k++) duplicate |= children[i][k] == child;
                    if (!duplicate) { children[i][count[i]++] = child; uses[child]++; }
                }
                std::sort(children[i].begin(), children[i].begin() + count[i], [&](int a, int b) {
                    return need[a] != need[b] ? need[a] > need[b] : a < b;
                });
                for (int k = 0; k < count[i]; k++) need[i] = std::max(need[i], need[children[i][k]] + k);
            }
            if (!valid) { begin = end; continue; }
            // Iterative postorder avoids a stack overflow on 100k-deep sums.
            std::vector<char> emitted(n, 0);
            std::vector<std::pair<int, int>> stack;
            std::vector<int> order;
            auto visit = [&](int root) {
                if (emitted[root]) return;
                stack.push_back({root, 0});
                while (!stack.empty()) {
                    auto &top = stack.back();
                    if (top.second < count[top.first]) {
                        const int child = children[top.first][top.second++];
                        if (!emitted[child]) stack.push_back({child, 0});
                    } else {
                        const int node = top.first; stack.pop_back();
                        if (!emitted[node]) { emitted[node] = 1; order.push_back(node); }
                    }
                }
            };
            for (int i = n - 1; i >= 0; i--) if (!uses[i]) visit(i);
            for (int i = 0; i < n; i++) visit(i);
            std::vector<Inst> output;
            output.reserve(n);
            for (int i = 0; i < n; i++) {
                if (order[i] != i) changed = true;
                output.push_back(block.insts[begin + order[i]]);
            }
            std::copy(output.begin(), output.end(), block.insts.begin() + static_cast<long>(begin));
            begin = end;
        }
    }
    return changed;
}
}  // namespace kopt
