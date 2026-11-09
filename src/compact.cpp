// Share identical register-form blocks. Only control-flow targets change;
// stores, traps and volatile accesses execute exactly as often as before.
#include "kir.h"
#include <map>
#include <sstream>
#include <set>

namespace kopt {
Program compactBlocks(const Program &input, bool shareTails) {
    Program p = input;
    if (shareTails && p.blocks.size() <= 128) {
        auto same = [](const Instr &a, const Instr &b) {
            if (a.op != b.op || a.nsrc != b.nsrc || a.k != b.k) return false;
            if (hasDest(a.op) && a.dst != b.dst) return false;
            for (int i = 0; i < a.nsrc; i++) if (a.src[i] != b.src[i]) return false;
            if ((a.op == OP_JMP || a.op == OP_BR) && a.target[0] != b.target[0]) return false;
            return a.op != OP_BR || a.target[1] == b.target[1];
        };
        std::set<std::string> labels;
        for (const Block &b : p.blocks) labels.insert(b.label);
        for (int round = 0; round < 4; round++) {
            size_t best = 3, first = 0, second = 0;
            for (size_t a = 0; a < p.blocks.size(); a++)
                for (size_t b = a + 1; b < p.blocks.size(); b++) {
                    const auto &x = p.blocks[a].ins, &y = p.blocks[b].ins;
                    size_t count = 0;
                    while (count < 32 && count + 1 < x.size() && count + 1 < y.size() &&
                           same(x[x.size() - 1 - count], y[y.size() - 1 - count])) count++;
                    if (count > best) { best = count; first = a; second = b; }
                }
            if (best <= 3) break;
            Block tail;
            int name = 0;
            do { tail.label = "shared_tail_" + std::to_string(name++); } while (labels.count(tail.label));
            labels.insert(tail.label);
            const auto &body = p.blocks[first].ins;
            tail.ins.assign(body.end() - static_cast<long>(best), body.end());
            const int target = static_cast<int>(p.blocks.size());
            for (size_t b : {first, second}) {
                auto &ins = p.blocks[b].ins;
                ins.resize(ins.size() - best);
                Instr jump; jump.op = OP_JMP; jump.target[0] = target;
                ins.push_back(jump);
            }
            p.blocks.push_back(std::move(tail));
        }
    }
    const int nb = static_cast<int>(p.blocks.size());
    std::vector<int> representative(nb);
    for (int b = 0; b < nb; b++) representative[b] = b;
    auto root = [&](int b) {
        while (representative[b] != b) { representative[b] = representative[representative[b]]; b = representative[b]; }
        return b;
    };
    for (int round = 0; round < 8; round++) {
        bool changed = false;
        std::map<std::string, int> known;
        for (int b = 0; b < nb; b++) {
            if (root(b) != b) continue;
            std::ostringstream key;
            for (const Instr &x : p.blocks[b].ins) {
                key << static_cast<int>(x.op) << ':';
                if (hasDest(x.op)) key << x.dst;
                key << ':' << x.k;
                for (int i = 0; i < x.nsrc; i++) key << ':' << x.src[i].isReg << ':' << x.src[i].v;
                if (x.op == OP_JMP || x.op == OP_BR) key << ':' << root(x.target[0]);
                if (x.op == OP_BR) key << ':' << root(x.target[1]);
                key << ';';
            }
            const auto inserted = known.emplace(key.str(), b);
            if (!inserted.second) { representative[b] = inserted.first->second; changed = true; }
        }
        if (!changed) break;
    }
    for (Block &b : p.blocks) {
        Instr &t = b.ins.back();
        if (t.op == OP_JMP || t.op == OP_BR) t.target[0] = root(t.target[0]);
        if (t.op == OP_BR) t.target[1] = root(t.target[1]);
    }
    // Remove unreachable copies, including chains made unreachable by sharing.
    std::vector<char> seen(nb, 0);
    std::vector<int> stack{0}; seen[0] = 1;
    while (!stack.empty()) {
        const int b = stack.back(); stack.pop_back();
        const Instr &t = p.blocks[b].ins.back();
        const int ns = t.op == OP_BR ? 2 : (t.op == OP_JMP ? 1 : 0);
        for (int i = 0; i < ns; i++) if (!seen[t.target[i]]) {
            seen[t.target[i]] = 1; stack.push_back(t.target[i]);
        }
    }
    std::vector<int> index(nb, -1);
    Program out; out.name = p.name; out.params = p.params;
    for (int b = 0; b < nb; b++) if (seen[b]) {
        index[b] = static_cast<int>(out.blocks.size()); out.blocks.push_back(p.blocks[b]);
    }
    for (Block &b : out.blocks) {
        Instr &t = b.ins.back();
        if (t.op == OP_JMP || t.op == OP_BR) t.target[0] = index[t.target[0]];
        if (t.op == OP_BR) t.target[1] = index[t.target[1]];
    }
    return out;
}
}  // namespace kopt
