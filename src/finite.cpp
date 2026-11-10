// Source-derived finite-domain evaluation of pure, masked-input functions.
#include "passes.h"

#include <algorithm>
#include <map>
#include <tuple>
#include <vector>

namespace kopt {
namespace {

struct FiniteBit { size_t param; uint32_t mask; };
struct FiniteNode {
    int bit = -1, low = -1, high = -1;
    uint32_t value = 0;
};

}  // namespace

bool finiteFunction(const Program &original, const Machine &, Program &out) {
    // Bound SSA construction separately from the exhaustive interpreter work.
    if (original.blocks.empty() || original.blocks.size() > 256 ||
        original.params.size() > 8 || original.instrCount() > 8000) return false;
    for (const Block &b : original.blocks) for (const Instr &x : b.ins)
        if (isMemOp(x.op) || x.op == OP_TRAP) return false;

    Func f;
    std::string err;
    if (!buildSSA(original, f, err)) return false;
    instSimplify(f);
    dce(f);
    simplifyCFG(f);
    f.resolveAll();
    std::vector<int> paramOf(f.nvals, -1);
    std::vector<uint32_t> masks(f.params.size(), 0);
    for (size_t p = 0; p < f.params.size(); p++) paramOf[f.params[p]] = static_cast<int>(p);
    for (const BB &b : f.bb) {
        if (!b.alive) continue;
        for (const Phi &ph : b.phis) for (const auto &in : ph.in)
            if (!in.second.isConst && paramOf[in.second.v] >= 0) return false;
        for (const Inst &x : b.insts) for (int a = 0; a < x.n; a++) {
            const Opnd o = x.a[a];
            if (o.isConst || paramOf[o.v] < 0) continue;
            if (x.op != OP_AND || x.n != 2 || !x.a[1 - a].isConst) return false;
            masks[paramOf[o.v]] |= x.a[1 - a].c;
        }
    }

    // Every remaining read of a raw parameter is AND with a literal. Thus
    // replacing an input by input & union(mask) preserves every such result,
    // and all subsequent SSA values, control flow and termination are equal.
    // Parameter bits are counted separately even when their bit positions match.
    std::vector<FiniteBit> bits;
    for (size_t p = 0; p < masks.size(); p++) for (unsigned b = 0; b < 32; b++)
        if ((masks[p] & (uint32_t{1} << b)) != 0) {
            bits.push_back({p, uint32_t{1} << b});
            if (bits.size() > 6) return false;
        }

    const SimProgram sim(original);
    std::vector<uint32_t> table(size_t{1} << bits.size());
    uint64_t remaining = 1000000;
    for (size_t key = 0; key < table.size(); key++) {
        if (remaining == 0) return false;
        Input input;
        input.args.assign(original.params.size(), 0);
        for (size_t b = 0; b < bits.size(); b++)
            if ((key & (size_t{1} << b)) != 0) input.args[bits[b].param] |= bits[b].mask;
        const RunResult result = sim.run(input, std::min<uint64_t>(remaining, 20000), false);
        remaining -= result.steps;
        if (result.status != Status::RET) return false;
        table[key] = result.value;
    }

    // At most 127 nodes / recursion depth 6. Equal leaves and equal decision
    // subtables are shared; tests whose two branches agree disappear entirely.
    std::vector<FiniteNode> nodes;
    std::map<uint32_t, int> leaves;
    std::map<std::tuple<int, int, int>, int> decisions;
    auto build = [&](auto &&self, int level, size_t key) -> int {
        if (level == static_cast<int>(bits.size())) {
            const uint32_t value = table[key];
            const auto found = leaves.find(value);
            if (found != leaves.end()) return found->second;
            const int id = static_cast<int>(nodes.size());
            nodes.push_back({-1, -1, -1, value});
            leaves.emplace(value, id);
            return id;
        }
        const int low = self(self, level + 1, key);
        const int high = self(self, level + 1, key | (size_t{1} << level));
        if (low == high) return low;
        const auto signature = std::make_tuple(level, low, high);
        const auto found = decisions.find(signature);
        if (found != decisions.end()) return found->second;
        const int id = static_cast<int>(nodes.size());
        nodes.push_back({level, low, high, 0});
        decisions.emplace(signature, id);
        return id;
    };
    const int root = build(build, 0, 0);
    auto selectLeaf = [&](const FiniteNode &n) {
        return n.bit >= 0 && nodes[n.low].bit < 0 && nodes[n.high].bit < 0;
    };
    std::vector<int> order, blockOf(nodes.size(), -1), stack{root};
    while (!stack.empty()) {
        const int id = stack.back(); stack.pop_back();
        if (blockOf[id] >= 0) continue;
        blockOf[id] = static_cast<int>(order.size());
        order.push_back(id);
        const FiniteNode &n = nodes[id];
        if (n.bit >= 0 && !selectLeaf(n)) { stack.push_back(n.high); stack.push_back(n.low); }
    }

    Program candidate;
    candidate.name = original.name;
    candidate.params = original.params;
    uint32_t temp = 0;
    while (std::find(candidate.params.begin(), candidate.params.end(), temp) != candidate.params.end()) temp++;
    for (int id : order) {
        const FiniteNode &n = nodes[id];
        Block b;
        b.label = "finite_" + std::to_string(blockOf[id]);
        Instr ret;
        ret.op = OP_RET; ret.nsrc = 1;
        if (n.bit < 0) {
            ret.src[0] = Operand::imm(n.value);
            b.ins.push_back(ret);
        } else {
            Instr test;
            test.op = OP_AND; test.dst = temp; test.nsrc = 2;
            test.src[0] = Operand::reg(original.params[bits[n.bit].param]);
            test.src[1] = Operand::imm(bits[n.bit].mask);
            b.ins.push_back(test);
            if (selectLeaf(n)) {
                Instr select;
                select.op = OP_SELECT; select.dst = temp; select.nsrc = 3;
                select.src[0] = Operand::reg(temp);
                select.src[1] = Operand::imm(nodes[n.high].value);
                select.src[2] = Operand::imm(nodes[n.low].value);
                b.ins.push_back(select);
                ret.src[0] = Operand::reg(temp);
                b.ins.push_back(ret);
            } else {
                Instr branch;
                branch.op = OP_BR; branch.nsrc = 1; branch.src[0] = Operand::reg(temp);
                branch.target[0] = blockOf[n.high]; branch.target[1] = blockOf[n.low];
                b.ins.push_back(branch);
            }
        }
        candidate.blocks.push_back(std::move(b));
    }
    out = std::move(candidate);  // A rejection leaves the caller's output intact.
    return true;
}

}  // namespace kopt
