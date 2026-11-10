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

struct FiniteDomain {
    std::vector<FiniteBit> bits;
    std::vector<uint32_t> table;
};

bool evaluateFinite(const Program &original, FiniteDomain &domain, unsigned maxBits = 6, unsigned minBits = 0) {
    // Bound SSA construction separately from the exhaustive interpreter work.
    if (original.blocks.empty() || original.blocks.size() > 256 ||
        original.params.size() > 8 || original.instrCount() > 8000) return false;
    for (const Block &b : original.blocks) for (const Instr &x : b.ins)
        if (isMemOp(x.op) || x.op == OP_TRAP) return false;

    std::vector<uint32_t> masks;
    if (!finiteInputMasksUpTo(original, masks, maxBits)) return false;

    // Exact backward bit-demand analysis proves projected-input equivalence.
    // Exhaustive evaluation below establishes totality and every table value.
    std::vector<FiniteBit> &bits = domain.bits;
    for (size_t p = 0; p < masks.size(); p++) for (unsigned b = 0; b < 32; b++)
        if ((masks[p] & (uint32_t{1} << b)) != 0) {
            bits.push_back({p, uint32_t{1} << b});
            if (bits.size() > maxBits) return false;
        }

    if (bits.size() < minBits) return false;
    const SimProgram sim(original);
    std::vector<uint32_t> &table = domain.table;
    table.resize(size_t{1} << bits.size());
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
    return true;
}

bool emitDecision(const Program &original, const FiniteDomain &domain, Program &out) {
    const auto &bits = domain.bits;
    const auto &table = domain.table;

    // At most 2047 nodes / recursion depth 10 (127 / 6 in the default mode). Equal leaves and equal decision
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

// Alternative only: caller retains the BDD/original candidates and measures.
// Three low scratch names suffice; no original parameter is ever overwritten.
bool emitPacked(const Program &original, const FiniteDomain &domain, Program &out, size_t maxWords = 16) {
    const auto &bits = domain.bits;
    const auto &table = domain.table;
    const auto bounds = std::minmax_element(table.begin(), table.end());
    const uint32_t minimum = *bounds.first, maximum = *bounds.second;
    auto fieldWidth = [](uint32_t range) {
        for (unsigned width : {1u, 2u, 4u, 8u, 16u})
            if (range <= ((uint32_t{1} << width) - 1)) return width;
        return 32u;
    };
    // Unsigned minimum makes every subtraction exact (not a signed range or
    // a cyclic interval). Use base zero when subtraction saves no field bits.
    const unsigned width = fieldWidth(maximum - minimum);
    const uint32_t base = fieldWidth(maximum) == width ? 0 : minimum;
    const unsigned entries = 32 / width;
    const size_t wordCount = (table.size() + entries - 1) / entries;
    if (wordCount > maxWords) return false;
    std::vector<uint32_t> words(wordCount, 0);
    for (size_t i = 0; i < table.size(); i++)
        words[i / entries] |= (table[i] - base) << ((i % entries) * width);

    Program candidate;
    candidate.name = original.name;
    candidate.params = original.params;
    uint32_t cursor = 0;
    auto fresh = [&]() {
        while (std::find(candidate.params.begin(), candidate.params.end(), cursor) != candidate.params.end()) cursor++;
        return cursor++;
    };
    const uint32_t wordReg = fresh(), keyReg = fresh(), partReg = fresh();
    auto binary = [](Op op, uint32_t dst, Operand a, Operand b) {
        Instr x;
        x.op = op; x.dst = dst; x.nsrc = 2; x.src[0] = a; x.src[1] = b;
        return x;
    };
    auto finish = [](Operand value) {
        Instr x; x.op = OP_RET; x.nsrc = 1; x.src[0] = value; return x;
    };
    if (minimum == maximum) {
        Block b; b.label = "packed_0"; b.ins.push_back(finish(Operand::imm(minimum)));
        candidate.blocks.push_back(std::move(b));
        out = std::move(candidate);
        return true;
    }
    unsigned logWidth = 0, lowBits = 0;
    while ((1u << logWidth) < width) logWidth++;
    while ((1u << lowBits) < entries && lowBits < bits.size()) lowBits++;

    // Select a constant word with the HIGH key bits. Reading their original
    // parameter bits directly is exactly the same key assignment as the BDD.
    // At most 64 words / depth 6 in the wide alternative; equal words/subtables share one node.
    std::vector<FiniteNode> nodes;
    std::map<std::tuple<int, int, int>, int> decisions;
    std::map<uint32_t, int> leaves;
    auto build = [&](auto &&self, unsigned level, size_t key) -> int {
        if (level == bits.size()) {
            const uint32_t value = words[key];
            const auto found = leaves.find(value);
            if (found != leaves.end()) return found->second;
            const int id = static_cast<int>(nodes.size());
            nodes.push_back({-1, -1, -1, value}); leaves.emplace(value, id);
            return id;
        }
        const int low = self(self, level + 1, key);
        const int high = self(self, level + 1, key | (size_t{1} << (level - lowBits)));
        if (low == high) return low;
        const auto signature = std::make_tuple(static_cast<int>(level), low, high);
        const auto found = decisions.find(signature);
        if (found != decisions.end()) return found->second;
        const int id = static_cast<int>(nodes.size());
        nodes.push_back({static_cast<int>(level), low, high, 0}); decisions.emplace(signature, id);
        return id;
    };
    const int root = build(build, lowBits, 0);
    auto selectLeaf = [&](const FiniteNode &n) {
        return n.bit >= 0 && nodes[n.low].bit < 0 && nodes[n.high].bit < 0;
    };
    std::vector<int> order, blockOf(nodes.size(), -1), stack{root};
    while (!stack.empty()) {
        const int id = stack.back(); stack.pop_back();
        if (blockOf[id] >= 0) continue;
        blockOf[id] = static_cast<int>(order.size()); order.push_back(id);
        const FiniteNode &n = nodes[id];
        if (n.bit >= 0 && !selectLeaf(n)) { stack.push_back(n.high); stack.push_back(n.low); }
    }
    // A single constant word is used as an immediate, needing no selector.
    const bool constantWord = nodes[root].bit < 0;
    const int decode = constantWord ? 0 : static_cast<int>(order.size());
    if (!constantWord) for (int id : order) {
        const FiniteNode &n = nodes[id];
        Block b; b.label = "packed_" + std::to_string(blockOf[id]);
        bool leaf = n.bit < 0 || selectLeaf(n);
        if (n.bit < 0) {
            Instr x; x.op = OP_CONST; x.dst = wordReg; x.nsrc = 1; x.src[0] = Operand::imm(n.value);
            b.ins.push_back(x);
        } else {
            b.ins.push_back(binary(OP_AND, wordReg,
                Operand::reg(original.params[bits[n.bit].param]), Operand::imm(bits[n.bit].mask)));
            if (leaf) {
                Instr x; x.op = OP_SELECT; x.dst = wordReg; x.nsrc = 3;
                x.src[0] = Operand::reg(wordReg); x.src[1] = Operand::imm(nodes[n.high].value);
                x.src[2] = Operand::imm(nodes[n.low].value); b.ins.push_back(x);
            } else {
                Instr x; x.op = OP_BR; x.nsrc = 1; x.src[0] = Operand::reg(wordReg);
                x.target[0] = blockOf[n.high]; x.target[1] = blockOf[n.low]; b.ins.push_back(x);
            }
        }
        if (leaf) { Instr jump; jump.op = OP_JMP; jump.target[0] = decode; b.ins.push_back(jump); }
        candidate.blocks.push_back(std::move(b));
    }

    Block b; b.label = "packed_decode";
    const Operand word = constantWord ? Operand::imm(nodes[root].value) : Operand::reg(wordReg);
    if (lowBits == 0) {
        b.ins.push_back(finish(word));  // Width 32: no shift by 32 or mask overflow.
    } else {
        // Combine contiguous source runs with one AND and at most one shift.
        // Runs retain parameter order, bit-31 handling and sparse bit order.
        for (unsigned at = 0; at < lowBits;) {
            unsigned end = at + 1;
            uint32_t mask = bits[at].mask;
            while (end < lowBits && bits[end].param == bits[at].param &&
                   bits[end - 1].mask < 0x80000000u && bits[end].mask == (bits[end - 1].mask << 1))
                mask |= bits[end++].mask;
            unsigned sourceBit = 0;
            while ((uint32_t{1} << sourceBit) != bits[at].mask) sourceBit++;
            const uint32_t dst = at == 0 ? keyReg : partReg;
            b.ins.push_back(binary(OP_AND, dst, Operand::reg(original.params[bits[at].param]), Operand::imm(mask)));
            if (sourceBit != at) b.ins.push_back(binary(sourceBit > at ? OP_SHR : OP_SHL,
                dst, Operand::reg(dst), Operand::imm(sourceBit > at ? sourceBit - at : at - sourceBit)));
            if (at != 0) b.ins.push_back(binary(OP_OR, keyReg, Operand::reg(keyReg), Operand::reg(partReg)));
            at = end;
        }
        if (logWidth != 0) b.ins.push_back(binary(OP_SHL, keyReg, Operand::reg(keyReg), Operand::imm(logWidth)));
        b.ins.push_back(binary(OP_SHR, keyReg, word, Operand::reg(keyReg)));
        b.ins.push_back(binary(OP_AND, keyReg, Operand::reg(keyReg), Operand::imm((uint32_t{1} << width) - 1)));
        if (base != 0) b.ins.push_back(binary(OP_ADD, keyReg, Operand::reg(keyReg), Operand::imm(base)));
        b.ins.push_back(finish(Operand::reg(keyReg)));
    }
    candidate.blocks.push_back(std::move(b));
    out = std::move(candidate);
    return true;
}

}  // namespace

bool finiteFunction(const Program &original, const Machine &, Program &out) {
    FiniteDomain domain;
    return evaluateFinite(original, domain) && emitDecision(original, domain, out);
}

bool finitePackedFunction(const Program &original, const Machine &, Program &out) {
    FiniteDomain domain;
    return evaluateFinite(original, domain) && emitPacked(original, domain, out);
}

std::vector<Program> finiteAlternatives(const Program &original, bool decision, bool packed) {
    std::vector<Program> programs;
    FiniteDomain domain;
    if ((!decision && !packed) || !evaluateFinite(original, domain)) return programs;
    Program p;
    if (decision && emitDecision(original, domain, p)) programs.push_back(std::move(p));
    if (packed && emitPacked(original, domain, p)) programs.push_back(std::move(p));
    return programs;
}

// A separate, final-only alternative: earlier six-bit candidates and seed
// trajectories are unchanged. One exhaustive evaluation is shared by all
// representations. The exact input proof and step budgets are unchanged.
std::vector<Program> finiteWideAlternatives(const Program &original) {
    std::vector<Program> programs;
    FiniteDomain domain;
    if (!evaluateFinite(original, domain, 10, 7)) return programs;
    auto emit = [&](const FiniteDomain &d) {
        Program p;
        if (emitDecision(original, d, p) && p.instrCount() <= 1024) programs.push_back(std::move(p));
        if (emitPacked(original, d, p, 64) && p.instrCount() <= 1024) programs.push_back(std::move(p));
    };
    emit(domain);
    FiniteDomain reverse;
    reverse.bits.assign(domain.bits.rbegin(), domain.bits.rend());
    reverse.table.resize(domain.table.size());
    for (size_t key = 0; key < reverse.table.size(); key++) {
        size_t old = 0;
        for (size_t b = 0; b < domain.bits.size(); b++)
            if ((key >> b) & 1u) old |= size_t{1} << (domain.bits.size() - 1 - b);
        reverse.table[key] = domain.table[old];
    }
    emit(reverse);
    return programs;
}

}  // namespace kopt
