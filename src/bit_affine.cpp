// Prove a pure bit computation affine over GF(2), then emit its exact matrix.
#include "passes.h"

#include <algorithm>
#include <array>
#include <map>
#include <vector>

namespace kopt {
namespace {

struct Bit {
    std::array<uint64_t, 2> vars{{0, 0}};
    bool one = false;
    bool constant() const { return vars[0] == 0 && vars[1] == 0; }
};
using Word = std::array<Bit, 32>;

Bit xorBit(Bit a, const Bit &b) {
    a.vars[0] ^= b.vars[0]; a.vars[1] ^= b.vars[1]; a.one ^= b.one;
    return a;
}
bool andBit(const Bit &a, const Bit &b, Bit &out) {
    if (a.constant()) { out = a.one ? b : a; return true; }
    if (b.constant()) { out = b.one ? a : b; return true; }
    if (a.vars != b.vars) return false;  // independent product is nonlinear
    out = a.one == b.one ? a : Bit{};
    return true;
}
bool orBit(const Bit &a, const Bit &b, Bit &out) {
    Bit product;
    if (!andBit(a, b, product)) return false;
    out = xorBit(xorBit(a, b), product);
    return true;
}
Word constantWord(uint32_t c) {
    Word w{};
    for (unsigned i = 0; i < 32; i++) w[i].one = ((c >> i) & 1u) != 0;
    return w;
}
bool wordConstant(const Word &w, uint32_t &c) {
    c = 0;
    for (unsigned i = 0; i < 32; i++) {
        if (!w[i].constant()) return false;
        if (w[i].one) c |= uint32_t{1} << i;
    }
    return true;
}
bool nonzero(const Word &w, Bit &out) {
    out = Bit{};
    for (const Bit &b : w) {
        Bit next;
        if (!orBit(out, b, next)) return false;
        out = next;
    }
    return true;
}
Word shift(const Word &w, unsigned amount, bool left) {
    Word out{};
    for (unsigned i = 0; i < 32; i++) {
        if (left && i >= amount) out[i] = w[i - amount];
        if (!left && i + amount < 32) out[i] = w[i + amount];
    }
    return out;
}
bool add(const Word &a, const Word &b, bool subtract, Word &out) {
    Bit carry; carry.one = subtract;
    for (unsigned i = 0; i < 32; i++) {
        Bit rhs = b[i]; rhs.one ^= subtract;
        const Bit ab = xorBit(a[i], rhs);
        out[i] = xorBit(ab, carry);
        if (i == 31) break;  // KIR discards the carry out of bit 31
        Bit t, u, next;
        if (!andBit(a[i], rhs, t) || !andBit(ab, carry, u) || !orBit(t, u, next)) return false;
        carry = next;
    }
    return true;
}

}  // namespace

bool bitAffineFunction(const Program &original, const Machine &machine, Program &out) {
    if (original.blocks.empty() || original.blocks.size() > 128 || original.params.size() > 4 ||
        original.instrCount() > 1000) return false;
    for (const Block &b : original.blocks) for (const Instr &x : b.ins)
        if (isMemOp(x.op) || x.op == OP_DIV || x.op == OP_MOD || x.op == OP_TRAP) return false;
    Func f; std::string err;
    if (!buildSSA(original, f, err)) return false;
    // Analysis-only if-conversion may spend more pure work than the real
    // machine would prefer. It establishes a straight-line expression; this
    // transformed code itself is never emitted or trusted as a timing win.
    Machine analysis = machine; analysis.taken_branch_penalty = 64;
    for (int i = 0; i < 8; i++) {
        instSimplify(f); dce(f); simplifyCFG(f);
        if (!ifConvert(f, analysis)) break;
        if (f.nvals > 4000) return false;
    }
    instSimplify(f); dce(f); simplifyCFG(f); f.resolveAll();
    if (f.nvals > 4000 || !verifyFunc(f).empty()) return false;
    const BB *block = nullptr;
    for (const BB &b : f.bb) if (b.alive) {
        if (block || !b.phis.empty() || b.term().op != OP_RET) return false;
        block = &b;
    }
    if (!block) return false;
    std::vector<Word> values(f.nvals);
    std::vector<char> ready(f.nvals, 0);
    for (size_t p = 0; p < f.params.size(); p++) {
        ready[f.params[p]] = 1;
        for (unsigned b = 0; b < 32; b++) {
            const unsigned index = static_cast<unsigned>(32 * p) + b;
            values[f.params[p]][b].vars[index / 64] = uint64_t{1} << (index % 64);
        }
    }
    auto get = [&](Opnd o, Word &w) {
        if (o.isConst) { w = constantWord(o.c); return true; }
        if (!ready[o.v]) return false;
        w = values[o.v]; return true;
    };
    Word result{};
    for (const Inst &x : block->insts) {
        Word a[3]{};
        for (int i = 0; i < x.n; i++) if (!get(x.a[i], a[i])) return false;
        if (x.op == OP_RET) { result = a[0]; break; }
        if (x.dst < 0) return false;
        Word value{};
        uint32_t constants[3] = {0, 0, 0}; bool all = true;
        for (int i = 0; i < x.n; i++) all &= wordConstant(a[i], constants[i]);
        uint32_t folded;
        if (all && foldConstant(x.op, constants[0], constants[1], constants[2], x.k, folded)) {
            value = constantWord(folded);
        } else switch (x.op) {
        case OP_CONST: case OP_MOV: value = a[0]; break;
        case OP_XOR:
            for (unsigned b = 0; b < 32; b++) value[b] = xorBit(a[0][b], a[1][b]);
            break;
        case OP_AND: case OP_OR:
            for (unsigned b = 0; b < 32; b++)
                if (!(x.op == OP_AND ? andBit(a[0][b], a[1][b], value[b])
                                    : orBit(a[0][b], a[1][b], value[b]))) return false;
            break;
        case OP_SHL: case OP_SHR: {
            unsigned count = 0;
            for (unsigned b = 0; b < 5; b++) {
                if (!a[1][b].constant()) return false;
                if (a[1][b].one) count |= 1u << b;
            }
            value = shift(a[0], count, x.op == OP_SHL); break;
        }
        case OP_ADD: case OP_SUB:
            if (!add(a[0], a[1], x.op == OP_SUB, value)) return false;
            break;
        case OP_ADDSH:
            if (!add(a[0], shift(a[1], x.k, true), false, value)) return false;
            break;
        case OP_MUL: {
            uint32_t c; int operand = 0;
            if (!wordConstant(a[1], c)) { if (!wordConstant(a[0], c)) return false; operand = 1; }
            if (!c) value = Word{};
            else {
                if ((c & (c - 1)) != 0) return false;
                unsigned count = 0; while ((uint32_t{1} << count) != c) count++;
                value = shift(a[operand], count, true);
            }
            break;
        }
        case OP_SELECT: {
            Bit condition;
            if (!nonzero(a[0], condition)) return false;
            for (unsigned b = 0; b < 32; b++) {
                Bit term;
                if (!andBit(condition, xorBit(a[1][b], a[2][b]), term)) return false;
                value[b] = xorBit(a[2][b], term);
            }
            break;
        }
        case OP_EQ: {
            Word different;
            for (unsigned b = 0; b < 32; b++) different[b] = xorBit(a[0][b], a[1][b]);
            if (!nonzero(different, value[0])) return false;
            value[0].one = !value[0].one; break;
        }
        case OP_LT: {
            uint32_t c;
            if (!wordConstant(a[1], c) || c != 0) return false;
            value[0] = a[0][31]; break;
        }
        default: return false;
        }
        values[x.dst] = value; ready[x.dst] = 1;
    }
    uint32_t bias = 0;
    std::array<uint32_t, 128> columns{};
    for (unsigned b = 0; b < 32; b++) {
        if (result[b].one) bias |= uint32_t{1} << b;
        for (unsigned i = 0; i < 32 * original.params.size(); i++)
            if ((result[b].vars[i / 64] >> (i % 64)) & 1u) columns[i] |= uint32_t{1} << b;
    }
    if (std::count_if(columns.begin(), columns.end(), [](uint32_t c) { return c != 0; }) > 32) return false;
    Program candidate; candidate.name = original.name; candidate.params = original.params;
    Block b; b.label = "affine";
    uint32_t cursor = 0;
    auto fresh = [&]() {
        while (std::find(candidate.params.begin(), candidate.params.end(), cursor) != candidate.params.end()) cursor++;
        return cursor++;
    };
    const uint32_t accumulator = fresh(), temporary = fresh();
    auto binary = [&](Op op, uint32_t dst, Operand a, Operand c) {
        Instr x; x.op = op; x.dst = dst; x.nsrc = 2; x.src[0] = a; x.src[1] = c;
        b.ins.push_back(x);
    };
    Instr initial; initial.op = OP_CONST; initial.dst = accumulator; initial.nsrc = 1;
    initial.src[0] = Operand::imm(bias); b.ins.push_back(initial);
    // Wire columns with equal displacement form one masked logical shift.
    std::map<std::pair<unsigned, int>, uint32_t> wires;
    for (unsigned i = 0; i < 32 * original.params.size(); i++) {
        const uint32_t column = columns[i];
        if (!column) continue;
        if ((column & (column - 1)) == 0) {
            unsigned output = 0; while ((uint32_t{1} << output) != column) output++;
            wires[{i / 32, static_cast<int>(output) - static_cast<int>(i % 32)}] |= uint32_t{1} << (i % 32);
            continue;
        }
        binary(OP_AND, temporary, Operand::reg(original.params[i / 32]), Operand::imm(uint32_t{1} << (i % 32)));
        Instr select; select.op = OP_SELECT; select.dst = temporary; select.nsrc = 3;
        select.src[0] = Operand::reg(temporary); select.src[1] = Operand::imm(column); select.src[2] = Operand::imm(0);
        b.ins.push_back(select);
        binary(OP_XOR, accumulator, Operand::reg(accumulator), Operand::reg(temporary));
    }
    for (const auto &wire : wires) {
        binary(OP_AND, temporary, Operand::reg(original.params[wire.first.first]), Operand::imm(wire.second));
        const int displacement = wire.first.second;
        if (displacement) binary(displacement > 0 ? OP_SHL : OP_SHR, temporary, Operand::reg(temporary),
                                 Operand::imm(static_cast<uint32_t>(displacement > 0 ? displacement : -displacement)));
        binary(OP_XOR, accumulator, Operand::reg(accumulator), Operand::reg(temporary));
    }
    Instr ret; ret.op = OP_RET; ret.nsrc = 1; ret.src[0] = Operand::reg(accumulator); b.ins.push_back(ret);
    candidate.blocks.push_back(std::move(b));
    out = std::move(candidate);
    return true;
}

}  // namespace kopt
