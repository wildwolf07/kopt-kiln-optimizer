// kir.h - the KIR program representation used for input and output.
//
// A Program is the textual program: named blocks in layout order, each a list
// of instructions ending in exactly one terminator. Registers keep their
// original numbers here; the optimizer works on its own SSA form (ssa.h) and
// converts back to a Program at the end.
#pragma once

#include <cstdint>
#include <string>
#include <vector>

namespace kopt {

enum Op : uint8_t {
    OP_CONST, OP_MOV, OP_ADD, OP_SUB, OP_MUL, OP_AND, OP_OR, OP_XOR,
    OP_SHL, OP_SHR, OP_LT, OP_EQ, OP_SELECT, OP_DIV, OP_MOD, OP_MAC,
    OP_ADDSH, OP_LOAD, OP_STORE, OP_VLOAD, OP_VSTORE,
    OP_TRAP, OP_JMP, OP_BR, OP_RET,
    OP_COUNT
};

const char *opName(Op op);
bool opFromName(const std::string &name, Op &out);

inline bool isTerminator(Op op) { return op == OP_TRAP || op == OP_JMP || op == OP_BR || op == OP_RET; }
inline bool isMemOp(Op op) { return op == OP_LOAD || op == OP_STORE || op == OP_VLOAD || op == OP_VSTORE; }
// Instructions that write a destination register.
inline bool hasDest(Op op) {
    return !(op == OP_STORE || op == OP_VSTORE || isTerminator(op));
}

// An operand: a register (v<num>) or a 32-bit literal.
struct Operand {
    bool isReg = false;
    uint32_t v = 0;  // register number, or literal value (mod 2^32)
    static Operand reg(uint32_t r) { Operand o; o.isReg = true; o.v = r; return o; }
    static Operand imm(uint32_t c) { Operand o; o.isReg = false; o.v = c; return o; }
    bool operator==(const Operand &o) const { return isReg == o.isReg && v == o.v; }
    bool operator!=(const Operand &o) const { return !(*this == o); }
};

// One textual instruction. Field use by opcode:
//   dst          : destination register (if hasDest)
//   src[0..2]    : source operands in textual order (store: addr, value; br: cond)
//   nsrc         : number of source operands
//   k            : addsh shift literal
//   target[0..1] : block indices for jmp (target[0]) and br (true, false)
struct Instr {
    Op op = OP_RET;
    uint32_t dst = 0;
    Operand src[3];
    int nsrc = 0;
    int k = 0;
    int target[2] = {-1, -1};
};

struct Block {
    std::string label;
    std::vector<Instr> ins;
};

struct Program {
    std::string name;
    std::vector<uint32_t> params;   // register numbers, in header order
    std::vector<Block> blocks;      // layout order; blocks[0] is the entry
    size_t instrCount() const;
};

// Parse KIR text. On error, returns false and fills err with "line N: message".
bool parseProgram(const std::string &text, Program &out, std::string &err);

// Print a program as KIR text that the official tools accept.
std::string printProgram(const Program &p);

}  // namespace kopt
