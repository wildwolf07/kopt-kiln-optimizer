// kir.cpp - KIR parser and printer. Accepts exactly the syntax of KIR_SPEC.md
// sections 2 and 5 (the kit's kirlib.py is the reference behaviour).
#include "kir.h"

#include <cstring>
#include <unordered_map>

namespace kopt {

static const char *const kOpNames[OP_COUNT] = {
    "const", "mov", "add", "sub", "mul", "and", "or", "xor",
    "shl", "shr", "lt", "eq", "select", "div", "mod", "mac",
    "addsh", "load", "store", "vload", "vstore",
    "trap", "jmp", "br", "ret",
};

// Operand signature per opcode: d = dest reg, s = reg or literal,
// i = literal, k = shift literal 0..31, L = label.
static const char *const kSigs[OP_COUNT] = {
    "di", "ds", "dss", "dss", "dss", "dss", "dss", "dss",
    "dss", "dss", "dss", "dss", "dsss", "dss", "dss", "dsss",
    "dssk", "ds", "ss", "ds", "ss",
    "s", "L", "sLL", "s",
};

const char *opName(Op op) { return kOpNames[op]; }

bool opFromName(const std::string &name, Op &out) {
    for (int i = 0; i < OP_COUNT; i++) {
        if (name == kOpNames[i]) { out = static_cast<Op>(i); return true; }
    }
    return false;
}

size_t Program::instrCount() const {
    size_t n = 0;
    for (const Block &b : blocks) n += b.ins.size();
    return n;
}

namespace {

std::string trim(const std::string &s) {
    size_t a = 0, b = s.size();
    while (a < b && (s[a] == ' ' || s[a] == '\t' || s[a] == '\r' || s[a] == '\n' || s[a] == '\f' || s[a] == '\v')) a++;
    while (b > a && (s[b - 1] == ' ' || s[b - 1] == '\t' || s[b - 1] == '\r' || s[b - 1] == '\n' || s[b - 1] == '\f' || s[b - 1] == '\v')) b--;
    return s.substr(a, b - a);
}

bool isIdentStart(char c) { return (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || c == '_'; }
bool isIdentChar(char c) { return isIdentStart(c) || (c >= '0' && c <= '9'); }

bool isName(const std::string &s) {
    if (s.empty() || !isIdentStart(s[0])) return false;
    for (char c : s) if (!isIdentChar(c)) return false;
    return true;
}

// v0 | v[1-9][0-9]{0,5}
bool parseReg(const std::string &s, uint32_t &r) {
    if (s.size() < 2 || s.size() > 7 || s[0] != 'v') return false;
    if (s.size() > 2 && s[1] == '0') return false;
    uint32_t v = 0;
    for (size_t i = 1; i < s.size(); i++) {
        if (s[i] < '0' || s[i] > '9') return false;
        v = v * 10 + static_cast<uint32_t>(s[i] - '0');
    }
    r = v;
    return true;
}

// -?(0x[0-9a-fA-F]+|[0-9]+), value in [-2^31, 2^32-1]; stored mod 2^32.
bool parseLit(const std::string &s, int64_t &val) {
    size_t i = 0;
    bool neg = false;
    if (i < s.size() && s[i] == '-') { neg = true; i++; }
    if (i >= s.size()) return false;
    __int128 n = 0;
    if (s.size() - i > 2 && s[i] == '0' && s[i + 1] == 'x') {
        i += 2;
        for (; i < s.size(); i++) {
            char c = s[i];
            int d;
            if (c >= '0' && c <= '9') d = c - '0';
            else if (c >= 'a' && c <= 'f') d = c - 'a' + 10;
            else if (c >= 'A' && c <= 'F') d = c - 'A' + 10;
            else return false;
            n = n * 16 + d;
            if (n > ((__int128)1 << 40)) return false;
        }
    } else {
        for (; i < s.size(); i++) {
            char c = s[i];
            if (c < '0' || c > '9') return false;
            n = n * 10 + (c - '0');
            if (n > ((__int128)1 << 40)) return false;
        }
    }
    if (neg) n = -n;
    if (n < -((__int128)1 << 31) || n > (((__int128)1 << 32) - 1)) return false;
    val = static_cast<int64_t>(n);
    return true;
}

std::string decodeText(const std::string &raw) {
    // UTF-8 BOM
    if (raw.size() >= 3 && (unsigned char)raw[0] == 0xEF && (unsigned char)raw[1] == 0xBB && (unsigned char)raw[2] == 0xBF)
        return raw.substr(3);
    // UTF-16 with BOM (Windows PowerShell '>'): keep ASCII only, which is all KIR uses.
    if (raw.size() >= 2) {
        unsigned char a = raw[0], b = raw[1];
        bool le = (a == 0xFF && b == 0xFE), be = (a == 0xFE && b == 0xFF);
        if (le || be) {
            std::string out;
            for (size_t i = 2; i + 1 < raw.size(); i += 2) {
                unsigned lo = (unsigned char)raw[le ? i : i + 1];
                unsigned hi = (unsigned char)raw[le ? i + 1 : i];
                unsigned cp = lo | (hi << 8);
                out.push_back(cp < 128 ? static_cast<char>(cp) : '?');
            }
            return out;
        }
    }
    return raw;
}

}  // namespace

bool parseProgram(const std::string &rawText, Program &out, std::string &err) {
    const std::string text = decodeText(rawText);
    out = Program();
    bool seenFunc = false;
    std::unordered_map<std::string, int> labelIndex;
    struct PendingTarget { int block, instr, slot; std::string label; int line; };
    std::vector<PendingTarget> pending;

    auto fail = [&](int line, const std::string &msg) {
        err = "line " + std::to_string(line) + ": " + msg;
        return false;
    };
    std::vector<std::string> lines;
    {
        size_t pos = 0;
        while (pos < text.size()) {
            size_t nl = text.find('\n', pos);
            if (nl == std::string::npos) nl = text.size();
            lines.push_back(text.substr(pos, nl - pos));
            pos = nl + 1;
        }
    }
    for (size_t li = 0; li < lines.size(); li++) {
        const int lineno = static_cast<int>(li) + 1;
        std::string raw = lines[li];
        size_t sc = raw.find(';');
        if (sc != std::string::npos) raw.resize(sc);
        std::string line = trim(raw);
        if (line.empty()) continue;
        if (line.compare(0, 4, "func") == 0 && line.size() > 4 && (line[4] == ' ' || line[4] == '\t')) {
            if (seenFunc) return fail(lineno, "only one 'func' header is allowed");
            if (!out.blocks.empty()) return fail(lineno, "'func' header must come before the first label");
            size_t lp = line.find('(');
            if (lp == std::string::npos || line.back() != ')') return fail(lineno, "bad func header");
            std::string name = trim(line.substr(4, lp - 4));
            if (!isName(name)) return fail(lineno, "bad function name");
            std::string plist = trim(line.substr(lp + 1, line.size() - lp - 2));
            out.name = name;
            if (!plist.empty()) {
                size_t p = 0;
                while (true) {
                    size_t c = plist.find(',', p);
                    std::string tok = trim(plist.substr(p, c == std::string::npos ? std::string::npos : c - p));
                    uint32_t r;
                    if (!parseReg(tok, r)) return fail(lineno, "parameter '" + tok + "' is not a register");
                    for (uint32_t q : out.params) if (q == r) return fail(lineno, "parameter listed twice");
                    out.params.push_back(r);
                    if (c == std::string::npos) break;
                    p = c + 1;
                }
            }
            if (out.params.size() > 8) return fail(lineno, "at most 8 parameters are allowed");
            seenFunc = true;
            continue;
        }
        if (!seenFunc) return fail(lineno, "expected 'func name(params)' as the first statement");
        if (line.back() == ':') {
            std::string name = line.substr(0, line.size() - 1);
            uint32_t dummy;
            if (!isName(name)) return fail(lineno, "bad label");
            if (parseReg(name, dummy)) return fail(lineno, "label looks like a register");
            if (labelIndex.count(name)) return fail(lineno, "label defined twice");
            labelIndex[name] = static_cast<int>(out.blocks.size());
            out.blocks.push_back(Block{name, {}});
            continue;
        }
        // instruction
        size_t sp = 0;
        while (sp < line.size() && line[sp] != ' ' && line[sp] != '\t') sp++;
        std::string opname = line.substr(0, sp);
        std::string rest = trim(line.substr(sp));
        Op op;
        if (!opFromName(opname, op)) return fail(lineno, "unknown instruction '" + opname + "'");
        if (out.blocks.empty()) return fail(lineno, "instruction outside of a block");
        std::vector<std::string> toks;
        if (!rest.empty()) {
            size_t p = 0;
            while (true) {
                size_t c = rest.find(',', p);
                toks.push_back(trim(rest.substr(p, c == std::string::npos ? std::string::npos : c - p)));
                if (c == std::string::npos) break;
                p = c + 1;
            }
        }
        const char *sig = kSigs[op];
        if (toks.size() != strlen(sig)) return fail(lineno, "wrong number of operands");
        Instr ins;
        ins.op = op;
        Block &blk = out.blocks.back();
        for (size_t t = 0; t < toks.size(); t++) {
            const std::string &tok = toks[t];
            if (tok.empty()) return fail(lineno, "empty operand");
            char kind = sig[t];
            uint32_t r;
            int64_t lit;
            switch (kind) {
            case 'd':
                if (!parseReg(tok, r)) return fail(lineno, "expected a register");
                ins.dst = r;
                break;
            case 's':
                if (parseReg(tok, r)) ins.src[ins.nsrc++] = Operand::reg(r);
                else if (parseLit(tok, lit)) ins.src[ins.nsrc++] = Operand::imm(static_cast<uint32_t>(lit));
                else return fail(lineno, "expected a register or literal");
                break;
            case 'i':
                if (!parseLit(tok, lit)) return fail(lineno, "expected a literal");
                ins.src[ins.nsrc++] = Operand::imm(static_cast<uint32_t>(lit));
                break;
            case 'k':
                if (!parseLit(tok, lit) || lit < 0 || lit > 31) return fail(lineno, "bad addsh shift");
                ins.k = static_cast<int>(lit);
                break;
            case 'L': {
                if (!isName(tok) || parseReg(tok, r)) return fail(lineno, "expected a label");
                int slot = (op == OP_BR) ? static_cast<int>(t) - 1 : 0;
                pending.push_back({static_cast<int>(out.blocks.size()) - 1, static_cast<int>(blk.ins.size()), slot, tok, lineno});
                break;
            }
            default:
                return fail(lineno, "internal: bad signature");
            }
        }
        if (!blk.ins.empty() && isTerminator(blk.ins.back().op))
            return fail(lineno, "instruction after a terminator");
        blk.ins.push_back(ins);
    }
    if (!seenFunc) { err = "missing 'func name(params)' header"; return false; }
    if (out.blocks.empty()) { err = "the function has no blocks"; return false; }
    for (const Block &b : out.blocks) {
        if (b.ins.empty()) { err = "block '" + b.label + "' is empty"; return false; }
        if (!isTerminator(b.ins.back().op)) { err = "block '" + b.label + "' must end with a terminator"; return false; }
    }
    for (const PendingTarget &pt : pending) {
        auto it = labelIndex.find(pt.label);
        if (it == labelIndex.end()) return fail(pt.line, "jump to undefined label '" + pt.label + "'");
        out.blocks[pt.block].ins[pt.instr].target[pt.slot] = it->second;
    }
    return true;
}

static void appendOperand(std::string &s, const Operand &o) {
    if (o.isReg) {
        s += 'v';
        s += std::to_string(o.v);
    } else if (o.v >= 0x80000000u) {
        s += std::to_string(static_cast<int64_t>(o.v) - (int64_t(1) << 32));
    } else {
        s += std::to_string(o.v);
    }
}

std::string printProgram(const Program &p) {
    std::string s;
    s.reserve(p.instrCount() * 24 + 64);
    s += "func ";
    s += p.name;
    s += '(';
    for (size_t i = 0; i < p.params.size(); i++) {
        if (i) s += ", ";
        s += 'v';
        s += std::to_string(p.params[i]);
    }
    s += ")\n";
    for (const Block &b : p.blocks) {
        s += b.label;
        s += ":\n";
        for (const Instr &in : b.ins) {
            s += "  ";
            s += opName(in.op);
            const char *sig = kSigs[in.op];
            int si = 0;
            for (size_t t = 0; sig[t]; t++) {
                s += (t == 0) ? " " : ", ";
                switch (sig[t]) {
                case 'd': s += 'v'; s += std::to_string(in.dst); break;
                case 's':
                case 'i': appendOperand(s, in.src[si++]); break;
                case 'k': s += std::to_string(in.k); break;
                case 'L': {
                    int slot = (in.op == OP_BR) ? static_cast<int>(t) - 1 : 0;
                    s += p.blocks[in.target[slot]].label;
                    break;
                }
                }
            }
            s += '\n';
        }
    }
    return s;
}

}  // namespace kopt
