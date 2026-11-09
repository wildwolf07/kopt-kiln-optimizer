// sim.cpp - exact interpreter and cycle model. Mirrors kirlib.py line by line
// where it matters (slot numbering, touch order, LRU spill model, fences).
#include "sim.h"

#include <cstdlib>
#include <deque>
#include <unordered_map>

namespace kopt {

int Machine::latency(Op op) const {
    switch (op) {
    case OP_MUL: return lat_mul;
    case OP_DIV: case OP_MOD: return lat_div;
    case OP_LOAD: case OP_VLOAD: return lat_load;
    case OP_MAC: return lat_mac;
    case OP_ADDSH: return lat_addsh;
    case OP_CONST: case OP_MOV: case OP_ADD: case OP_SUB: case OP_AND: case OP_OR:
    case OP_XOR: case OP_SHL: case OP_SHR: case OP_LT: case OP_EQ: case OP_SELECT:
        return lat_alu;
    default: return 1;
    }
}

bool parseMachine(const std::string &text, Machine &m, std::string &err) {
    struct Key { const char *name; int Machine::*field; int minv; bool seen; };
    Key keys[] = {
        {"issue_width", &Machine::issue_width, 1, false},
        {"mem_ports", &Machine::mem_ports, 1, false},
        {"registers", &Machine::registers, 4, false},
        {"reg_spill_penalty", &Machine::reg_spill_penalty, 0, false},
        {"taken_branch_penalty", &Machine::taken_branch_penalty, 0, false},
        {"icache_size", &Machine::icache_size, 1, false},
        {"icache_penalty", &Machine::icache_penalty, 0, false},
        {"lat_alu", &Machine::lat_alu, 1, false},
        {"lat_mul", &Machine::lat_mul, 1, false},
        {"lat_div", &Machine::lat_div, 1, false},
        {"lat_load", &Machine::lat_load, 1, false},
        {"lat_mac", &Machine::lat_mac, 1, false},
        {"lat_addsh", &Machine::lat_addsh, 1, false},
        {"fused_mac", &Machine::fused_mac, 0, false},
        {"fused_addsh", &Machine::fused_addsh, 0, false},
    };
    size_t pos = 0;
    int lineno = 0;
    while (pos < text.size()) {
        size_t nl = text.find('\n', pos);
        if (nl == std::string::npos) nl = text.size();
        std::string line = text.substr(pos, nl - pos);
        pos = nl + 1;
        lineno++;
        size_t h = line.find('#');
        if (h != std::string::npos) line.resize(h);
        size_t a = line.find_first_not_of(" \t\r\f\v");
        if (a == std::string::npos) continue;
        size_t eq = line.find('=');
        if (eq == std::string::npos) { err = "machine line " + std::to_string(lineno) + ": expected key = value"; return false; }
        auto strip = [](std::string s) {
            size_t b = s.find_first_not_of(" \t\r\f\v");
            size_t e = s.find_last_not_of(" \t\r\f\v");
            return b == std::string::npos ? std::string() : s.substr(b, e - b + 1);
        };
        std::string key = strip(line.substr(0, eq));
        std::string val = strip(line.substr(eq + 1));
        bool found = false;
        for (Key &k : keys) {
            if (key != k.name) continue;
            found = true;
            if (val.empty() || val.find_first_not_of("0123456789") != std::string::npos || val.size() > 7) {
                err = "machine key '" + key + "' needs a non-negative integer"; return false;
            }
            long v = strtol(val.c_str(), nullptr, 10);
            if (v < k.minv || v > 1000000) { err = "machine key '" + key + "' out of range"; return false; }
            m.*(k.field) = static_cast<int>(v);
            k.seen = true;
        }
        if (!found) { err = "unknown machine key '" + key + "'"; return false; }
    }
    for (Key &k : keys) {
        if (!k.seen) { err = std::string("machine file is missing key '") + k.name + "'"; return false; }
    }
    if (m.fused_mac > 1 || m.fused_addsh > 1) { err = "fused_* must be 0 or 1"; return false; }
    return true;
}

static const uint32_t kEdgeValues[] = {0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 255, 256, 1000, 65535,
                                      0x7FFFFFFFu, 0x80000000u, 0xFFFFFFFEu, 0xFFFFFFFFu};
static const uint32_t kSpecialPairs[][2] = {
    {0x80000000u, 0xFFFFFFFFu}, {0xFFFFFFFFu, 0x80000000u}, {0x7FFFFFFFu, 0xFFFFFFFFu}, {1, 0},
    {0, 1}, {0xFFFFFFFFu, 1}, {7, 0xFFFFFFFEu}, {0xFFFFFFF9u, 2}, {7, 2}, {0x80000000u, 1},
    {0x80000000u, 2}, {0x7FFFFFFFu, 1}, {0x80000000u, 31}, {1, 32}, {1, 33}, {0xFFFFFFFFu, 31}};

std::vector<Input> generateInputs(int nparams, int count, uint64_t seed) {
    const int nEdge = sizeof(kEdgeValues) / sizeof(kEdgeValues[0]);
    const int nPairs = sizeof(kSpecialPairs) / sizeof(kSpecialPairs[0]);
    Rng rng(seed);
    std::vector<Input> out;
    for (int i = 0; i < count; i++) {
        Input in;
        if (i < nEdge) {
            in.args.assign(nparams, kEdgeValues[i]);
        } else if (i < nEdge + nPairs) {
            const uint32_t *pair = kSpecialPairs[i - nEdge];
            for (int j = 0; j < nparams; j++)
                in.args.push_back(j < 2 ? pair[j] : kEdgeValues[(i + j) % nEdge]);
        } else {
            for (int j = 0; j < nparams; j++) {
                uint64_t r = rng.below(10);
                if (r < 6) in.args.push_back(static_cast<uint32_t>(rng.below(16)));
                else if (r < 8) in.args.push_back(kEdgeValues[rng.below(nEdge)]);
                else in.args.push_back(static_cast<uint32_t>(rng.next()));
            }
        }
        uint64_t mode = rng.below(4);
        std::vector<uint32_t> words(256);
        for (int w = 0; w < 256; w++) {
            if (mode == 2) words[w] = static_cast<uint32_t>(rng.next());
            else words[w] = static_cast<uint32_t>(rng.below(mode == 0 ? 16 : mode == 1 ? 1000 : 256));
        }
        in.segments.push_back({0, words});
        for (uint32_t port = 0; port < 4; port++) {
            std::vector<uint32_t> q(16);
            for (int t = 0; t < 16; t++) q[t] = static_cast<uint32_t>(rng.below(1000));
            in.vin[port] = q;
        }
        out.push_back(std::move(in));
    }
    return out;
}

SimProgram::SimProgram(const Program &p) {
    std::unordered_map<uint32_t, int> regmap;
    auto rid = [&](uint32_t r) {
        auto it = regmap.find(r);
        if (it != regmap.end()) return it->second;
        int id = static_cast<int>(regmap.size());
        regmap.emplace(r, id);
        return id;
    };
    for (uint32_t r : p.params) rid(r);
    for (const Block &b : p.blocks)
        for (const Instr &in : b.ins) {
            if (hasDest(in.op)) rid(in.dst);
            for (int s = 0; s < in.nsrc; s++)
                if (in.src[s].isReg) rid(in.src[s].v);
        }
    nregs_ = static_cast<int>(regmap.size());
    nparams_ = static_cast<int>(p.params.size());
    std::unordered_map<uint32_t, int> consts;
    std::vector<uint32_t> constVals;
    auto slot = [&](const Operand &o) {
        if (o.isReg) return regmap.at(o.v);
        auto it = consts.find(o.v);
        if (it != consts.end()) return it->second;
        int id = nregs_ + static_cast<int>(constVals.size());
        consts.emplace(o.v, id);
        constVals.push_back(o.v);
        return id;
    };
    std::vector<uint32_t> blockStart(p.blocks.size());
    uint32_t idx = 0;
    for (size_t bi = 0; bi < p.blocks.size(); bi++) {
        blockStart[bi] = idx;
        idx += static_cast<uint32_t>(p.blocks[bi].ins.size());
    }
    for (const Block &b : p.blocks) {
        for (const Instr &in : b.ins) {
            Ins c{in.op, -1, 0, 0, 0, in.k, 0, 0};
            int s[3] = {-1, -1, -1};
            int ns = 0;
            for (int t = 0; t < in.nsrc; t++) s[ns++] = slot(in.src[t]);
            c.a = ns > 0 ? s[0] : 0;
            c.b = ns > 1 ? s[1] : 0;
            c.c = ns > 2 ? s[2] : 0;
            if (hasDest(in.op)) c.d = regmap.at(in.dst);
            if (in.op == OP_JMP) c.t1 = blockStart[in.target[0]];
            if (in.op == OP_BR) { c.t1 = blockStart[in.target[0]]; c.t2 = blockStart[in.target[1]]; }
            code_.push_back(c);
            // register slots read, in operand order
            int rs[3] = {-1, -1, -1};
            int nr = 0;
            for (int t = 0; t < ns; t++) if (s[t] < nregs_) rs[nr++] = s[t];
            for (int t = 0; t < 3; t++) srcs_.push_back(rs[t]);
            dst_.push_back(c.d);
            int tch[4] = {-1, -1, -1, -1};
            int nt = 0;
            auto addTouch = [&](int r) {
                for (int q = 0; q < nt; q++) if (tch[q] == r) return;
                tch[nt++] = r;
            };
            for (int t = 0; t < nr; t++) addTouch(rs[t]);
            if (c.d >= 0) addTouch(c.d);
            for (int t = 0; t < 4; t++) touch_.push_back(tch[t]);
        }
    }
    R0_.assign(nregs_, 0);
    R0_.insert(R0_.end(), constVals.begin(), constVals.end());
}

RunResult SimProgram::run(const Input &in, uint64_t maxSteps, bool wantTrace) const {
    RunResult res;
    std::vector<uint32_t> R = R0_;
    for (size_t i = 0; i < in.args.size() && static_cast<int>(i) < nparams_; i++) R[i] = in.args[i];
    res.mem.assign(kMemWords, 0);
    for (const auto &seg : in.segments)
        for (size_t w = 0; w < seg.second.size() && seg.first + w < kMemWords; w++)
            res.mem[seg.first + w] = seg.second[w];
    std::map<uint32_t, std::deque<uint32_t>> queues;
    for (const auto &q : in.vin) queues[q.first] = std::deque<uint32_t>(q.second.begin(), q.second.end());
    uint32_t pc = 0;
    uint64_t steps = 0;
    std::vector<uint32_t> &mem = res.mem;
    while (true) {
        if (steps >= maxSteps) { res.status = Status::TIMEOUT; break; }
        const Ins &c = code_[pc];
        steps++;
        if (wantTrace) res.trace.push_back(pc);
        switch (c.op) {
        case OP_CONST: case OP_MOV: R[c.d] = R[c.a]; pc++; break;
        case OP_ADD: R[c.d] = R[c.a] + R[c.b]; pc++; break;
        case OP_SUB: R[c.d] = R[c.a] - R[c.b]; pc++; break;
        case OP_MUL: R[c.d] = R[c.a] * R[c.b]; pc++; break;
        case OP_AND: R[c.d] = R[c.a] & R[c.b]; pc++; break;
        case OP_OR: R[c.d] = R[c.a] | R[c.b]; pc++; break;
        case OP_XOR: R[c.d] = R[c.a] ^ R[c.b]; pc++; break;
        case OP_SHL: R[c.d] = R[c.a] << (R[c.b] & 31u); pc++; break;
        case OP_SHR: R[c.d] = R[c.a] >> (R[c.b] & 31u); pc++; break;
        case OP_LT: R[c.d] = (static_cast<int32_t>(R[c.a]) < static_cast<int32_t>(R[c.b])) ? 1u : 0u; pc++; break;
        case OP_EQ: R[c.d] = (R[c.a] == R[c.b]) ? 1u : 0u; pc++; break;
        case OP_SELECT: R[c.d] = R[c.a] ? R[c.b] : R[c.c]; pc++; break;
        case OP_MAC: R[c.d] = R[c.a] * R[c.b] + R[c.c]; pc++; break;
        case OP_ADDSH: R[c.d] = R[c.a] + (R[c.b] << c.k); pc++; break;
        case OP_DIV: case OP_MOD: {
            uint32_t y = R[c.b];
            if (y == 0) { res.status = Status::TRAP; res.trap = TrapKind::DIV_BY_ZERO; goto done; }
            int64_t sx = static_cast<int32_t>(R[c.a]), sy = static_cast<int32_t>(y);
            int64_t ax = sx < 0 ? -sx : sx, ay = sy < 0 ? -sy : sy;
            if (c.op == OP_DIV) {
                int64_t q = ax / ay;
                if ((sx < 0) != (sy < 0)) q = -q;
                R[c.d] = static_cast<uint32_t>(q);
            } else {
                int64_t r = ax % ay;
                if (sx < 0) r = -r;
                R[c.d] = static_cast<uint32_t>(r);
            }
            pc++;
            break;
        }
        case OP_LOAD: {
            uint32_t addr = R[c.a];
            if (addr >= kMemWords) { res.status = Status::TRAP; res.trap = TrapKind::BAD_ADDRESS; goto done; }
            R[c.d] = mem[addr];
            pc++;
            break;
        }
        case OP_STORE: {
            uint32_t addr = R[c.a];
            if (addr >= kMemWords) { res.status = Status::TRAP; res.trap = TrapKind::BAD_ADDRESS; goto done; }
            mem[addr] = R[c.b];
            pc++;
            break;
        }
        case OP_VLOAD: {
            uint32_t port = R[c.a];
            uint32_t val = 0;
            auto it = queues.find(port);
            if (it != queues.end() && !it->second.empty()) { val = it->second.front(); it->second.pop_front(); }
            res.vlog.push_back({true, port, val});
            R[c.d] = val;
            pc++;
            break;
        }
        case OP_VSTORE: res.vlog.push_back({false, R[c.a], R[c.b]}); pc++; break;
        case OP_TRAP: res.status = Status::TRAP; res.trap = TrapKind::EXPLICIT; res.value = R[c.a]; goto done;
        case OP_JMP: pc = c.t1; break;
        case OP_BR: pc = R[c.a] ? c.t1 : c.t2; break;
        case OP_RET: res.status = Status::RET; res.value = R[c.a]; goto done;
        default: abort();
        }
    }
done:
    res.steps = steps;
    return res;
}

uint64_t SimProgram::cycles(const std::vector<uint32_t> &trace, const Machine &mc) const {
    const int W = mc.issue_width, MP = mc.mem_ports, K = mc.registers;
    const int SP = mc.reg_spill_penalty, TB = mc.taken_branch_penalty;
    const uint32_t IC = static_cast<uint32_t>(mc.icache_size);
    const int ICP = mc.icache_penalty;
    std::vector<int64_t> ready(nregs_, 0);
    const bool track = nregs_ > K;
    // LRU over resident registers: doubly linked list, head = least recent.
    std::vector<int> prv(nregs_, -1), nxt(nregs_, -1);
    std::vector<uint8_t> resident(nregs_, 0), spilled(nregs_, 0);
    int head = -1, tail = -1, nres = 0;
    auto unlink = [&](int r) {
        if (prv[r] >= 0) nxt[prv[r]] = nxt[r]; else head = nxt[r];
        if (nxt[r] >= 0) prv[nxt[r]] = prv[r]; else tail = prv[r];
        prv[r] = nxt[r] = -1;
    };
    auto pushTail = [&](int r) {
        prv[r] = tail; nxt[r] = -1;
        if (tail >= 0) nxt[tail] = r; else head = r;
        tail = r;
    };
    auto makeResident = [&](int r) {
        if (nres >= K) {
            int victim = head;
            unlink(victim);
            resident[victim] = 0;
            spilled[victim] = 1;
            nres--;
        }
        resident[r] = 1;
        pushTail(r);
        nres++;
    };
    if (track)
        for (int r = 0; r < nparams_; r++) makeResident(r);
    int64_t last = 0, fence = 0;
    int used = 0, memused = 0;
    const size_t n = trace.size();
    for (size_t idx = 0; idx < n; idx++) {
        const uint32_t pc = trace[idx];
        int64_t F = (pc >= IC) ? ICP : 0;
        const int *tch = &touch_[pc * 4];
        if (track) {
            for (int q = 0; q < 4 && tch[q] >= 0; q++) {
                int r = tch[q];
                if (resident[r]) {
                    unlink(r);
                    pushTail(r);
                } else {
                    if (spilled[r]) { F += SP; spilled[r] = 0; }
                    makeResident(r);
                }
            }
        }
        int64_t t = last + F;
        if (fence > t) t = fence;
        const int *rs = &srcs_[pc * 3];
        for (int q = 0; q < 3; q++)
            if (rs[q] >= 0 && ready[rs[q]] > t) t = ready[rs[q]];
        const int d = dst_[pc];
        if (d >= 0 && ready[d] > t) t = ready[d];
        const Op op = code_[pc].op;
        const bool m = isMemOp(op);
        if (t == last && (used >= W || (m && memused >= MP))) t += 1;
        if (t > last) { used = 0; memused = 0; }
        used++;
        if (m) memused++;
        last = t;
        if (d >= 0) ready[d] = t + mc.latency(op);
        if (isTerminator(op) && idx + 1 < n && trace[idx + 1] != pc + 1) fence = t + 1 + TB;
    }
    return static_cast<uint64_t>(last + 1);
}

SimProgram::Breakdown SimProgram::breakdown(const std::vector<uint32_t> &trace, const Machine &mc) const {
    // Same model as cycles(), with counters. Kept separate so cycles() stays lean.
    Breakdown bd;
    const int W = mc.issue_width, MP = mc.mem_ports, K = mc.registers;
    const int SP = mc.reg_spill_penalty, TB = mc.taken_branch_penalty;
    const uint32_t IC = static_cast<uint32_t>(mc.icache_size);
    const int ICP = mc.icache_penalty;
    std::vector<int64_t> ready(nregs_, 0);
    const bool track = nregs_ > K;
    std::vector<uint64_t> lastUse(nregs_, 0);
    std::vector<uint8_t> resident(nregs_, 0), spilled(nregs_, 0);
    uint64_t tick = 0;
    int nres = 0;
    auto makeResident = [&](int r) {
        if (nres >= K) {
            int victim = -1;
            for (int q = 0; q < nregs_; q++)
                if (resident[q] && (victim < 0 || lastUse[q] < lastUse[victim])) victim = q;
            resident[victim] = 0;
            spilled[victim] = 1;
            nres--;
        }
        resident[r] = 1;
        lastUse[r] = ++tick;
        nres++;
    };
    if (track)
        for (int r = 0; r < nparams_; r++) makeResident(r);
    int64_t last = 0, fence = 0;
    int used = 0, memused = 0;
    for (size_t idx = 0; idx < trace.size(); idx++) {
        const uint32_t pc = trace[idx];
        bd.instrs++;
        int64_t F = 0;
        if (pc >= IC) { F += ICP; bd.icacheMisses++; }
        const int *tch = &touch_[pc * 4];
        if (track)
            for (int q = 0; q < 4 && tch[q] >= 0; q++) {
                int r = tch[q];
                if (resident[r]) lastUse[r] = ++tick;
                else {
                    if (spilled[r]) { F += SP; spilled[r] = 0; bd.spillTouches++; }
                    makeResident(r);
                }
            }
        int64_t t = last + F;
        int64_t tf = std::max(t, fence);
        if (tf > t) bd.fenceStall += static_cast<uint64_t>(tf - t);
        t = tf;
        int64_t td = t;
        const int *rs = &srcs_[pc * 3];
        for (int q = 0; q < 3; q++) if (rs[q] >= 0 && ready[rs[q]] > td) td = ready[rs[q]];
        const int d = dst_[pc];
        if (d >= 0 && ready[d] > td) td = ready[d];
        if (td > t) bd.dataStall += static_cast<uint64_t>(td - t);
        t = td;
        const Op op = code_[pc].op;
        const bool m = isMemOp(op);
        if (t == last && (used >= W || (m && memused >= MP))) { t += 1; bd.slotStall++; }
        if (t > last) { used = 0; memused = 0; }
        used++;
        if (m) memused++;
        last = t;
        if (d >= 0) ready[d] = t + mc.latency(op);
        if (isTerminator(op) && idx + 1 < trace.size() && trace[idx + 1] != pc + 1) {
            fence = t + 1 + TB;
            bd.takenJumps++;
        }
    }
    return bd;
}

std::string compareRuns(const RunResult &a, const RunResult &b) {
    if (a.status != b.status) return "status differs";
    if (a.status == Status::RET && a.value != b.value) return "return value differs";
    if (a.status == Status::TRAP) {
        if (a.trap != b.trap) return "trap kind differs";
        if (a.trap == TrapKind::EXPLICIT && a.value != b.value) return "trap code differs";
    }
    if (a.vlog.size() != b.vlog.size()) return "volatile log length differs";
    for (size_t i = 0; i < a.vlog.size(); i++)
        if (!(a.vlog[i] == b.vlog[i])) return "volatile log differs at entry " + std::to_string(i);
    for (uint32_t i = 0; i < kScratchBase; i++)
        if (a.mem[i] != b.mem[i]) return "memory differs at address " + std::to_string(i);
    return std::string();
}

}  // namespace kopt
