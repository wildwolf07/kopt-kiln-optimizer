// passes.cpp - machine-independent SSA optimizations.
#include "passes.h"

#include <algorithm>
#include <unordered_map>

#include "cfg.h"

namespace kopt {

// ---------------------------------------------------------------------------
// Small helpers
// ---------------------------------------------------------------------------

namespace {

struct DefSite {
    int block = -1;
    int idx = -1;       // instruction index, or -1 for phis/params
    bool isPhi = false;
};

// Where each value is defined. Rebuilt whenever the instruction lists change.
std::vector<DefSite> defSites(const Func &f) {
    std::vector<DefSite> d(f.nvals);
    for (int b = 0; b < static_cast<int>(f.bb.size()); b++) {
        const BB &B = f.bb[b];
        if (!B.alive) continue;
        for (const Phi &p : B.phis) d[p.dst] = DefSite{b, -1, true};
        for (int i = 0; i < static_cast<int>(B.insts.size()); i++)
            if (B.insts[i].dst >= 0) d[B.insts[i].dst] = DefSite{b, i, false};
    }
    return d;
}

const Inst *defInst(const Func &f, const std::vector<DefSite> &ds, Opnd o) {
    if (o.isConst) return nullptr;
    const DefSite &d = ds[o.v];
    if (d.block < 0 || d.isPhi || d.idx < 0) return nullptr;
    const BB &B = f.bb[d.block];
    if (d.idx >= static_cast<int>(B.insts.size())) return nullptr;
    const Inst &x = B.insts[d.idx];
    return x.dst == o.v ? &x : nullptr;
}

inline bool isCommutative(Op op) {
    return op == OP_ADD || op == OP_MUL || op == OP_AND || op == OP_OR || op == OP_XOR || op == OP_EQ;
}

inline bool isPure(Op op) {
    switch (op) {
    case OP_MOV: case OP_ADD: case OP_SUB: case OP_MUL: case OP_AND: case OP_OR: case OP_XOR:
    case OP_SHL: case OP_SHR: case OP_LT: case OP_EQ: case OP_SELECT: case OP_MAC: case OP_ADDSH:
        return true;
    default:
        return false;
    }
}

}  // namespace

bool foldConstant(Op op, uint32_t a, uint32_t b, uint32_t c, int k, uint32_t &out) {
    switch (op) {
    case OP_CONST: case OP_MOV: out = a; return true;
    case OP_ADD: out = a + b; return true;
    case OP_SUB: out = a - b; return true;
    case OP_MUL: out = a * b; return true;
    case OP_AND: out = a & b; return true;
    case OP_OR: out = a | b; return true;
    case OP_XOR: out = a ^ b; return true;
    case OP_SHL: out = a << (b & 31u); return true;
    case OP_SHR: out = a >> (b & 31u); return true;
    case OP_LT: out = (static_cast<int32_t>(a) < static_cast<int32_t>(b)) ? 1u : 0u; return true;
    case OP_EQ: out = (a == b) ? 1u : 0u; return true;
    case OP_SELECT: out = a ? b : c; return true;
    case OP_MAC: out = a * b + c; return true;
    case OP_ADDSH: out = a + (b << k); return true;
    case OP_DIV: case OP_MOD: {
        if (b == 0) return false;
        int64_t sx = static_cast<int32_t>(a), sy = static_cast<int32_t>(b);
        int64_t ax = sx < 0 ? -sx : sx, ay = sy < 0 ? -sy : sy;
        if (op == OP_DIV) {
            int64_t q = ax / ay;
            if ((sx < 0) != (sy < 0)) q = -q;
            out = static_cast<uint32_t>(q);
        } else {
            int64_t r = ax % ay;
            if (sx < 0) r = -r;
            out = static_cast<uint32_t>(r);
        }
        return true;
    }
    default:
        return false;
    }
}

// ---------------------------------------------------------------------------
// Unsigned value ranges (cheap, recursive, depth-limited). Used to prove that
// addresses are in memory and divisors are non-zero.
// ---------------------------------------------------------------------------

namespace {

struct Range {
    uint64_t lo = 0, hi = 0xFFFFFFFFull;
    bool full() const { return lo == 0 && hi == 0xFFFFFFFFull; }
};

uint64_t maskUpTo(uint64_t v) {
    uint64_t m = 0;
    while (m < v) m = (m << 1) | 1;
    return m;
}

Range rangeOf(const Func &f, const std::vector<DefSite> &ds, Opnd o, int depth) {
    Range full;
    if (o.isConst) return Range{o.c, o.c};
    if (depth <= 0) return full;
    const Inst *x = defInst(f, ds, o);
    if (!x) {
        const DefSite &d = ds[o.v];
        if (d.isPhi && d.block >= 0 && depth > 2) {
            const BB &B = f.bb[d.block];
            for (const Phi &p : B.phis) {
                if (p.dst != o.v) continue;
                Range r{0xFFFFFFFFull, 0};
                for (auto &in : p.in) {
                    if (!in.second.isConst && in.second.v == o.v) continue;
                    Range s = rangeOf(f, ds, in.second, depth - 2);
                    r.lo = std::min(r.lo, s.lo);
                    r.hi = std::max(r.hi, s.hi);
                }
                if (r.lo > r.hi) return full;
                return r;
            }
        }
        return full;
    }
    auto R = [&](int i) { return rangeOf(f, ds, x->a[i], depth - 1); };
    switch (x->op) {
    case OP_MOV: return R(0);
    case OP_AND: {
        Range a = R(0), b = R(1);
        return Range{0, std::min(a.hi, b.hi)};
    }
    case OP_OR: case OP_XOR: {
        Range a = R(0), b = R(1);
        return Range{0, maskUpTo(std::max(a.hi, b.hi))};
    }
    case OP_SHR: {
        Range a = R(0);
        if (x->a[1].isConst) {
            int s = x->a[1].c & 31;
            return Range{a.lo >> s, a.hi >> s};
        }
        return Range{0, a.hi};
    }
    case OP_SHL: {
        Range a = R(0);
        if (x->a[1].isConst) {
            int s = x->a[1].c & 31;
            if ((a.hi << s) <= 0xFFFFFFFFull) return Range{a.lo << s, a.hi << s};
        }
        return full;
    }
    case OP_ADD: {
        Range a = R(0), b = R(1);
        if (a.hi + b.hi <= 0xFFFFFFFFull) return Range{a.lo + b.lo, a.hi + b.hi};
        return full;
    }
    case OP_ADDSH: {
        Range a = R(0), b = R(1);
        uint64_t bh = b.hi << x->k, bl = b.lo << x->k;
        if (bh <= 0xFFFFFFFFull && a.hi + bh <= 0xFFFFFFFFull) return Range{a.lo + bl, a.hi + bh};
        return full;
    }
    case OP_SUB: {
        Range a = R(0), b = R(1);
        if (a.lo >= b.hi) return Range{a.lo - b.hi, a.hi - b.lo};
        return full;
    }
    case OP_MUL: {
        Range a = R(0), b = R(1);
        if (a.hi == 0 || b.hi == 0) return Range{0, 0};
        if (a.hi <= 0xFFFFFFFFull / b.hi) return Range{a.lo * b.lo, a.hi * b.hi};
        return full;
    }
    case OP_MAC: {
        Range a = R(0), b = R(1), c = R(2);
        if (a.hi == 0 || b.hi == 0) return c;
        if (a.hi <= 0xFFFFFFFFull / b.hi) {
            uint64_t ph = a.hi * b.hi;
            if (ph + c.hi <= 0xFFFFFFFFull) return Range{a.lo * b.lo + c.lo, ph + c.hi};
        }
        return full;
    }
    case OP_LT: case OP_EQ: return Range{0, 1};
    case OP_SELECT: {
        Range a = R(1), b = R(2);
        return Range{std::min(a.lo, b.lo), std::max(a.hi, b.hi)};
    }
    case OP_MOD: {
        Range a = R(0), b = R(1);
        // Non-negative dividend and positive divisor: result in [0, min(a, b-1)].
        if (a.hi < 0x80000000ull && b.lo >= 1 && b.hi < 0x80000000ull) return Range{0, std::min(a.hi, b.hi - 1)};
        return full;
    }
    case OP_DIV: {
        Range a = R(0), b = R(1);
        if (a.hi < 0x80000000ull && b.lo >= 1 && b.hi < 0x80000000ull) return Range{a.lo / b.hi, a.hi / b.lo};
        return full;
    }
    default:
        return full;
    }
}

}  // namespace

bool addressInRange(Func &f, Opnd addr) {
    addr = f.resolve(addr);
    if (addr.isConst) return addr.c < kMemWords;
    std::vector<DefSite> ds = defSites(f);
    return rangeOf(f, ds, addr, 8).hi < kMemWords;
}

static bool mayTrapWith(const Func &f, const std::vector<DefSite> &ds, const Inst &x) {
    switch (x.op) {
    case OP_DIV: case OP_MOD:
        return rangeOf(f, ds, x.a[1], 8).lo == 0;
    case OP_LOAD: case OP_STORE:
        return rangeOf(f, ds, x.a[0], 8).hi >= kMemWords;
    case OP_TRAP:
        return true;
    default:
        return false;
    }
}

bool mayTrap(Func &f, const Inst &x) {
    std::vector<DefSite> ds = defSites(f);
    return mayTrapWith(f, ds, x);
}

// ---------------------------------------------------------------------------
// CFG simplification
// ---------------------------------------------------------------------------

static void removeUnreachable(Func &f) {
    f.rebuildPreds();
    DomInfo d = computeDominators(f);
    bool any = false;
    for (int b = 0; b < static_cast<int>(f.bb.size()); b++)
        if (f.bb[b].alive && !d.reachable(b)) { f.bb[b].alive = false; any = true; }
    if (any) f.rebuildPreds();
}

bool simplifyCFG(Func &f) {
    bool changed = false;
    for (int round = 0; round < 50; round++) {
        bool again = false;
        f.resolveAll();
        // Constant branches and branches with equal targets become jumps.
        for (BB &B : f.bb) {
            if (!B.alive) continue;
            Inst &t = B.term();
            if (t.op != OP_BR) continue;
            if (t.a[0].isConst || t.tgt[0] == t.tgt[1]) {
                int target = t.a[0].isConst ? (t.a[0].c ? t.tgt[0] : t.tgt[1]) : t.tgt[0];
                t.op = OP_JMP;
                t.n = 0;
                t.tgt[0] = target;
                t.tgt[1] = -1;
                again = true;
            }
        }
        removeUnreachable(f);
        // Merge a block into its only predecessor when that predecessor jumps to it.
        for (int b = 0; b < static_cast<int>(f.bb.size()); b++) {
            if (!f.bb[b].alive) continue;
            while (true) {
                BB &B = f.bb[b];
                Inst &t = B.term();
                if (t.op != OP_JMP) break;
                int s = t.tgt[0];
                if (s == b || s == 0) break;
                BB &S = f.bb[s];
                if (S.preds.size() != 1 || S.preds[0] != b) break;
                for (Phi &p : S.phis) f.replaceAll(p.dst, p.in.empty() ? Opnd::cst(0) : p.in[0].second);
                S.phis.clear();
                B.insts.pop_back();
                for (Inst &x : S.insts) B.insts.push_back(x);
                S.insts.clear();
                S.alive = false;
                if (B.label.empty()) B.label = S.label;
                int ss[2];
                int ns = f.succs(b, ss);
                for (int i = 0; i < ns; i++) {
                    for (Phi &p : f.bb[ss[i]].phis)
                        for (auto &in : p.in) if (in.first == s) in.first = b;
                    for (int &pp : f.bb[ss[i]].preds) if (pp == s) pp = b;
                }
                again = true;
            }
        }
        f.rebuildPreds();
        // Thread jumps through empty blocks.
        for (int e = 1; e < static_cast<int>(f.bb.size()); e++) {
            BB &E = f.bb[e];
            if (!E.alive || !E.phis.empty() || E.insts.size() != 1 || E.term().op != OP_JMP) continue;
            int t = E.term().tgt[0];
            if (t == e) continue;
            std::vector<int> preds = E.preds;
            for (int p : preds) {
                BB &P = f.bb[p];
                BB &T = f.bb[t];
                bool pAlreadyPred = std::find(T.preds.begin(), T.preds.end(), p) != T.preds.end();
                if (pAlreadyPred && !T.phis.empty()) continue;
                Inst &pt = P.term();
                for (int k = 0; k < 2; k++)
                    if ((pt.op == OP_JMP && k == 0) || pt.op == OP_BR)
                        if (pt.tgt[k] == e) pt.tgt[k] = t;
                if (!pAlreadyPred) {
                    for (Phi &ph : T.phis) {
                        Opnd v = Opnd::cst(0);
                        for (auto &in : ph.in) if (in.first == e) v = in.second;
                        ph.in.push_back({p, v});
                    }
                }
                f.rebuildPreds();
                again = true;
            }
        }
        if (again) {
            changed = true;
            removeUnreachable(f);
        } else {
            break;
        }
    }
    return changed;
}

// ---------------------------------------------------------------------------
// Sparse conditional constant propagation (Wegman and Zadeck)
// ---------------------------------------------------------------------------

bool sccp(Func &f) {
    f.resolveAll();
    enum : uint8_t { TOP = 0, CONSTV = 1, BOT = 2 };
    const int nv = f.nvals;
    const int nb = static_cast<int>(f.bb.size());
    std::vector<uint8_t> st(nv, TOP);
    std::vector<uint32_t> cv(nv, 0);
    for (Val p : f.params) st[p] = BOT;
    // Users of each value: (block, index); index -1-k means phi k.
    std::vector<std::vector<std::pair<int, int>>> users(nv);
    for (int b = 0; b < nb; b++) {
        BB &B = f.bb[b];
        if (!B.alive) continue;
        for (int k = 0; k < static_cast<int>(B.phis.size()); k++)
            for (auto &in : B.phis[k].in)
                if (!in.second.isConst) users[in.second.v].push_back({b, -1 - k});
        for (int i = 0; i < static_cast<int>(B.insts.size()); i++)
            for (int a = 0; a < B.insts[i].n; a++)
                if (!B.insts[i].a[a].isConst) users[B.insts[i].a[a].v].push_back({b, i});
    }
    std::vector<char> blockExec(nb, 0);
    std::vector<std::pair<int, int>> execEdges;   // (from, to)
    auto edgeExec = [&](int from, int to) {
        for (auto &e : execEdges) if (e.first == from && e.second == to) return true;
        return false;
    };
    std::vector<std::pair<int, int>> flowWork;
    std::vector<std::pair<int, int>> ssaWork;     // (block, idx)
    auto lat = [&](Opnd o, uint8_t &s, uint32_t &c) {
        if (o.isConst) { s = CONSTV; c = o.c; return; }
        s = st[o.v];
        c = cv[o.v];
    };
    auto setVal = [&](Val v, uint8_t s, uint32_t c) {
        if (st[v] == BOT) return;
        if (s == st[v] && (s != CONSTV || c == cv[v])) return;
        if (st[v] == CONSTV && s == CONSTV && c != cv[v]) s = BOT;
        if (s < st[v]) return;   // monotone
        st[v] = s;
        cv[v] = c;
        for (auto &u : users[v]) ssaWork.push_back(u);
    };
    auto evalPhi = [&](int b, int k) {
        Phi &p = f.bb[b].phis[k];
        uint8_t s = TOP;
        uint32_t c = 0;
        for (auto &in : p.in) {
            if (!edgeExec(in.first, b)) continue;
            uint8_t is;
            uint32_t ic;
            lat(in.second, is, ic);
            if (is == TOP) continue;
            if (is == BOT) { s = BOT; break; }
            if (s == TOP) { s = CONSTV; c = ic; }
            else if (c != ic) { s = BOT; break; }
        }
        setVal(p.dst, s, c);
    };
    auto evalInst = [&](int b, int i) {
        Inst &x = f.bb[b].insts[i];
        if (x.op == OP_JMP) { flowWork.push_back({b, x.tgt[0]}); return; }
        if (x.op == OP_BR) {
            uint8_t s;
            uint32_t c;
            lat(x.a[0], s, c);
            if (s == TOP) return;
            if (s == CONSTV) flowWork.push_back({b, c ? x.tgt[0] : x.tgt[1]});
            else { flowWork.push_back({b, x.tgt[0]}); flowWork.push_back({b, x.tgt[1]}); }
            return;
        }
        if (x.dst < 0) return;
        if (x.op == OP_LOAD || x.op == OP_VLOAD) { setVal(x.dst, BOT, 0); return; }
        uint8_t s[3] = {CONSTV, CONSTV, CONSTV};
        uint32_t c[3] = {0, 0, 0};
        bool anyTop = false, anyBot = false;
        for (int a = 0; a < x.n; a++) {
            lat(x.a[a], s[a], c[a]);
            if (s[a] == TOP) anyTop = true;
            if (s[a] == BOT) anyBot = true;
        }
        if (x.op == OP_SELECT && s[0] == CONSTV) {
            int pick = c[0] ? 1 : 2;
            setVal(x.dst, s[pick], c[pick]);
            return;
        }
        if ((x.op == OP_MUL || x.op == OP_AND) &&
            ((s[0] == CONSTV && c[0] == 0) || (s[1] == CONSTV && c[1] == 0))) {
            setVal(x.dst, CONSTV, 0);
            return;
        }
        if (anyBot) { setVal(x.dst, BOT, 0); return; }
        if (anyTop) return;
        uint32_t out;
        if (foldConstant(x.op, c[0], c[1], c[2], x.k, out)) setVal(x.dst, CONSTV, out);
        else setVal(x.dst, BOT, 0);
    };
    flowWork.push_back({-1, 0});
    while (!flowWork.empty() || !ssaWork.empty()) {
        while (!flowWork.empty()) {
            auto e = flowWork.back();
            flowWork.pop_back();
            if (e.first >= 0) {
                if (edgeExec(e.first, e.second)) continue;
                execEdges.push_back(e);
            }
            int b = e.second;
            for (int k = 0; k < static_cast<int>(f.bb[b].phis.size()); k++) evalPhi(b, k);
            if (!blockExec[b]) {
                blockExec[b] = 1;
                for (int i = 0; i < static_cast<int>(f.bb[b].insts.size()); i++) evalInst(b, i);
            }
        }
        while (!ssaWork.empty()) {
            auto u = ssaWork.back();
            ssaWork.pop_back();
            if (!blockExec[u.first]) continue;
            if (u.second < 0) evalPhi(u.first, -1 - u.second);
            else evalInst(u.first, u.second);
        }
    }
    bool changed = false;
    for (int v = 0; v < nv; v++) {
        if (st[v] == CONSTV && f.fwd[v] == Opnd::val(v)) {
            f.replaceAll(v, Opnd::cst(cv[v]));
            changed = true;
        }
    }
    for (int b = 0; b < nb; b++) {
        BB &B = f.bb[b];
        if (!B.alive) continue;
        if (!blockExec[b]) { B.alive = false; changed = true; continue; }
        Inst &t = B.term();
        if (t.op == OP_BR) {
            bool e0 = edgeExec(b, t.tgt[0]), e1 = edgeExec(b, t.tgt[1]);
            if (e0 != e1) {
                int target = e0 ? t.tgt[0] : t.tgt[1];
                t.op = OP_JMP;
                t.n = 0;
                t.tgt[0] = target;
                t.tgt[1] = -1;
                changed = true;
            }
        }
    }
    if (changed) {
        f.rebuildPreds();
        f.resolveAll();
    }
    return changed;
}

// ---------------------------------------------------------------------------
// Instruction simplification
// ---------------------------------------------------------------------------

namespace {

bool isPow2(uint32_t c) { return c && !(c & (c - 1)); }
int log2u(uint32_t c) { int k = 0; while ((1u << k) != c) k++; return k; }

// Try to simplify x. Returns true if x was changed. When the whole value can be
// replaced by another operand, *hasRepl is set and *repl holds it; otherwise x
// was rewritten in place. A replaced division or remainder always has a known
// non-zero divisor, so turning it into a copy never removes a trap.
bool simplifyOne(Func &f, const std::vector<DefSite> &ds, Inst &x, Opnd *repl, bool *hasRepl) {
    *hasRepl = false;
    for (int a = 0; a < x.n; a++) x.a[a] = f.resolve(x.a[a]);
    if (x.dst < 0) return false;
    const Op op = x.op;
    Opnd A = x.a[0], B = x.n > 1 ? x.a[1] : Opnd(), C = x.n > 2 ? x.a[2] : Opnd();
    // Constant folding (never folds a trapping division).
    bool allConst = true;
    for (int a = 0; a < x.n; a++) allConst = allConst && x.a[a].isConst;
    if (allConst && op != OP_LOAD && op != OP_VLOAD) {
        uint32_t out;
        if (foldConstant(op, A.c, B.c, C.c, x.k, out)) { *repl = Opnd::cst(out); *hasRepl = true; return true; }
        return false;
    }
    // In-place rewrite.
    auto setOp = [&](Op nop, Opnd a0, Opnd a1) {
        x.op = nop; x.n = 2; x.a[0] = f.resolve(a0); x.a[1] = f.resolve(a1);
        *hasRepl = false;
        return true;
    };
    // Every "*repl = ...; return true" below is a whole-value replacement.
    *hasRepl = true;
    // Canonical order: constant second for commutative ops.
    if (isCommutative(op) && A.isConst && !B.isConst) { std::swap(x.a[0], x.a[1]); A = x.a[0]; B = x.a[1]; }
    if (isCommutative(op) && !A.isConst && !B.isConst && A.v > B.v) { std::swap(x.a[0], x.a[1]); A = x.a[0]; B = x.a[1]; }
    const Inst *dA = defInst(f, ds, A);
    switch (op) {
    case OP_MOV:
        *repl = A;
        return true;
    case OP_ADD:
        if (B.isC(0)) { *repl = A; return true; }
        if (B.isConst && dA && dA->op == OP_ADD && dA->a[1].isConst)   // (y + c1) + c2
            return setOp(OP_ADD, dA->a[0], Opnd::cst(dA->a[1].c + B.c));
        if (B.isConst && dA && dA->op == OP_SUB && dA->a[0].isConst)   // (c1 - y) + c2
            return setOp(OP_SUB, Opnd::cst(dA->a[0].c + B.c), dA->a[1]);
        if (!B.isConst) {
            const Inst *dB = defInst(f, ds, B);
            if (dB && dB->op == OP_SUB && dB->a[1] == A) { *repl = dB->a[0]; return true; }   // a + (y - a)
            if (dA && dA->op == OP_SUB && dA->a[1] == B) { *repl = dA->a[0]; return true; }   // (y - b) + b
            if (dB && dB->op == OP_SUB && dB->a[0].isC(0)) return setOp(OP_SUB, A, dB->a[1]);   // a + (0 - y)
            if (dA && dA->op == OP_SUB && dA->a[0].isC(0)) return setOp(OP_SUB, B, dA->a[1]);
        }
        return false;
    case OP_SUB:
        if (B.isC(0)) { *repl = A; return true; }
        if (A == B) { *repl = Opnd::cst(0); return true; }
        if (B.isConst) return setOp(OP_ADD, A, Opnd::cst(0u - B.c));   // canonical: x + (-c)
        {
            const Inst *dB = defInst(f, ds, B);
            if (dA && dA->op == OP_ADD && dA->a[0] == B) { *repl = dA->a[1]; return true; }   // (b + y) - b
            if (dA && dA->op == OP_ADD && dA->a[1] == B) { *repl = dA->a[0]; return true; }   // (y + b) - b
            if (dB && dB->op == OP_ADD && dB->a[0] == A && dB->a[1].isConst)                 // a - (a + c)
                { *repl = Opnd::cst(0u - dB->a[1].c); return true; }
            if (dA && dB && dA->op == OP_ADD && dB->op == OP_ADD && dA->a[1].isConst && dB->a[1].isConst &&
                dA->a[0] == dB->a[0])                                                          // (y+c1)-(y+c2)
                { *repl = Opnd::cst(dA->a[1].c - dB->a[1].c); return true; }
            if (dA && dA->op == OP_ADD && dA->a[1].isConst && dA->a[0] == B)                  // (b + c) - b
                { *repl = Opnd::cst(dA->a[1].c); return true; }
            if (A.isConst && dB && dB->op == OP_ADD && dB->a[1].isConst)                      // c1 - (y + c2)
                return setOp(OP_SUB, Opnd::cst(A.c - dB->a[1].c), dB->a[0]);
            if (dB && dB->op == OP_SUB && dB->a[0].isC(0)) return setOp(OP_ADD, A, dB->a[1]);  // a - (0 - y)
        }
        return false;
    case OP_MUL:
        if (B.isC(0)) { *repl = Opnd::cst(0); return true; }
        if (B.isC(1)) { *repl = A; return true; }
        if (B.isC(0xFFFFFFFFu)) return setOp(OP_SUB, Opnd::cst(0), A);
        if (B.isConst && dA && dA->op == OP_MUL && dA->a[1].isConst)
            return setOp(OP_MUL, dA->a[0], Opnd::cst(dA->a[1].c * B.c));
        if (B.isConst && dA && dA->op == OP_SHL && dA->a[1].isConst)
            return setOp(OP_MUL, dA->a[0], Opnd::cst((1u << (dA->a[1].c & 31)) * B.c));
        return false;
    case OP_AND:
        if (B.isC(0)) { *repl = Opnd::cst(0); return true; }
        if (B.isC(0xFFFFFFFFu) || A == B) { *repl = A; return true; }
        if (B.isConst && dA && dA->op == OP_AND && dA->a[1].isConst)
            return setOp(OP_AND, dA->a[0], Opnd::cst(dA->a[1].c & B.c));
        if (B.isConst) {
            Range r = rangeOf(f, ds, A, 6);
            if (r.hi <= B.c && ((maskUpTo(r.hi) & B.c) == maskUpTo(r.hi))) { *repl = A; return true; }
        }
        return false;
    case OP_OR:
        if (B.isC(0) || A == B) { *repl = A; return true; }
        if (B.isC(0xFFFFFFFFu)) { *repl = Opnd::cst(0xFFFFFFFFu); return true; }
        if (B.isConst && dA && dA->op == OP_OR && dA->a[1].isConst)
            return setOp(OP_OR, dA->a[0], Opnd::cst(dA->a[1].c | B.c));
        return false;
    case OP_XOR:
        if (B.isC(0)) { *repl = A; return true; }
        if (A == B) { *repl = Opnd::cst(0); return true; }
        if (B.isConst && dA && dA->op == OP_XOR && dA->a[1].isConst)
            return setOp(OP_XOR, dA->a[0], Opnd::cst(dA->a[1].c ^ B.c));
        if (!B.isConst) {
            const Inst *dB = defInst(f, ds, B);
            if (dA && dA->op == OP_XOR && dA->a[1] == B) { *repl = dA->a[0]; return true; }   // (y^b)^b
            if (dA && dA->op == OP_XOR && dA->a[0] == B) { *repl = dA->a[1]; return true; }
            if (dB && dB->op == OP_XOR && dB->a[1] == A) { *repl = dB->a[0]; return true; }
            if (dB && dB->op == OP_XOR && dB->a[0] == A) { *repl = dB->a[1]; return true; }
        }
        return false;
    case OP_SHL: case OP_SHR:
        if (B.isConst && (B.c & 31) == 0) { *repl = A; return true; }
        if (A.isC(0)) { *repl = Opnd::cst(0); return true; }
        if (B.isConst && B.c > 31) { x.a[1] = Opnd::cst(B.c & 31); *hasRepl = false; return true; }
        if (B.isConst && dA && dA->op == op && dA->a[1].isConst) {
            uint32_t s = (dA->a[1].c & 31) + (B.c & 31);
            if (s > 31) { *repl = Opnd::cst(0); return true; }
            return setOp(op, dA->a[0], Opnd::cst(s));
        }
        if (op == OP_SHR && B.isConst) {
            Range r = rangeOf(f, ds, A, 6);
            if ((r.hi >> (B.c & 31)) == 0) { *repl = Opnd::cst(0); return true; }
        }
        return false;
    case OP_LT:
        if (A == B) { *repl = Opnd::cst(0); return true; }
        if (B.isC(0x80000000u)) { *repl = Opnd::cst(0); return true; }     // nothing is < INT_MIN
        if (A.isC(0x7FFFFFFFu)) { *repl = Opnd::cst(0); return true; }     // INT_MAX < nothing
        {
            Range ra = rangeOf(f, ds, A, 6), rb = rangeOf(f, ds, B, 6);
            if (ra.hi < 0x80000000ull && rb.hi < 0x80000000ull) {
                if (ra.hi < rb.lo) { *repl = Opnd::cst(1); return true; }
                if (ra.lo >= rb.hi) { *repl = Opnd::cst(0); return true; }
            }
        }
        return false;
    case OP_EQ:
        if (A == B) { *repl = Opnd::cst(1); return true; }
        if (B.isConst) {
            Range r = rangeOf(f, ds, A, 6);
            if (B.c < r.lo || B.c > r.hi) { *repl = Opnd::cst(0); return true; }
            // eq(lt(..), 1) == lt(..); eq(eq(..), 1) == eq(..)
            if (B.c == 1 && r.hi <= 1) { *repl = A; return true; }
        }
        return false;
    case OP_SELECT:
        if (A.isConst) { *repl = A.c ? B : C; return true; }
        if (B == C) { *repl = B; return true; }
        if (B.isC(1) && C.isC(0)) {
            Range r = rangeOf(f, ds, A, 6);
            if (r.hi <= 1) { *repl = A; return true; }
        }
        return false;
    case OP_DIV:
        if (B.isC(1)) { *repl = A; return true; }
        if (B.isC(0xFFFFFFFFu)) return setOp(OP_SUB, Opnd::cst(0), A);
        if (B.isConst && B.c != 0 && B.c < 0x80000000u && isPow2(B.c)) {
            Range r = rangeOf(f, ds, A, 6);
            if (r.hi < 0x80000000ull) return setOp(OP_SHR, A, Opnd::cst(log2u(B.c)));
        }
        return false;
    case OP_MOD:
        if (B.isC(1) || B.isC(0xFFFFFFFFu)) { *repl = Opnd::cst(0); return true; }
        if (B.isConst && B.c != 0 && B.c < 0x80000000u && isPow2(B.c)) {
            Range r = rangeOf(f, ds, A, 6);
            if (r.hi < 0x80000000ull) return setOp(OP_AND, A, Opnd::cst(B.c - 1));
        }
        if (B.isConst && B.c != 0 && B.c < 0x80000000u) {
            Range r = rangeOf(f, ds, A, 6);
            if (r.hi < B.c) { *repl = A; return true; }
        }
        return false;
    case OP_MAC:
        if (A.isC(0) || B.isC(0)) { *repl = C; return true; }
        return false;
    case OP_ADDSH:
        if (B.isC(0)) { *repl = A; return true; }
        return false;
    default:
        return false;
    }
}

}  // namespace

bool instSimplify(Func &f) {
    bool changed = false;
    for (int round = 0; round < 20; round++) {
        bool again = false;
        f.resolveAll();
        std::vector<DefSite> ds = defSites(f);
        DomInfo d = computeDominators(f);
        for (int b : d.rpo) {
            BB &B = f.bb[b];
            // Trivial phis: every input (ignoring self references) is the same.
            for (size_t k = 0; k < B.phis.size();) {
                Phi &p = B.phis[k];
                Opnd same;
                bool trivial = true, have = false;
                for (auto &in : p.in) {
                    Opnd o = f.resolve(in.second);
                    if (!o.isConst && o.v == p.dst) continue;
                    if (!have) { same = o; have = true; }
                    else if (o != same) { trivial = false; break; }
                }
                if (trivial) {
                    f.replaceAll(p.dst, have ? same : Opnd::cst(0));
                    B.phis.erase(B.phis.begin() + k);
                    again = true;
                } else {
                    k++;
                }
            }
            for (Inst &x : B.insts) {
                if (x.op == OP_BR || x.op == OP_RET || x.op == OP_TRAP || x.op == OP_STORE || x.op == OP_VSTORE) {
                    for (int a = 0; a < x.n; a++) x.a[a] = f.resolve(x.a[a]);
                    continue;
                }
                if (x.dst < 0 || f.fwd[x.dst] != Opnd::val(x.dst)) continue;
                if (x.op == OP_LOAD || x.op == OP_VLOAD) {
                    for (int a = 0; a < x.n; a++) x.a[a] = f.resolve(x.a[a]);
                    continue;
                }
                Opnd repl;
                bool hasRepl = false;
                if (!simplifyOne(f, ds, x, &repl, &hasRepl)) continue;
                if (hasRepl) {
                    repl = f.resolve(repl);
                    if (!repl.isConst && repl.v == x.dst) continue;
                    f.replaceAll(x.dst, repl);
                    x.op = OP_MOV;
                    x.n = 1;
                    x.a[0] = repl;
                }
                again = true;
            }
        }
        if (!again) break;
        changed = true;
    }
    return changed;
}

// ---------------------------------------------------------------------------
// Global value numbering with load/store forwarding
// ---------------------------------------------------------------------------

namespace {

struct ExprKey {
    Op op;
    uint8_t k;
    Opnd a[3];
    bool operator==(const ExprKey &o) const {
        return op == o.op && k == o.k && a[0] == o.a[0] && a[1] == o.a[1] && a[2] == o.a[2];
    }
};
struct ExprHash {
    size_t operator()(const ExprKey &e) const {
        uint64_t h = static_cast<uint64_t>(e.op) * 0x9E3779B97F4A7C15ull + e.k;
        for (int i = 0; i < 3; i++) {
            uint64_t x = e.a[i].isConst ? (0x100000000ull | e.a[i].c) : static_cast<uint64_t>(static_cast<uint32_t>(e.a[i].v));
            h ^= x + 0x9E3779B97F4A7C15ull + (h << 6) + (h >> 2);
        }
        return static_cast<size_t>(h);
    }
};

// Address = base + offset (base is a value, or "none" for absolute addresses).
struct AddrForm {
    bool hasBase;
    Val base;
    uint32_t off;
};

AddrForm addrForm(const Func &f, const std::vector<DefSite> &ds, Opnd a) {
    if (a.isConst) return AddrForm{false, -1, a.c};
    const Inst *x = defInst(f, ds, a);
    if (x && x->op == OP_ADD && x->a[1].isConst && !x->a[0].isConst) return AddrForm{true, x->a[0].v, x->a[1].c};
    if (x && x->op == OP_ADD && x->a[0].isConst && !x->a[1].isConst) return AddrForm{true, x->a[1].v, x->a[0].c};
    return AddrForm{true, a.v, 0};
}

bool mustDiffer(const Func &f, const std::vector<DefSite> &ds, Opnd a, Opnd b) {
    AddrForm x = addrForm(f, ds, a), y = addrForm(f, ds, b);
    if (x.hasBase == y.hasBase && (!x.hasBase || x.base == y.base)) return x.off != y.off;
    // Disjoint value ranges.
    Range ra = rangeOf(f, ds, a, 6), rb = rangeOf(f, ds, b, 6);
    return ra.hi < rb.lo || rb.hi < ra.lo;
}

}  // namespace

bool gvn(Func &f) {
    f.resolveAll();
    DomInfo d = computeDominators(f);
    std::vector<DefSite> ds = defSites(f);
    std::unordered_map<ExprKey, Val, ExprHash> table;
    struct Undo { ExprKey key; bool had; Val old; };
    std::vector<Undo> undo;
    using MemTable = std::vector<std::pair<Opnd, Opnd>>;   // address -> known value
    std::vector<MemTable> memAtEnd(f.bb.size());
    bool changed = false;

    struct Frame { int b; size_t child; size_t undoMark; };
    std::vector<Frame> st;
    auto visit = [&](int b) {
        BB &B = f.bb[b];
        MemTable mem;
        if (B.preds.size() == 1 && d.idom[b] == B.preds[0]) mem = memAtEnd[B.preds[0]];
        // Phis with identical inputs in the same block are the same value.
        for (size_t k = 0; k < B.phis.size(); k++) {
            for (size_t j = 0; j < k; j++) {
                bool same = B.phis[j].in.size() == B.phis[k].in.size();
                for (size_t q = 0; same && q < B.phis[k].in.size(); q++) {
                    Opnd vk = Opnd(), vj = Opnd();
                    bool found = false;
                    for (auto &in : B.phis[j].in)
                        if (in.first == B.phis[k].in[q].first) { vj = f.resolve(in.second); found = true; }
                    vk = f.resolve(B.phis[k].in[q].second);
                    same = found && vj == vk;
                }
                if (same && f.fwd[B.phis[k].dst] == Opnd::val(B.phis[k].dst) &&
                    f.fwd[B.phis[j].dst] == Opnd::val(B.phis[j].dst)) {
                    f.replaceAll(B.phis[k].dst, Opnd::val(B.phis[j].dst));
                    changed = true;
                    break;
                }
            }
        }
        for (Inst &x : B.insts) {
            for (int a = 0; a < x.n; a++) x.a[a] = f.resolve(x.a[a]);
            if (x.op == OP_STORE) {
                Opnd addr = x.a[0];
                MemTable keep;
                for (auto &e : mem)
                    if (mustDiffer(f, ds, e.first, addr)) keep.push_back(e);
                keep.push_back({addr, x.a[1]});
                mem.swap(keep);
                continue;
            }
            if (x.op == OP_LOAD) {
                Opnd addr = x.a[0];
                bool hit = false;
                for (auto &e : mem)
                    if (e.first == addr) {
                        f.replaceAll(x.dst, e.second);
                        x.op = OP_MOV; x.n = 1; x.a[0] = f.resolve(e.second);
                        hit = true;
                        changed = true;
                        break;
                    }
                if (!hit) mem.push_back({addr, Opnd::val(x.dst)});
                continue;
            }
            if (x.dst < 0 || !(isPure(x.op) || x.op == OP_DIV || x.op == OP_MOD) || x.op == OP_MOV) continue;
            ExprKey key{x.op, x.k, {x.a[0], x.n > 1 ? x.a[1] : Opnd(), x.n > 2 ? x.a[2] : Opnd()}};
            if (isCommutative(x.op)) {
                auto ord = [](const Opnd &p, const Opnd &q) {
                    if (p.isConst != q.isConst) return !p.isConst;
                    return p.isConst ? p.c < q.c : p.v < q.v;
                };
                if (ord(key.a[1], key.a[0])) std::swap(key.a[0], key.a[1]);
            }
            if (x.op == OP_MAC) {
                auto ord = [](const Opnd &p, const Opnd &q) {
                    if (p.isConst != q.isConst) return !p.isConst;
                    return p.isConst ? p.c < q.c : p.v < q.v;
                };
                if (ord(key.a[1], key.a[0])) std::swap(key.a[0], key.a[1]);
            }
            auto it = table.find(key);
            if (it != table.end()) {
                // A dominating identical computation already ran: same value, and an
                // identical division cannot trap here because that one did not.
                f.replaceAll(x.dst, Opnd::val(it->second));
                x.op = OP_MOV; x.n = 1; x.a[0] = Opnd::val(it->second);
                changed = true;
            } else {
                undo.push_back({key, false, -1});
                table.emplace(key, x.dst);
            }
        }
        memAtEnd[b] = mem;
    };
    st.push_back({0, 0, undo.size()});
    visit(0);
    while (!st.empty()) {
        Frame &top = st.back();
        if (top.child < d.children[top.b].size()) {
            int c = d.children[top.b][top.child++];
            st.push_back({c, 0, undo.size()});
            visit(c);
        } else {
            while (undo.size() > top.undoMark) {
                table.erase(undo.back().key);
                undo.pop_back();
            }
            st.pop_back();
        }
    }
    if (changed) f.resolveAll();
    return changed;
}

// ---------------------------------------------------------------------------
// Dead code elimination
// ---------------------------------------------------------------------------

bool dce(Func &f) {
    f.resolveAll();
    std::vector<DefSite> ds = defSites(f);
    std::vector<char> live(f.nvals, 0);
    std::vector<Val> work;
    auto markOp = [&](Opnd o) {
        if (!o.isConst && !live[o.v]) { live[o.v] = 1; work.push_back(o.v); }
    };
    for (BB &B : f.bb) {
        if (!B.alive) continue;
        for (Inst &x : B.insts) {
            bool root = x.dst < 0 || x.op == OP_VLOAD || mayTrapWith(f, ds, x);
            if (root) {
                if (x.dst >= 0 && !live[x.dst]) live[x.dst] = 1;   // keep the instruction itself
                for (int a = 0; a < x.n; a++) markOp(x.a[a]);
            }
        }
    }
    while (!work.empty()) {
        Val v = work.back();
        work.pop_back();
        const DefSite &dsv = ds[v];
        if (dsv.block < 0) continue;
        BB &B = f.bb[dsv.block];
        if (dsv.isPhi) {
            for (Phi &p : B.phis)
                if (p.dst == v)
                    for (auto &in : p.in) markOp(in.second);
        } else {
            Inst &x = B.insts[dsv.idx];
            for (int a = 0; a < x.n; a++) markOp(x.a[a]);
        }
    }
    bool changed = false;
    for (BB &B : f.bb) {
        if (!B.alive) continue;
        size_t np = B.phis.size();
        B.phis.erase(std::remove_if(B.phis.begin(), B.phis.end(), [&](const Phi &p) { return !live[p.dst]; }), B.phis.end());
        size_t ni = B.insts.size();
        B.insts.erase(std::remove_if(B.insts.begin(), B.insts.end(), [&](const Inst &x) {
            return x.dst >= 0 && !live[x.dst];
        }), B.insts.end());
        if (np != B.phis.size() || ni != B.insts.size()) changed = true;
    }
    return changed;
}

// ---------------------------------------------------------------------------
// Dead store elimination (within a block)
// ---------------------------------------------------------------------------

bool deadStores(Func &f) {
    f.resolveAll();
    std::vector<DefSite> ds = defSites(f);
    bool changed = false;
    for (BB &B : f.bb) {
        if (!B.alive) continue;
        std::vector<Opnd> overwritten;   // addresses stored later in this block, unobserved since
        std::vector<char> kill(B.insts.size(), 0);
        for (int i = static_cast<int>(B.insts.size()) - 1; i >= 0; i--) {
            const Inst &x = B.insts[i];
            if (x.op == OP_STORE) {
                // Only a store that cannot trap is a guaranteed overwrite; a store
                // that may trap is a point where earlier stores become visible.
                bool trapping = mayTrapWith(f, ds, x);
                bool dead = false;
                if (!trapping)
                    for (const Opnd &o : overwritten) if (o == x.a[0]) dead = true;
                if (dead) { kill[i] = 1; changed = true; continue; }
                if (trapping) overwritten.clear();
                else overwritten.push_back(x.a[0]);
                continue;
            }
            if (x.op == OP_LOAD) {
                std::vector<Opnd> keep;
                for (const Opnd &o : overwritten)
                    if (mustDiffer(f, ds, o, x.a[0])) keep.push_back(o);
                overwritten.swap(keep);
                if (mayTrapWith(f, ds, x)) overwritten.clear();
                continue;
            }
            if (mayTrapWith(f, ds, x)) overwritten.clear();
        }
        if (changed) {
            std::vector<Inst> out;
            for (size_t i = 0; i < B.insts.size(); i++) if (!kill[i]) out.push_back(B.insts[i]);
            B.insts.swap(out);
        }
    }
    return changed;
}

// Implemented in later files.
bool licm(Func &) { return false; }
bool fuseOps(Func &, const Machine &) { return false; }
bool ifConvert(Func &, const Machine &) { return false; }

}  // namespace kopt
