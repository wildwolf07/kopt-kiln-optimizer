// passes.cpp - machine-independent SSA optimizations.
#include "passes.h"

#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <functional>
#include <map>
#include <unordered_map>
#include <unordered_set>

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
    // Values created after ds was computed are "unknown" (conservative).
    if (o.isConst || o.v < 0 || o.v >= static_cast<int>(ds.size())) return nullptr;
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

// Ranges of loop induction variables (computeIVRanges). Facts about a value
// stay true for as long as the value exists, so the table never goes stale;
// values created later simply are not in it.
std::vector<Range> gIVRange;

Range rangeOf(const Func &f, const std::vector<DefSite> &ds, Opnd o, int depth) {
    Range full;
    if (o.isConst) return Range{o.c, o.c};
    if (depth <= 0) return full;
    if (o.v >= 0 && o.v < static_cast<int>(gIVRange.size()) && !gIVRange[o.v].full()) return gIVRange[o.v];
    const Inst *x = defInst(f, ds, o);
    if (!x) {
        if (o.v < 0 || o.v >= static_cast<int>(ds.size())) return full;
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

// Induction variables: a loop-header phi P = phi(init, P + c) with a small
// constant step c > 0, where every iteration that continues has passed a test
// "X < N" (X is P or P + c, N loop-invariant). If init and N are known
// non-negative and N + c stays below 2^31, P never wraps and stays in
// [lo(init), max(hi(init), hi(N) + c - 1)].
void computeIVRanges(Func &f) {
    f.resolveAll();
    f.rebuildPreds();
    gIVRange.assign(f.nvals, Range());
    DomInfo d = computeDominators(f);
    LoopInfo li = computeLoops(f, d);
    std::vector<bool> irr = irreducibleBlocks(f, d);
    for (int pass = 0; pass < 2; pass++) {   // twice: inner bounds may use outer IVs
        std::vector<DefSite> ds = defSites(f);
        for (size_t l = 0; l < li.loops.size(); l++) {
            const LoopInfo::Loop &L = li.loops[l];
            const int h = L.header;
            if (irr[h] || L.latches.size() != 1) continue;
            auto inL = [&](int b) { return b >= 0 && li.inLoop(b, static_cast<int>(l)); };
            const int latch = L.latches[0];
            // The exit tests: branches in the loop with one target outside.
            std::vector<int> tests;
            for (int b : L.blocks) {
                const Inst &t = f.bb[b].term();
                if (t.op == OP_BR && inL(t.tgt[0]) != inL(t.tgt[1])) tests.push_back(b);
            }
            for (const Phi &p : f.bb[h].phis) {
                if (p.in.size() != 2) continue;
                Opnd init, next;
                bool haveInit = false, haveNext = false;
                for (auto &in : p.in) {
                    if (in.first == latch) { next = f.resolve(in.second); haveNext = true; }
                    else if (!inL(in.first)) { init = f.resolve(in.second); haveInit = true; }
                }
                if (!haveInit || !haveNext || next.isConst) continue;
                const Inst *nx = defInst(f, ds, next);
                if (!nx || nx->op != OP_ADD) continue;
                Opnd a0 = f.resolve(nx->a[0]), a1 = f.resolve(nx->a[1]);
                uint32_t c;
                if (!a0.isConst && a0.v == p.dst && a1.isConst) c = a1.c;
                else if (!a1.isConst && a1.v == p.dst && a0.isConst) c = a0.c;
                else continue;
                if (c == 0 || c > 65536) continue;
                Range ri = rangeOf(f, ds, init, 8);
                if (ri.hi >= 0x80000000ull) continue;
                // A dominating-every-latch test "X < N" whose in-loop side continues.
                uint64_t bestHi = 0xFFFFFFFFull;
                for (int tb : tests) {
                    if (!d.dominates(tb, latch)) continue;
                    const Inst &t = f.bb[tb].term();
                    const Inst *cmp = defInst(f, ds, f.resolve(t.a[0]));
                    if (!cmp || cmp->op != OP_LT) continue;
                    Opnd X = f.resolve(cmp->a[0]), N = f.resolve(cmp->a[1]);
                    bool xIsP = !X.isConst && X.v == p.dst, xIsNext = X == next;
                    if (!xIsP && !xIsNext) continue;
                    // A post-increment test observes the wrapped result on the
                    // very first iteration. Its guard cannot establish a
                    // nonnegative recurrence if init+step already overflows.
                    if (xIsNext && ri.hi + c >= 0x80000000ull) continue;
                    if (!inL(t.tgt[0]) || inL(t.tgt[1])) continue;   // true must stay in the loop
                    if (!N.isConst) {
                        const DefSite &nd = ds[N.v];
                        if (nd.block >= 0 && inL(nd.block)) continue;   // N must be invariant
                    }
                    Range rn = rangeOf(f, ds, N, 8);
                    if (rn.hi + c >= 0x80000000ull) continue;
                    bestHi = std::min<uint64_t>(bestHi, std::max<uint64_t>(ri.hi, rn.hi + c - 1));
                }
                if (bestHi < 0x80000000ull) gIVRange[p.dst] = Range{ri.lo, bestHi};
            }
        }
    }
}

void clearIVRanges() { gIVRange.clear(); }

// ---------------------------------------------------------------------------
// Value range propagation (signed intervals) with branch refinement.
//
// Every value gets a signed interval [lo, hi] that holds on every execution.
// Operands are refined by the branch conditions that guard their use: a block
// reached only through the "true" edge of br (lt a, b) knows a < b. Facts come
// from chains of single-predecessor blocks, so the guarding edge is always on
// the way in. Ranges start empty and only grow (union with the old value); a
// value that keeps growing is widened to the type limit, so the iteration
// ends. If it does not settle within the iteration cap, nothing is used.
// ---------------------------------------------------------------------------

namespace {

constexpr int64_t kSMin = -2147483648LL, kSMax = 2147483647LL;

struct SR {
    int64_t lo = 1, hi = 0;   // lo > hi: empty
    bool empty() const { return lo > hi; }
    static SR full() { return SR{kSMin, kSMax}; }
    static SR pt(int64_t v) { return SR{v, v}; }
};

SR sOfConst(uint32_t c) { return SR::pt(static_cast<int32_t>(c)); }

SR clampSR(int64_t lo, int64_t hi) {
    if (lo < kSMin || hi > kSMax) return SR::full();
    return SR{lo, hi};
}

SR unionSR(SR a, SR b) {
    if (a.empty()) return b;
    if (b.empty()) return a;
    return SR{std::min(a.lo, b.lo), std::max(a.hi, b.hi)};
}

SR fromRange(const Range &r) {
    if (r.hi <= static_cast<uint64_t>(kSMax)) return SR{static_cast<int64_t>(r.lo), static_cast<int64_t>(r.hi)};
    if (r.lo >= 0x80000000ull) return SR{static_cast<int64_t>(r.lo) - 4294967296LL, static_cast<int64_t>(r.hi) - 4294967296LL};
    return SR::full();
}

Range toRange(const SR &s) {
    if (s.empty()) return Range();
    if (s.lo >= 0) return Range{static_cast<uint64_t>(s.lo), static_cast<uint64_t>(s.hi)};
    if (s.hi < 0) return Range{static_cast<uint64_t>(s.lo + 4294967296LL), static_cast<uint64_t>(s.hi + 4294967296LL)};
    return Range();
}

// A fact "v rel other" known at some point. rel: 0 <, 1 <=, 2 >, 3 >=, 4 ==, 5 !=
struct Fact { Val v; int rel; Opnd other; };

void factsFromCond(const Func &f, const std::vector<DefSite> &ds, Opnd c, bool truth, std::vector<Fact> &out, int depth) {
    if (c.isConst || depth > 3) return;
    out.push_back({c.v, truth ? 5 : 4, Opnd::cst(0)});
    const Inst *d = defInst(f, ds, c);
    if (!d) return;
    if (d->op == OP_LT) {
        Opnd a = d->a[0], b = d->a[1];
        if (!a.isConst) out.push_back({a.v, truth ? 0 : 3, b});
        if (!b.isConst) out.push_back({b.v, truth ? 2 : 1, a});
    } else if (d->op == OP_EQ) {
        Opnd a = d->a[0], b = d->a[1];
        // eq(x, 0) where x is a condition: the negation of x.
        if (b.isC(0) && !a.isConst) {
            const Inst *xa = defInst(f, ds, a);
            if (xa && (xa->op == OP_LT || xa->op == OP_EQ)) factsFromCond(f, ds, a, !truth, out, depth + 1);
        }
        if (!a.isConst) out.push_back({a.v, truth ? 4 : 5, b});
        if (!b.isConst) out.push_back({b.v, truth ? 4 : 5, a});
    }
}

// Facts that hold on entry to block b: walk the chain of single predecessors.
// With idom (dominators of the current CFG): walk up the dominator tree
// instead. A block a with a single predecessor p is entered only along the
// edge p->a, so the branch fact of that edge holds in every block a dominates.
std::vector<Fact> chainFacts(const Func &f, const std::vector<DefSite> &ds, int b,
                             const std::vector<int> *idom = nullptr) {
    std::vector<Fact> out;
    for (int depth = 0; depth < 48 && b > 0; depth++) {
        const BB &B = f.bb[b];
        if (B.preds.size() != 1) {
            if (!idom) break;
            b = (*idom)[b];
            continue;
        }
        const int p = B.preds[0];
        const Inst &t = f.bb[p].term();
        if (t.op == OP_BR && t.tgt[0] != t.tgt[1]) factsFromCond(f, ds, t.a[0], t.tgt[0] == b, out, 0);
        b = p;
    }
    return out;
}

SR refine(SR r, Val v, const std::vector<Fact> &facts, const std::function<SR(Opnd)> &rangeOfOther) {
    if (r.empty()) return r;
    for (const Fact &fa : facts) {
        if (fa.v != v) continue;
        SR o = rangeOfOther(fa.other);
        if (o.empty()) continue;
        switch (fa.rel) {
        case 0: r.hi = std::min(r.hi, o.hi - 1); break;
        case 1: r.hi = std::min(r.hi, o.hi); break;
        case 2: r.lo = std::max(r.lo, o.lo + 1); break;
        case 3: r.lo = std::max(r.lo, o.lo); break;
        case 4: r.lo = std::max(r.lo, o.lo); r.hi = std::min(r.hi, o.hi); break;
        case 5:
            if (o.lo == o.hi) {
                if (r.lo == o.lo) r.lo++;
                if (r.hi == o.lo) r.hi--;
            }
            break;
        }
        if (r.empty()) return r;
    }
    return r;
}

SR transfer(const Inst &x, const std::function<SR(int)> &R) {
    auto A = [&](int i) { return R(i); };
    switch (x.op) {
    case OP_MOV: return A(0);
    case OP_ADD: { SR a = A(0), b = A(1); return clampSR(a.lo + b.lo, a.hi + b.hi); }
    case OP_SUB: { SR a = A(0), b = A(1); return clampSR(a.lo - b.hi, a.hi - b.lo); }
    case OP_MUL: case OP_MAC: {
        SR a = A(0), b = A(1);
        if (a.lo < -65536 || a.hi > 65536 || b.lo < -65536 || b.hi > 65536) return SR::full();
        int64_t p[4] = {a.lo * b.lo, a.lo * b.hi, a.hi * b.lo, a.hi * b.hi};
        SR m{*std::min_element(p, p + 4), *std::max_element(p, p + 4)};
        if (x.op == OP_MUL) return clampSR(m.lo, m.hi);
        SR c = A(2);
        return clampSR(m.lo + c.lo, m.hi + c.hi);
    }
    case OP_ADDSH: {
        SR a = A(0), b = A(1);
        if (b.lo < -65536 || b.hi > 65536 || x.k > 15) return SR::full();
        const int64_t scale = 1LL << x.k;
        return clampSR(a.lo + b.lo * scale, a.hi + b.hi * scale);
    }
    case OP_AND: {
        SR a = A(0), b = A(1);
        if (a.lo >= 0 && b.lo >= 0) return SR{0, std::min(a.hi, b.hi)};
        if (a.lo >= 0) return SR{0, a.hi};
        if (b.lo >= 0) return SR{0, b.hi};
        return SR::full();
    }
    case OP_OR: case OP_XOR: {
        SR a = A(0), b = A(1);
        if (a.lo >= 0 && b.lo >= 0) return SR{0, static_cast<int64_t>(maskUpTo(static_cast<uint64_t>(std::max(a.hi, b.hi))))};
        return SR::full();
    }
    case OP_SHL: {
        SR a = A(0), b = A(1);
        if (b.lo != b.hi) return SR::full();
        int k = static_cast<int>(b.lo & 31);
        if (a.lo < -(1LL << 30) || a.hi > (1LL << 30)) return SR::full();
        return clampSR(a.lo * (1LL << k), a.hi * (1LL << k));
    }
    case OP_SHR: {
        SR a = A(0), b = A(1);
        if (b.lo == b.hi) {
            int k = static_cast<int>(b.lo & 31);
            if (a.lo >= 0) return SR{a.lo >> k, a.hi >> k};
            if (k >= 1) return SR{0, static_cast<int64_t>(0xFFFFFFFFull >> k)};
            return a;
        }
        if (a.lo >= 0) return SR{0, a.hi};
        return SR::full();
    }
    case OP_LT: case OP_EQ: return SR{0, 1};
    case OP_SELECT: return unionSR(A(1), A(2));
    case OP_DIV: {
        SR a = A(0), b = A(1);
        if (b.lo >= 1) {
            int64_t c1 = b.lo, c2 = b.hi;
            int64_t q[4] = {a.lo / c1, a.lo / c2, a.hi / c1, a.hi / c2};
            return SR{*std::min_element(q, q + 4), *std::max_element(q, q + 4)};
        }
        return SR::full();
    }
    case OP_MOD: {
        SR a = A(0), b = A(1);
        int64_t m = std::max(std::llabs(b.lo), std::llabs(b.hi));
        if (b.lo <= 0 && b.hi >= 0 && m == 0) return SR::full();
        if (m == 0 || m > kSMax) return SR::full();
        if (a.lo >= 0) return SR{0, std::min(a.hi, m - 1)};
        if (a.hi <= 0) return SR{std::max(a.lo, -(m - 1)), 0};
        return SR{-(m - 1), m - 1};
    }
    default:
        return SR::full();
    }
}

std::vector<SR> gVRP;   // signed ranges from the last computeVRP (by value)

// Trip-count bounds for innermost loops (from a sound range solution sr).
// Every path from the header back to it (the loop body without inner loops is
// a DAG) changes each header phi by an exact constant, or by something we
// cannot follow. If a set S of header phis with bounded ranges only grows,
// and on every path their sum grows by at least 1, the back edges are taken at
// most B = sum of the range widths of S times per entry into the loop. A
// header phi that changes by [dmin, dmax] per path then stays within
// init + B*[min(dmin,0), max(dmax,0)]. Example: merge loops (k grows each round
// while i or j grows), output pointers that grow in some rounds only.
bool tripCaps(const Func &f, const DomInfo &d, const std::vector<DefSite> &ds, const std::vector<SR> &sr,
              std::vector<SR> &cap) {
    LoopInfo li = computeLoops(f, d);
    bool any = false;
    for (size_t l = 0; l < li.loops.size(); l++) {
        const LoopInfo::Loop &L = li.loops[l];
        bool innermost = true;
        for (size_t o = 0; o < li.loops.size(); o++)
            if (o != l && li.loops[o].parent == static_cast<int>(l)) innermost = false;
        const int h = L.header;
        const BB &H = f.bb[h];
        if (!innermost || H.phis.empty() || h == 0) continue;
        std::vector<char> in(f.bb.size(), 0);
        for (int b : L.blocks) in[b] = 1;
        // Enumerate paths header -> latch (edges into h end a path).
        std::vector<std::vector<int>> paths;
        std::vector<int> cur{h};
        bool tooMany = false;
        std::function<void(int)> dfs = [&](int b) {
            if (tooMany) return;
            int s[2];
            int ns = f.succs(b, s);
            for (int i = 0; i < ns && !tooMany; i++) {
                if (i == 1 && s[1] == s[0]) continue;
                const int t = s[i];
                if (t < 0 || !in[t]) continue;
                if (t == h) {
                    if (paths.size() >= 48) { tooMany = true; return; }
                    paths.push_back(cur);
                    continue;
                }
                if (cur.size() > 64) { tooMany = true; return; }
                for (int c : cur) if (c == t) { tooMany = true; return; }   // not a DAG: give up
                cur.push_back(t);
                dfs(t);
                cur.pop_back();
            }
        };
        dfs(h);
        if (tooMany || paths.empty()) continue;
        const int np = static_cast<int>(H.phis.size());
        // delta[v][p]: exact change of header phi v along path p (or none).
        std::vector<std::vector<int64_t>> delta(np, std::vector<int64_t>(paths.size(), 0));
        std::vector<char> known(np, 1);
        for (size_t pi = 0; pi < paths.size() && true; pi++) {
            const std::vector<int> &P = paths[pi];
            auto pos = [&](int b) { for (size_t i = 0; i < P.size(); i++) if (P[i] == b) return static_cast<int>(i); return -1; };
            for (int v = 0; v < np; v++) {
                if (!known[v]) continue;
                const Phi &ph = H.phis[v];
                Opnd x;
                bool got = false;
                for (auto &inc : ph.in) if (inc.first == P.back()) { x = inc.second; got = true; }
                if (!got) { known[v] = 0; continue; }
                int64_t acc = 0;
                bool ok = false;
                for (int step = 0; step < 32; step++) {
                    if (x.isConst) break;
                    if (x.v == ph.dst) { ok = true; break; }
                    const DefSite &dsx = ds[x.v];
                    if (dsx.block < 0) break;
                    if (dsx.isPhi) {
                        if (dsx.block == h) break;
                        const int m = pos(dsx.block);
                        if (m <= 0) break;
                        const Phi *q = nullptr;
                        for (const Phi &pp : f.bb[dsx.block].phis) if (pp.dst == x.v) q = &pp;
                        if (!q) break;
                        bool found = false;
                        for (auto &inc : q->in) if (inc.first == P[m - 1]) { x = inc.second; found = true; }
                        if (!found) break;
                        continue;
                    }
                    const Inst &y = f.bb[dsx.block].insts[dsx.idx];
                    if (y.op == OP_MOV) { x = y.a[0]; continue; }
                    if (y.op == OP_ADD && y.a[1].isConst && !y.a[0].isConst) { acc += static_cast<int32_t>(y.a[1].c); x = y.a[0]; continue; }
                    if (y.op == OP_ADD && y.a[0].isConst && !y.a[1].isConst) { acc += static_cast<int32_t>(y.a[0].c); x = y.a[1]; continue; }
                    if (y.op == OP_SUB && y.a[1].isConst && !y.a[0].isConst) { acc -= static_cast<int32_t>(y.a[1].c); x = y.a[0]; continue; }
                    break;
                }
                if (!ok || acc > (1 << 20) || acc < -(1 << 20)) { known[v] = 0; continue; }
                delta[v][pi] = acc;
            }
        }
        // The measure S: known, never decreasing, bounded header phis.
        int64_t B = 0;
        std::vector<char> inS(np, 0);
        for (int v = 0; v < np; v++) {
            if (!known[v]) continue;
            const SR r = sr[H.phis[v].dst];
            if (r.empty() || r.hi - r.lo > (1 << 20)) continue;
            bool nonneg = true;
            for (size_t pi = 0; pi < paths.size(); pi++) if (delta[v][pi] < 0) nonneg = false;
            if (!nonneg) continue;
            inS[v] = 1;
            B += r.hi - r.lo;
        }
        bool measure = B <= (1 << 22);
        for (size_t pi = 0; pi < paths.size() && measure; pi++) {
            int64_t sum = 0;
            for (int v = 0; v < np; v++) if (inS[v]) sum += delta[v][pi];
            if (sum < 1) measure = false;
        }
        if (!measure) continue;
        for (int v = 0; v < np; v++) {
            if (!known[v]) continue;
            const Phi &ph = H.phis[v];
            SR init;
            for (auto &inc : ph.in) {
                if (in[inc.first]) continue;
                init = unionSR(init, inc.second.isConst ? SR::pt(static_cast<int32_t>(inc.second.c)) : sr[inc.second.v]);
            }
            if (init.empty() || init.lo == kSMin || init.hi == kSMax) continue;
            int64_t dmin = 0, dmax = 0;
            for (size_t pi = 0; pi < paths.size(); pi++) { dmin = std::min(dmin, delta[v][pi]); dmax = std::max(dmax, delta[v][pi]); }
            SR c{init.lo + B * dmin, init.hi + B * dmax};
            if (c.lo < kSMin || c.hi > kSMax) continue;
            SR &old = cap[ph.dst];
            SR nc{std::max(old.lo, c.lo), std::min(old.hi, c.hi)};
            if (nc.empty() || (nc.lo == old.lo && nc.hi == old.hi)) continue;
            old = nc;
            any = true;
        }
    }
    return any;
}



}  // namespace

void computeVRP(Func &f) {
    f.resolveAll();
    f.rebuildPreds();
    gVRP.clear();
    DomInfo d = computeDominators(f);
    std::vector<DefSite> ds = defSites(f);
    const int nv = f.nvals;
    std::vector<SR> sr(nv);
    std::vector<int> grow(nv, 0);
    for (Val p : f.params) sr[p] = SR::full();
    const int nb = static_cast<int>(f.bb.size());
    std::vector<std::vector<Fact>> facts(nb);
    for (int b : d.rpo) facts[b] = chainFacts(f, ds, b, &d.idom);
    // Facts on each edge p -> b into a block with phis: those of p plus p's branch.
    std::map<std::pair<int, int>, std::vector<Fact>> edgeCache;
    auto edgeFacts = [&](int p, int b) -> const std::vector<Fact> & {
        auto key = std::make_pair(p, b);
        auto it = edgeCache.find(key);
        if (it != edgeCache.end()) return it->second;
        std::vector<Fact> ef = facts[p];
        const Inst &t = f.bb[p].term();
        if (t.op == OP_BR && t.tgt[0] != t.tgt[1]) factsFromCond(f, ds, t.a[0], t.tgt[0] == b, ef, 0);
        return edgeCache.emplace(key, std::move(ef)).first->second;
    };
    auto valRange = [&](Opnd o) -> SR { return o.isConst ? sOfConst(o.c) : sr[o.v]; };
    auto refinedIn = [&](Opnd o, int block) -> SR {
        if (o.isConst) return sOfConst(o.c);
        return refine(sr[o.v], o.v, facts[block], valRange);
    };
    // Widening thresholds: the program's constants (and +-1), so a counter
    // bounded by "i < 8" or by "n & 15" widens to that bound rather than to
    // 2^31-1. Every widening step moves to the next threshold, so the number
    // of steps stays finite.
    std::vector<int64_t> thr;
    for (BB &B : f.bb) {
        if (!B.alive) continue;
        for (Inst &x : B.insts)
            for (int a = 0; a < x.n; a++)
                if (x.a[a].isConst) {
                    int64_t c = static_cast<int32_t>(x.a[a].c);
                    for (int64_t dlt = -1; dlt <= 1; dlt++) thr.push_back(c + dlt);
                }
    }
    std::sort(thr.begin(), thr.end());
    thr.erase(std::unique(thr.begin(), thr.end()), thr.end());
    if (thr.size() > 192) {   // keep the search cheap on huge programs: a spread sample
        std::vector<int64_t> keep;
        for (size_t i = 0; i < 192; i++) keep.push_back(thr[i * thr.size() / 192]);
        thr.swap(keep);
    }
    // Caps: proven bounds of header phis (from trip counts), applied on top.
    std::vector<SR> cap(nv, SR::full());
    auto capped = [&](Val v, SR r) {
        if (r.empty()) return r;
        SR x{std::max(r.lo, cap[v].lo), std::min(r.hi, cap[v].hi)};
        return x.empty() ? r : x;
    };
    bool settled = false;
    auto solve = [&]() {
        std::fill(sr.begin(), sr.end(), SR());
        std::fill(grow.begin(), grow.end(), 0);
        for (Val p : f.params) sr[p] = SR::full();
        settled = false;
        for (int iter = 0; iter < 100 && !settled; iter++) {
            settled = true;
            for (int b : d.rpo) {
                BB &B = f.bb[b];
                auto update = [&](Val v, SR nr) {
                    SR old = sr[v];
                    SR u = unionSR(old, nr);
                    if (u.lo == old.lo && u.hi == old.hi && !old.empty()) return;
                    if (old.empty() && u.empty()) return;
                    if (!old.empty() && ++grow[v] > 4) {
                        const bool far = grow[v] > 28;   // thresholds first, then the limits
                        if (u.lo < old.lo) {
                            int64_t t = kSMin;
                            if (!far) for (auto it = thr.rbegin(); it != thr.rend(); ++it) if (*it <= u.lo) { t = *it; break; }
                            u.lo = t;
                        }
                        if (u.hi > old.hi) {
                            int64_t t = kSMax;
                            if (!far) for (int64_t c : thr) if (c >= u.hi) { t = c; break; }
                            u.hi = t;
                        }
                    }
                    sr[v] = u;
                    settled = false;
                };
                for (Phi &ph : B.phis) {
                    SR acc;
                    for (auto &in : ph.in) {
                        const int p = in.first;
                        if (!d.reachable(p)) continue;
                        const std::vector<Fact> &ef = edgeFacts(p, b);
                        Opnd o = in.second;
                        SR r = o.isConst ? sOfConst(o.c) : refine(sr[o.v], o.v, ef, valRange);
                        acc = unionSR(acc, r);
                    }
                    update(ph.dst, capped(ph.dst, acc));
                }
                for (Inst &x : B.insts) {
                    if (x.dst < 0) continue;
                    bool anyEmpty = false;
                    SR ops[3];
                    for (int a = 0; a < x.n; a++) {
                        ops[a] = refinedIn(x.a[a], b);
                        if (ops[a].empty()) anyEmpty = true;
                    }
                    if (anyEmpty && x.op != OP_LOAD && x.op != OP_VLOAD) continue;   // not reached yet
                    SR nr = (x.op == OP_LOAD || x.op == OP_VLOAD) ? SR::full() : transfer(x, [&](int i) { return ops[i]; });
                    update(x.dst, nr);
                }
            }
        }
        // Narrowing: from a sound over-approximation, x := x intersect F(x) stays
        // sound and recovers the bounds that widening threw away (i < 8 => i <= 8).
        if (settled) {
            for (int pass = 0; pass < 4; pass++) {
                for (int b : d.rpo) {
                    BB &B = f.bb[b];
                    auto narrow = [&](Val v, SR nr) {
                        if (nr.empty() || sr[v].empty()) return;
                        SR x{std::max(sr[v].lo, nr.lo), std::min(sr[v].hi, nr.hi)};
                        if (!x.empty()) sr[v] = x;
                    };
                    for (Phi &ph : B.phis) {
                        SR acc;
                        for (auto &in : ph.in) {
                            const int p = in.first;
                            if (!d.reachable(p)) continue;
                            const std::vector<Fact> &ef = edgeFacts(p, b);
                            Opnd o = in.second;
                            acc = unionSR(acc, o.isConst ? sOfConst(o.c) : refine(sr[o.v], o.v, ef, valRange));
                        }
                        narrow(ph.dst, capped(ph.dst, acc));
                    }
                    for (Inst &x : B.insts) {
                        if (x.dst < 0 || x.op == OP_LOAD || x.op == OP_VLOAD) continue;
                        SR ops[3];
                        bool anyEmpty = false;
                        for (int a = 0; a < x.n; a++) {
                            ops[a] = refinedIn(x.a[a], b);
                            if (ops[a].empty()) anyEmpty = true;
                        }
                        if (anyEmpty) continue;
                        narrow(x.dst, transfer(x, [&](int i) { return ops[i]; }));
                    }
                }
            }
        }
    };
    solve();
    if (settled) {
        // Second round with trip-count caps; keep the first if it does not settle.
        std::vector<SR> first = sr;
        if (tripCaps(f, d, ds, sr, cap)) {
            solve();
            if (!settled) { sr = first; settled = true; }
        }
    }
    if (getenv("KOPT_DEBUGRANGE")) {
        fprintf(stderr, "VRP settled=%d\n%s", settled ? 1 : 0, dumpFunc(f).c_str());
        for (int v = 0; v < nv; v++)
            if (!sr[v].empty()) fprintf(stderr, "  %%%d [%lld,%lld] grow=%d\n", v, (long long)sr[v].lo, (long long)sr[v].hi, grow[v]);
    }
    if (!settled) return;   // no fixpoint: use nothing
    gVRP = sr;
    if (static_cast<int>(gIVRange.size()) < nv) gIVRange.resize(nv, Range());
    for (int v = 0; v < nv; v++) {
        if (sr[v].empty()) continue;
        Range r = toRange(sr[v]);
        Range &g = gIVRange[v];
        g.lo = std::max(g.lo, r.lo);
        g.hi = std::min(g.hi, r.hi);
        if (g.lo > g.hi) g = r;   // cannot happen when both are sound; stay safe
    }
}

namespace {

// Range of an operand where it is used in block b: its global range refined by
// the branch facts that guard b.
Range rangeAt(const Func &f, const std::vector<DefSite> &ds, Opnd o, int b,
              const std::vector<int> *idom = nullptr) {
    Range r = rangeOf(f, ds, o, 8);
    if (o.isConst || b < 0) return r;
    std::vector<Fact> facts = chainFacts(f, ds, b, idom);
    if (facts.empty()) return r;
    auto other = [&](Opnd x) -> SR { return fromRange(rangeOf(f, ds, x, 6)); };
    // Start from the signed VRP interval when there is one: a range that
    // crosses zero is "full" as an unsigned range but still bounded signed.
    SR base = fromRange(r);
    if (o.v < static_cast<int>(gVRP.size()) && !gVRP[o.v].empty()) {
        const SR &g = gVRP[o.v];
        SR both{std::max(base.lo, g.lo), std::min(base.hi, g.hi)};
        if (!both.empty()) base = both;
    }
    SR s = refine(base, o.v, facts, other);
    if (s.empty()) return r;
    Range rr = toRange(s);
    uint64_t lo = std::max(r.lo, rr.lo), hi = std::min(r.hi, rr.hi);
    return lo <= hi ? Range{lo, hi} : r;
}

}  // namespace

// ---------------------------------------------------------------------------
// Linear combination: a tree of add/sub/mul-by-constant/shl-by-constant whose
// inner nodes are used only inside the tree is a sum of (coefficient x value)
// terms plus a constant. Equal values are merged (x*8 + x*10 + x*3 + x*16 =
// x*37). Exact: multiplication distributes over addition modulo 2^32.
// ---------------------------------------------------------------------------

bool combineLinear(Func &f) {
    f.resolveAll();
    std::vector<DefSite> ds = defSites(f);
    std::vector<int> uses(f.nvals, 0);
    for (BB &B : f.bb) {
        if (!B.alive) continue;
        for (Phi &p : B.phis) for (auto &in : p.in) if (!in.second.isConst) uses[in.second.v]++;
        for (Inst &x : B.insts) for (int a = 0; a < x.n; a++) if (!x.a[a].isConst) uses[x.a[a].v]++;
    }
    auto isLin = [](const Inst *x) {
        if (!x) return false;
        if (x->op == OP_ADD || x->op == OP_SUB || x->op == OP_ADDSH) return true;   // addsh: a + (b << k)
        if ((x->op == OP_MUL || x->op == OP_SHL) && x->a[1].isConst) return true;
        if (x->op == OP_MAC && x->a[1].isConst) return true;   // mac a, k, c = a*k + c
        return false;
    };
    bool changed = false;
    for (int b = 0; b < static_cast<int>(f.bb.size()); b++) {
        if (!f.bb[b].alive) continue;
        std::vector<std::pair<size_t, std::vector<Inst>>> inserts;
        const size_t nins = f.bb[b].insts.size();
        for (size_t i = 0; i < nins; i++) {
            const Inst root = f.bb[b].insts[i];
            if (root.op != OP_ADD && root.op != OP_SUB && root.op != OP_ADDSH) continue;
            // Gather terms: (coefficient, operand).
            std::vector<std::pair<uint32_t, Opnd>> terms;
            uint32_t konst = 0;
            int inner = 0, leaves = 0;
            struct Item { Opnd o; uint32_t k; bool top; };
            std::vector<Item> work;
            work.push_back({root.a[0], 1u, true});
            work.push_back({root.a[1], root.op == OP_SUB ? 0xFFFFFFFFu
                                       : root.op == OP_ADDSH ? (1u << (root.k & 31)) : 1u, true});
            while (!work.empty()) {
                Item it = work.back();
                work.pop_back();
                if (it.o.isConst) { konst += it.k * it.o.c; leaves++; continue; }
                const Inst *d = defInst(f, ds, it.o);
                if (isLin(d) && uses[it.o.v] == 1 && ds[it.o.v].block == b && inner < 24) {
                    inner++;
                    if (d->op == OP_ADD) { work.push_back({d->a[0], it.k, false}); work.push_back({d->a[1], it.k, false}); }
                    else if (d->op == OP_SUB) { work.push_back({d->a[0], it.k, false}); work.push_back({d->a[1], 0u - it.k, false}); }
                    else if (d->op == OP_MAC) { work.push_back({d->a[0], it.k * d->a[1].c, false}); work.push_back({d->a[2], it.k, false}); }
                    else if (d->op == OP_ADDSH) { work.push_back({d->a[0], it.k, false}); work.push_back({d->a[1], it.k * (1u << (d->k & 31)), false}); }
                    else if (d->op == OP_MUL) work.push_back({d->a[0], it.k * d->a[1].c, false});
                    else work.push_back({d->a[0], it.k * (1u << (d->a[1].c & 31)), false});
                    continue;
                }
                leaves++;
                bool merged = false;
                for (auto &t : terms) if (t.second == it.o) { t.first += it.k; merged = true; }
                if (!merged) terms.push_back({it.k, it.o});
            }
            // Only rewrite if something merged or cancelled.
            size_t nonzero = 0;
            for (auto &t : terms) if (t.first != 0) nonzero++;
            if (inner == 0 || nonzero + (konst != 0 ? 1 : 0) >= static_cast<size_t>(leaves)) continue;
            std::vector<Inst> pre;
            auto emit = [&](Op op, Opnd a, Opnd c) {
                Inst x;
                x.op = op; x.dst = f.newVal(); x.n = 2; x.a[0] = a; x.a[1] = c;
                pre.push_back(x);
                return Opnd::val(x.dst);
            };
            Opnd acc;
            bool have = false;
            std::vector<Opnd> negs;
            for (auto &t : terms) {
                if (t.first == 0) continue;
                bool neg = t.first >= 0x80000000u && t.first != 0x80000000u;
                uint32_t mag = neg ? 0u - t.first : t.first;
                Opnd term = (mag == 1) ? t.second : emit(OP_MUL, t.second, Opnd::cst(mag));
                if (neg) { negs.push_back(term); continue; }
                acc = have ? emit(OP_ADD, acc, term) : term;
                have = true;
            }
            for (Opnd n : negs) {
                acc = have ? emit(OP_SUB, acc, n) : emit(OP_SUB, Opnd::cst(0), n);
                have = true;
            }
            if (!have) acc = Opnd::cst(konst);
            else if (konst != 0) acc = emit(OP_ADD, acc, Opnd::cst(konst));
            // The root becomes a copy of the new sum.
            Inst &r = f.bb[b].insts[i];
            r.op = OP_ADD; r.n = 2; r.k = 0; r.a[0] = acc; r.a[1] = Opnd::cst(0);
            if (!pre.empty()) inserts.push_back({i, pre});
            changed = true;
        }
        for (auto it = inserts.rbegin(); it != inserts.rend(); ++it) {
            auto &ins = f.bb[b].insts;
            ins.insert(ins.begin() + it->first, it->second.begin(), it->second.end());
        }
        if (!inserts.empty()) {
            ds = defSites(f);
            uses.resize(f.nvals, 0);
        }
    }
    return changed;
}

// ---------------------------------------------------------------------------
// Strength reduction: inside a loop, x = P * c for an induction variable
// P = phi(init, P + s) becomes a second induction variable
// Q = phi(init * c, Q + s * c). Exact modulo 2^32.
// ---------------------------------------------------------------------------

bool strengthReduce(Func &f) {
    f.resolveAll();
    f.rebuildPreds();
    DomInfo d = computeDominators(f);
    LoopInfo li = computeLoops(f, d);
    std::vector<bool> irr = irreducibleBlocks(f, d);
    std::vector<DefSite> ds = defSites(f);
    bool changed = false;
    for (size_t l = 0; l < li.loops.size(); l++) {
        const LoopInfo::Loop &L = li.loops[l];
        const int h = L.header;
        if (irr[h] || L.latches.size() != 1) continue;
        auto inL = [&](int b) { return b >= 0 && li.inLoop(b, static_cast<int>(l)); };
        const int latch = L.latches[0];
        std::vector<int> outside;
        for (int p : f.bb[h].preds) if (!inL(p)) outside.push_back(p);
        if (outside.size() != 1) continue;
        const size_t nphis = f.bb[h].phis.size();
        for (size_t pi = 0; pi < nphis; pi++) {
            const Phi p = f.bb[h].phis[pi];
            if (p.in.size() != 2) continue;
            Opnd init, next;
            for (auto &in : p.in) {
                if (in.first == latch) next = f.resolve(in.second);
                else init = f.resolve(in.second);
            }
            if (next.isConst) continue;
            const Inst *nx = defInst(f, ds, next);
            if (!nx || nx->op != OP_ADD) continue;
            Opnd a0 = f.resolve(nx->a[0]), a1 = f.resolve(nx->a[1]);
            uint32_t step;
            if (!a0.isConst && a0.v == p.dst && a1.isConst) step = a1.c;
            else if (!a1.isConst && a1.v == p.dst && a0.isConst) step = a0.c;
            else continue;
            const int nextBlock = ds[next.v].block;
            if (!init.isConst) continue;   // keep it simple: constant start
            // Multiplications of P by a constant inside the loop.
            for (int b : L.blocks) {
                for (size_t i = 0; i < f.bb[b].insts.size(); i++) {
                    Inst &x = f.bb[b].insts[i];
                    if (x.op != OP_MUL || !x.a[1].isConst || x.a[0].isConst || f.resolve(x.a[0]) != Opnd::val(p.dst)) continue;
                    const uint32_t c = x.a[1].c;
                    // Copy now: inserting below may shift (or reallocate) this
                    // block's instruction list, and x would then name another
                    // instruction.
                    const Val xdst = x.dst;
                    const Val q = f.newVal(), qn = f.newVal();
                    Phi qp;
                    qp.dst = q;
                    for (auto &in : p.in)
                        qp.in.push_back({in.first, in.first == latch ? Opnd::val(qn) : Opnd::cst(init.c * c)});
                    Inst inc;
                    inc.op = OP_ADD; inc.dst = qn; inc.n = 2; inc.a[0] = Opnd::val(q); inc.a[1] = Opnd::cst(step * c);
                    // Q + s*c goes right after P + s (same block, so it reaches the latch).
                    std::vector<Inst> &nb = f.bb[nextBlock].insts;
                    size_t pos = 0;
                    while (pos < nb.size() && nb[pos].dst != next.v) pos++;
                    nb.insert(nb.begin() + std::min(pos + 1, nb.size() - 1), inc);
                    f.replaceAll(xdst, Opnd::val(q));
                    f.bb[h].phis.push_back(qp);
                    ds = defSites(f);
                    changed = true;
                    break;   // instruction lists changed; continue with the next block
                }
            }
        }
    }
    if (changed) f.resolveAll();
    return changed;
}

bool memoryAccessesBelow(Func &f, uint32_t limit) {
    f.resolveAll();
    std::vector<DefSite> ds = defSites(f);
    f.rebuildPreds();
    DomInfo dom = computeDominators(f);
    for (int b = 0; b < static_cast<int>(f.bb.size()); b++) {
        BB &B = f.bb[b];
        if (!B.alive || !dom.reachable(b)) continue;
        for (Inst &x : B.insts)
            if ((x.op == OP_LOAD || x.op == OP_STORE) && rangeAt(f, ds, x.a[0], b, &dom.idom).hi >= limit) {
                if (getenv("KOPT_DEBUGRANGE")) {
                    Range r = rangeAt(f, ds, x.a[0], b, &dom.idom);
                    fprintf(stderr, "unbounded %s in B%d addr %%%d range [%llu,%llu]\n", opName(x.op), b, x.a[0].isConst ? -1 : x.a[0].v,
                            (unsigned long long)r.lo, (unsigned long long)r.hi);
                }
                return false;
            }
    }
    return true;
}

bool addressInRange(Func &f, Opnd addr) {
    addr = f.resolve(addr);
    if (addr.isConst) return addr.c < kMemWords;
    std::vector<DefSite> ds = defSites(f);
    return rangeOf(f, ds, addr, 8).hi < kMemWords;
}

// Block-aware: the operand ranges are refined by the branches guarding block b
// (b < 0: no refinement). Only for decisions about the instruction where it is.
static bool mayTrapWith(const Func &f, const std::vector<DefSite> &ds, const Inst &x, int b = -1) {
    switch (x.op) {
    case OP_DIV: case OP_MOD:
        return rangeAt(f, ds, x.a[1], b).lo == 0;
    case OP_LOAD: case OP_STORE:
        return rangeAt(f, ds, x.a[0], b).hi >= kMemWords;
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
                    T.preds.push_back(p);
                }
                // Incremental update (a full rebuild per edge is quadratic on big programs).
                auto &ep = f.bb[e].preds;
                ep.erase(std::find(ep.begin(), ep.end(), p));
                again = true;
            }
        }
        if (again) {
            changed = true;
            removeUnreachable(f);   // also rebuilds the predecessor lists exactly
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
    std::unordered_set<uint64_t> execEdges;   // (from, to) packed
    auto edgeKey = [](int from, int to) {
        return (static_cast<uint64_t>(static_cast<uint32_t>(from)) << 32) | static_cast<uint32_t>(to);
    };
    auto edgeExec = [&](int from, int to) { return execEdges.count(edgeKey(from, to)) != 0; };
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
                execEdges.insert(edgeKey(e.first, e.second));
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
        // x * 2^k == x << k (mod 2^32); fuseOps turns it back on machines where mul is faster.
        if (B.isConst && isPow2(B.c)) return setOp(OP_SHL, A, Opnd::cst(log2u(B.c)));
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
            // An unsigned range that stays inside one half of [0, 2^32) is
            // also a signed interval (the upper half is negative).
            auto toSigned = [](const Range &r, int64_t &lo, int64_t &hi) {
                if (r.hi < 0x80000000ull) { lo = static_cast<int64_t>(r.lo); hi = static_cast<int64_t>(r.hi); return true; }
                if (r.lo >= 0x80000000ull) {
                    lo = static_cast<int64_t>(r.lo) - 0x100000000ll; hi = static_cast<int64_t>(r.hi) - 0x100000000ll;
                    return true;
                }
                return false;
            };
            int64_t alo, ahi, blo, bhi;
            if (toSigned(ra, alo, ahi) && toSigned(rb, blo, bhi)) {
                if (ahi < blo) { *repl = Opnd::cst(1); return true; }
                if (alo >= bhi) { *repl = Opnd::cst(0); return true; }
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
        if (A == B && !A.isConst && rangeOf(f, ds, A, 6).lo > 0) { *repl = Opnd::cst(1); return true; }   // x / x, x != 0
        if (B.isC(0xFFFFFFFFu)) return setOp(OP_SUB, Opnd::cst(0), A);
        if (B.isConst && B.c != 0 && B.c < 0x80000000u && isPow2(B.c)) {
            Range r = rangeOf(f, ds, A, 6);
            if (r.hi < 0x80000000ull) return setOp(OP_SHR, A, Opnd::cst(log2u(B.c)));
        }
        return false;
    case OP_MOD:
        if (B.isC(1) || B.isC(0xFFFFFFFFu)) { *repl = Opnd::cst(0); return true; }
        if (A == B && !A.isConst && rangeOf(f, ds, A, 6).lo > 0) { *repl = Opnd::cst(0); return true; }   // x % x, x != 0
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
        f.rebuildPreds();
        for (int b : d.rpo) {
            BB &B = f.bb[b];
            std::vector<Fact> blockFacts;
            bool factsReady = false;
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
                    // br (x == 0), A, B  ->  br x, B, A  (br tests "not zero")
                    if (x.op == OP_BR && !x.a[0].isConst) {
                        const Inst *c = defInst(f, ds, x.a[0]);
                        if (c && c->op == OP_EQ && c->a[1].isC(0) && !c->a[0].isConst) {
                            x.a[0] = f.resolve(c->a[0]);
                            std::swap(x.tgt[0], x.tgt[1]);
                            again = true;
                        } else if (c && c->op == OP_EQ && c->a[0].isC(0) && !c->a[1].isConst) {
                            x.a[0] = f.resolve(c->a[1]);
                            std::swap(x.tgt[0], x.tgt[1]);
                            again = true;
                        } else {
                            // A condition whose value range excludes 0 is always true.
                            const Range r = rangeOf(f, ds, x.a[0], 6);
                            if (r.lo > 0) { x.a[0] = Opnd::cst(1); again = true; }
                            else if (r.hi == 0) { x.a[0] = Opnd::cst(0); again = true; }
                        }
                    }
                    continue;
                }
                if (x.dst < 0 || f.fwd[x.dst] != Opnd::val(x.dst)) continue;
                // select on a condition that a dominating branch already decided.
                if (x.op == OP_SELECT && !f.resolve(x.a[0]).isConst) {
                    const Opnd c = f.resolve(x.a[0]);
                    if (!factsReady) { blockFacts = chainFacts(f, ds, b, &d.idom); factsReady = true; }
                    int known = -1;
                    for (const Fact &fa : blockFacts)
                        if (fa.v == c.v && fa.other.isC(0) && (fa.rel == 4 || fa.rel == 5)) known = fa.rel == 5 ? 1 : 0;
                    if (known >= 0) {
                        f.replaceAll(x.dst, f.resolve(x.a[known ? 1 : 2]));
                        again = true;
                        continue;
                    }
                }
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

std::vector<BlockMemInfo> memoryFacts(Func &f) {
    f.resolveAll();
    f.rebuildPreds();
    std::vector<DefSite> ds = defSites(f);
    DomInfo dom = computeDominators(f);
    std::vector<BlockMemInfo> out(f.bb.size());
    for (int b = 0; b < static_cast<int>(f.bb.size()); b++) {
        BB &B = f.bb[b];
        if (!B.alive || !dom.reachable(b)) continue;
        std::vector<Opnd> addrs;
        for (const Inst &x : B.insts)
            if (x.op == OP_LOAD || x.op == OP_STORE) addrs.push_back(f.resolve(x.a[0]));
        if (addrs.empty() || addrs.size() > 64) continue;
        BlockMemInfo &mi = out[b];
        const size_t n = addrs.size();
        mi.safe.assign(n, 0);
        mi.disjoint.assign(n, std::vector<char>(n, 0));
        for (size_t i = 0; i < n; i++)
            mi.safe[i] = addrs[i].isConst ? addrs[i].c < kMemWords
                                          : rangeAt(f, ds, addrs[i], b, &dom.idom).hi < kMemWords;
        for (size_t i = 0; i < n; i++)
            for (size_t j = i + 1; j < n; j++)
                mi.disjoint[i][j] = mi.disjoint[j][i] = mustDiffer(f, ds, addrs[i], addrs[j]) ? 1 : 0;
    }
    return out;
}

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

// Loads at merge points: when every predecessor ends with a known value for
// the load's address (the latest load from, or store to, that same address
// on the way up its single-predecessor chain, with no store in between that
// may touch it), the load becomes a phi of those values. Every path has
// already accessed the same address, so no trap can be lost; the address is
// defined in a block that strictly dominates the merge (or is a constant), so
// it names the same word on every incoming edge, including back edges.
bool loadPhis(Func &f) {
    f.resolveAll();
    f.rebuildPreds();
    std::vector<DefSite> ds = defSites(f);
    DomInfo d = computeDominators(f);
    auto sameAddr = [&](Opnd a, Opnd b) {
        a = f.resolve(a); b = f.resolve(b);
        if (a == b) return true;
        AddrForm x = addrForm(f, ds, a), y = addrForm(f, ds, b);
        return x.hasBase == y.hasBase && (!x.hasBase || x.base == y.base) && x.off == y.off;
    };
    // Value of [A] at the end of block p, or a non-value when unknown.
    // stopAt: instruction index limit inside p (p's own size for "end").
    auto availAtEnd = [&](int p, Opnd A, int defBlock, Opnd &out) {
        int blk = p;
        int end = static_cast<int>(f.bb[p].insts.size());
        for (int depth = 0; depth < 8; depth++) {
            const BB &B = f.bb[blk];
            for (int i = end - 1; i >= 0; i--) {
                const Inst &x = B.insts[static_cast<size_t>(i)];
                if (x.op == OP_STORE || x.op == OP_VSTORE) {
                    if (x.op == OP_STORE && sameAddr(x.a[0], A)) { out = f.resolve(x.a[1]); return true; }
                    if (!mustDiffer(f, ds, f.resolve(x.a[0]), A)) return false;
                } else if (x.op == OP_LOAD && x.dst >= 0 && sameAddr(x.a[0], A)) {
                    out = Opnd::val(x.dst);
                    return true;
                }
            }
            if (blk == defBlock || blk == 0) return false;
            if (B.preds.size() != 1) return false;
            blk = B.preds[0];
            end = static_cast<int>(f.bb[blk].insts.size());
        }
        return false;
    };
    bool changed = false;
    for (int b = 0; b < static_cast<int>(f.bb.size()); b++) {
        if (!f.bb[b].alive) continue;
        for (size_t i = 0; i < f.bb[b].insts.size(); i++) {
            const Inst x = f.bb[b].insts[i];
            if (x.op != OP_LOAD || x.dst < 0) continue;
            const Opnd A = f.resolve(x.a[0]);
            // Walk up from the load to the nearest merge block m. Anything that
            // already provides the value on the way is GVN's job; a store that
            // may touch A ends the search.
            int blk = b;
            int end = static_cast<int>(i);
            int m = -1;
            bool fail = false;
            for (int depth = 0; depth < 8 && !fail; depth++) {
                const BB &B = f.bb[blk];
                for (int k = end - 1; k >= 0 && !fail; k--) {
                    const Inst &y = B.insts[static_cast<size_t>(k)];
                    if (y.op == OP_STORE || y.op == OP_VSTORE) {
                        if (!mustDiffer(f, ds, f.resolve(y.a[0]), A)) fail = true;
                    } else if (y.op == OP_LOAD && y.dst >= 0 && sameAddr(y.a[0], A)) {
                        fail = true;   // available already
                    }
                    if (!A.isConst && y.dst == A.v) fail = true;   // A defined below the merge
                }
                if (fail) break;
                if (blk == 0) { fail = true; break; }
                if (B.preds.size() >= 2) { m = blk; break; }
                if (B.preds.size() != 1) { fail = true; break; }
                blk = B.preds[0];
                end = static_cast<int>(f.bb[blk].insts.size());
            }
            if (fail || m < 0) continue;
            int defBlock = -1;
            if (!A.isConst) {
                if (A.v >= static_cast<int>(ds.size())) continue;
                defBlock = ds[A.v].block;
                if (defBlock == m) continue;
                if (defBlock >= 0 && !d.dominates(defBlock, m)) continue;
            }
            std::vector<std::pair<int, Opnd>> ins;
            bool ok = true;
            for (int p : f.bb[m].preds) {
                Opnd v;
                if (!f.bb[p].alive || !availAtEnd(p, A, defBlock, v)) { ok = false; break; }
                if (!v.isConst && v.v == x.dst) { ok = false; break; }
                ins.push_back({p, v});
            }
            if (!ok) continue;
            Phi ph;
            ph.dst = f.newVal();
            ph.in = ins;
            f.bb[m].phis.push_back(ph);
            f.replaceAll(x.dst, Opnd::val(ph.dst));
            Inst &y = f.bb[b].insts[i];
            y.op = OP_MOV;
            y.n = 1;
            y.a[0] = Opnd::val(ph.dst);
            changed = true;
            ds = defSites(f);
        }
    }
    return changed;
}

// Conditional stores whose old values are known: in a triangle
//   P: ... br c, T, J      T: pure work; store a1, x1; ...; jmp J
// where every ai is defined above P (or constant), the ai are pairwise
// different words, and the value of each [ai] at the end of P is known
// (the latest load from or store to ai, with nothing in between that may
// touch it), T's work moves into P and each store becomes
//   store ai, select(c, xi, old_i)
// On the path that skipped T this rewrites a word with its current value; the
// word was already accessed on that path, so no new trap is possible.
bool storeSelect(Func &f) {
    f.resolveAll();
    f.rebuildPreds();
    std::vector<DefSite> ds = defSites(f);
    DomInfo d = computeDominators(f);
    auto sameAddr = [&](Opnd a, Opnd b) {
        a = f.resolve(a); b = f.resolve(b);
        if (a == b) return true;
        AddrForm x = addrForm(f, ds, a), y = addrForm(f, ds, b);
        return x.hasBase == y.hasBase && (!x.hasBase || x.base == y.base) && x.off == y.off;
    };
    auto availAtEnd = [&](int p, Opnd A, int defBlock, Opnd &out) {
        int blk = p;
        int end = static_cast<int>(f.bb[p].insts.size()) - 1;   // skip the terminator
        for (int depth = 0; depth < 8; depth++) {
            const BB &B = f.bb[blk];
            for (int i = end - 1; i >= 0; i--) {
                const Inst &x = B.insts[static_cast<size_t>(i)];
                if (x.op == OP_STORE || x.op == OP_VSTORE) {
                    if (x.op == OP_STORE && sameAddr(x.a[0], A)) { out = f.resolve(x.a[1]); return true; }
                    if (!mustDiffer(f, ds, f.resolve(x.a[0]), A)) return false;
                } else if (x.op == OP_LOAD && x.dst >= 0 && sameAddr(x.a[0], A)) {
                    out = Opnd::val(x.dst);
                    return true;
                }
            }
            if (blk == defBlock || blk == 0) return false;
            if (B.preds.size() != 1) return false;
            blk = B.preds[0];
            end = static_cast<int>(f.bb[blk].insts.size());
        }
        return false;
    };
    bool changed = false;
    for (int pb = 0; pb < static_cast<int>(f.bb.size()); pb++) {
        BB &P = f.bb[pb];
        if (!P.alive || P.term().op != OP_BR || P.term().a[0].isConst) continue;
        for (int side = 0; side < 2; side++) {
            const int t = P.term().tgt[side], j = P.term().tgt[1 - side];
            if (t == j || t == pb || t == 0) continue;
            const BB &T = f.bb[t];
            if (!T.alive || T.preds.size() != 1 || !T.phis.empty()) continue;
            // T's leading run of pure, non-trapping work and plain stores moves
            // up; the rest of T (if any) stays where it is.
            std::vector<size_t> stores;
            bool ok = true;
            size_t prefix = 0;
            while (prefix + 1 < T.insts.size()) {
                const Inst &x = T.insts[prefix];
                if (x.op == OP_STORE) { stores.push_back(prefix); prefix++; continue; }
                if (x.op == OP_LOAD || x.op == OP_VLOAD || x.op == OP_VSTORE || x.dst < 0 || mayTrap(f, x)) break;
                prefix++;
            }
            while (!stores.empty() && stores.back() + 1 != prefix) prefix--;   // end the run at its last store
            const bool whole = prefix + 1 == T.insts.size() && T.term().op == OP_JMP && T.term().tgt[0] == j;
            if (stores.empty() || stores.size() > 4) continue;
            std::vector<Opnd> olds;
            for (size_t si = 0; si < stores.size() && ok; si++) {
                const Opnd A = f.resolve(T.insts[stores[si]].a[0]);
                int defBlock = -1;
                if (!A.isConst) {
                    defBlock = A.v < static_cast<int>(ds.size()) ? ds[A.v].block : -2;
                    if (defBlock == -2 || defBlock == t || (defBlock >= 0 && !d.dominates(defBlock, pb))) { ok = false; break; }
                }
                for (size_t sj = 0; sj < si; sj++)
                    if (!mustDiffer(f, ds, f.resolve(T.insts[stores[sj]].a[0]), A)) ok = false;
                Opnd old;
                if (ok && !availAtEnd(pb, A, defBlock, old)) ok = false;
                olds.push_back(old);
            }
            if (!ok) continue;
            const Opnd c = f.resolve(P.term().a[0]);
            std::vector<Inst> moved;
            for (size_t i = 0; i < prefix; i++) {
                const Inst &x = f.bb[t].insts[i];
                if (x.op != OP_STORE) { moved.push_back(x); continue; }
                const size_t si = static_cast<size_t>(std::find(stores.begin(), stores.end(), i) - stores.begin());
                Inst sel;
                sel.op = OP_SELECT; sel.dst = f.newVal(); sel.n = 3; sel.a[0] = c;
                sel.a[1] = side == 0 ? f.resolve(x.a[1]) : olds[si];
                sel.a[2] = side == 0 ? olds[si] : f.resolve(x.a[1]);
                Inst st = x;
                st.a[1] = Opnd::val(sel.dst);
                moved.push_back(sel);
                moved.push_back(st);
            }
            if (!whole) {
                f.bb[t].insts.erase(f.bb[t].insts.begin(), f.bb[t].insts.begin() + static_cast<long>(prefix));
                auto &pi = f.bb[pb].insts;
                pi.insert(pi.end() - 1, moved.begin(), moved.end());
                changed = true;
                ds = defSites(f);
                break;
            }
            // J's phis: the inputs from P and T merge into one select in P.
            for (Phi &ph : f.bb[j].phis) {
                Opnd fromP, fromT;
                bool hp = false, ht = false;
                for (auto &in : ph.in) {
                    if (in.first == pb) { fromP = f.resolve(in.second); hp = true; }
                    if (in.first == t) { fromT = f.resolve(in.second); ht = true; }
                }
                if (!hp || !ht) continue;
                Opnd merged = fromP;
                if (!(fromP == fromT)) {
                    Inst sel;
                    sel.op = OP_SELECT; sel.dst = f.newVal(); sel.n = 3; sel.a[0] = c;
                    sel.a[1] = side == 0 ? fromT : fromP;
                    sel.a[2] = side == 0 ? fromP : fromT;
                    moved.push_back(sel);
                    merged = Opnd::val(sel.dst);
                }
                std::vector<std::pair<int, Opnd>> keep;
                for (auto &in : ph.in) {
                    if (in.first == t) continue;
                    if (in.first == pb) keep.push_back({pb, merged});
                    else keep.push_back(in);
                }
                ph.in.swap(keep);
            }
            f.bb[t].insts.clear();
            f.bb[t].phis.clear();
            f.bb[t].alive = false;
            auto &pi = f.bb[pb].insts;
            pi.insert(pi.end() - 1, moved.begin(), moved.end());
            Inst &term = f.bb[pb].term();
            term.op = OP_JMP;
            term.n = 0;
            term.tgt[0] = j;
            term.tgt[1] = -1;
            f.rebuildPreds();
            changed = true;
            ds = defSites(f);
            d = computeDominators(f);
            break;
        }
    }
    return changed;
}

// A return block whose phi inputs from some predecessor are all constants gets
// a private copy for that edge, with the constants substituted; constant
// folding then reduces the copy (often to "ret C"), and the predecessor no
// longer needs to keep those values alive. The block ends in ret, so its
// values are not used anywhere else. Pure copying of executed instructions.
bool dupConstReturns(Func &f, int maxSize, int maxNew) {
    f.resolveAll();
    f.rebuildPreds();
    bool changed = false;
    int budget = maxNew;
    const int nb = static_cast<int>(f.bb.size());
    for (int j = 1; j < nb; j++) {
        if (!f.bb[j].alive || f.bb[j].phis.empty() || f.bb[j].term().op != OP_RET) continue;
        if (static_cast<int>(f.bb[j].insts.size()) > maxSize) continue;
        const std::vector<int> preds = f.bb[j].preds;
        if (preds.size() < 2) continue;
        for (int p : preds) {
            if (budget < static_cast<int>(f.bb[j].insts.size())) break;
            if (p == j || !f.bb[p].alive) continue;
            bool allConst = true;
            int count = 0;
            for (const Phi &ph : f.bb[j].phis)
                for (const auto &in : ph.in)
                    if (in.first == p) { count++; if (!f.resolve(in.second).isConst) allConst = false; }
            if (!allConst || count != static_cast<int>(f.bb[j].phis.size())) continue;
            // Edge counted once only (a branch with both targets j is left alone).
            const Inst &pt = f.bb[p].term();
            if (pt.op == OP_BR && pt.tgt[0] == j && pt.tgt[1] == j) continue;
            std::unordered_map<int, Opnd> map;
            for (const Phi &ph : f.bb[j].phis)
                for (const auto &in : ph.in)
                    if (in.first == p) map[ph.dst] = f.resolve(in.second);
            BB copy;
            copy.label.clear();
            for (const Inst &x0 : f.bb[j].insts) {
                Inst x = x0;
                for (int a = 0; a < x.n; a++) {
                    Opnd o = f.resolve(x.a[a]);
                    if (!o.isConst) { auto it = map.find(o.v); if (it != map.end()) o = it->second; }
                    x.a[a] = o;
                }
                if (x.dst >= 0) { Val nv = f.newVal(); map[x0.dst] = Opnd::val(nv); x.dst = nv; }
                copy.insts.push_back(x);
            }
            const int nbk = static_cast<int>(f.bb.size());
            f.bb.push_back(copy);
            Inst &t = f.bb[p].term();
            for (int k = 0; k < 2; k++) if (t.tgt[k] == j) t.tgt[k] = nbk;
            for (Phi &ph : f.bb[j].phis) {
                std::vector<std::pair<int, Opnd>> keep;
                for (auto &in : ph.in) if (in.first != p) keep.push_back(in);
                ph.in.swap(keep);
            }
            budget -= static_cast<int>(f.bb[j].insts.size());
            changed = true;
        }
    }
    if (changed) f.rebuildPreds();
    return changed;
}

// Forwarding through stores that may alias: in a block,
//   ... [A] known as v0 ...; store B1, w1; ...; load A
// where Bi may or may not equal A: the load's value is
//   select(A == Bk, wk, ... select(A == B1, w1, v0))
// (later stores win). At most two such stores; no volatile access between.
// A was already accessed, so dropping the load cannot lose a trap.
bool aliasForward(Func &f) {
    f.resolveAll();
    std::vector<DefSite> ds = defSites(f);
    auto sameAddr = [&](Opnd a, Opnd b) {
        a = f.resolve(a); b = f.resolve(b);
        if (a == b) return true;
        AddrForm x = addrForm(f, ds, a), y = addrForm(f, ds, b);
        return x.hasBase == y.hasBase && (!x.hasBase || x.base == y.base) && x.off == y.off;
    };
    bool changed = false;
    for (int b = 0; b < static_cast<int>(f.bb.size()); b++) {
        if (!f.bb[b].alive) continue;
        for (size_t i = 0; i < f.bb[b].insts.size(); i++) {
            const Inst x = f.bb[b].insts[i];
            if (x.op != OP_LOAD || x.dst < 0) continue;
            const Opnd A = f.resolve(x.a[0]);
            std::vector<std::pair<Opnd, Opnd>> between;   // (address, value), newest first
            Opnd v0;
            bool found = false, fail = false;
            for (size_t k = i; k-- > 0 && !found && !fail;) {
                const Inst &y = f.bb[b].insts[k];
                if (y.op == OP_VSTORE || y.op == OP_VLOAD) { fail = true; break; }
                if (y.op == OP_STORE) {
                    const Opnd B = f.resolve(y.a[0]);
                    if (sameAddr(B, A)) { v0 = f.resolve(y.a[1]); found = true; break; }
                    if (mustDiffer(f, ds, B, A)) continue;
                    if (between.size() >= 2) { fail = true; break; }
                    between.push_back({B, f.resolve(y.a[1])});
                } else if (y.op == OP_LOAD && y.dst >= 0 && sameAddr(y.a[0], A)) {
                    v0 = Opnd::val(y.dst); found = true; break;
                }
            }
            if (!found || fail || between.empty()) continue;
            std::vector<Inst> pre;
            Opnd v = v0;
            for (size_t q = between.size(); q-- > 0;) {   // oldest first
                Inst e; e.op = OP_EQ; e.dst = f.newVal(); e.n = 2; e.a[0] = A; e.a[1] = between[q].first;
                Inst sl; sl.op = OP_SELECT; sl.dst = f.newVal(); sl.n = 3;
                sl.a[0] = Opnd::val(e.dst); sl.a[1] = between[q].second; sl.a[2] = v;
                pre.push_back(e); pre.push_back(sl);
                v = Opnd::val(sl.dst);
            }
            f.replaceAll(x.dst, v);
            Inst &y = f.bb[b].insts[i];
            y.op = OP_MOV; y.n = 1; y.a[0] = v;
            auto &ins = f.bb[b].insts;
            ins.insert(ins.begin() + static_cast<long>(i), pre.begin(), pre.end());
            i += pre.size();
            ds = defSites(f);
            changed = true;
        }
    }
    return changed;
}

bool dce(Func &f) {
    f.resolveAll();
    std::vector<DefSite> ds = defSites(f);
    std::vector<char> live(f.nvals, 0);
    std::vector<Val> work;
    auto markOp = [&](Opnd o) {
        if (!o.isConst && !live[o.v]) { live[o.v] = 1; work.push_back(o.v); }
    };
    f.rebuildPreds();
    for (BB &B : f.bb) {
        if (!B.alive) continue;
        const int bi = static_cast<int>(&B - &f.bb[0]);
        for (Inst &x : B.insts) {
            bool root = x.dst < 0 || x.op == OP_VLOAD || mayTrapWith(f, ds, x, bi);
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
    f.rebuildPreds();
    for (BB &B : f.bb) {
        if (!B.alive) continue;
        const int bi = static_cast<int>(&B - &f.bb[0]);
        std::vector<Opnd> overwritten;   // addresses stored later in this block, unobserved since
        std::vector<char> kill(B.insts.size(), 0);
        for (int i = static_cast<int>(B.insts.size()) - 1; i >= 0; i--) {
            const Inst &x = B.insts[i];
            if (x.op == OP_STORE) {
                // Only a store that cannot trap is a guaranteed overwrite; a store
                // that may trap is a point where earlier stores become visible.
                bool trapping = mayTrapWith(f, ds, x, bi);
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
                if (mayTrapWith(f, ds, x, bi)) overwritten.clear();
                continue;
            }
            if (mayTrapWith(f, ds, x, bi)) overwritten.clear();
        }
        if (changed) {
            std::vector<Inst> out;
            for (size_t i = 0; i < B.insts.size(); i++) if (!kill[i]) out.push_back(B.insts[i]);
            B.insts.swap(out);
        }
    }
    return changed;
}

// ---------------------------------------------------------------------------
// Loop-invariant code motion
// ---------------------------------------------------------------------------

// A preheader for loop header h whose only outside predecessor is `outside`:
// that block itself if it falls into h alone, otherwise a new block on the edge.
// Predecessor lists are updated in place (no global rebuild).
static int makePreheader(Func &f, int h, int outside) {
    int s[2];
    if (f.succs(outside, s) == 1) return outside;
    int p = static_cast<int>(f.bb.size());
    f.bb.emplace_back();
    BB &P = f.bb[p];
    Inst j;
    j.op = OP_JMP;
    j.tgt[0] = h;
    P.insts.push_back(j);
    P.freq = f.bb[outside].freq;
    P.loopDepth = f.bb[outside].loopDepth;
    P.preds.push_back(outside);
    Inst &t = f.bb[outside].term();
    for (int k = 0; k < 2; k++) if (t.tgt[k] == h) t.tgt[k] = p;
    for (Phi &ph : f.bb[h].phis)
        for (auto &in : ph.in) if (in.first == outside) in.first = p;
    for (int &q : f.bb[h].preds) if (q == outside) q = p;
    return p;
}

// Is operand o provably non-zero on the edge from -> to? (Facts of the
// branches that dominate `from`, plus the edge's own branch.)
static bool nonZeroOnEdge(const Func &f, const std::vector<DefSite> &ds, Opnd o, int from, int to,
                          const std::vector<int> &idom) {
    if (o.isConst) return o.c != 0;
    std::vector<Fact> facts = chainFacts(f, ds, from, &idom);
    const Inst &t = f.bb[from].term();
    if (t.op == OP_BR && t.tgt[0] != t.tgt[1] && (t.tgt[0] == to || t.tgt[1] == to))
        factsFromCond(f, ds, t.a[0], t.tgt[0] == to, facts, 0);
    for (const Fact &fa : facts)
        if (fa.v == o.v && fa.rel == 5 && fa.other.isConst && fa.other.c == 0) return true;
    auto other = [&](Opnd x) -> SR { return x.isConst ? sOfConst(x.c) : fromRange(rangeOf(f, ds, x, 6)); };
    SR r = refine(fromRange(rangeOf(f, ds, o, 8)), o.v, facts, other);
    return !r.empty() && (r.lo > 0 || r.hi < 0);
}

bool licm(Func &f) {
    f.resolveAll();
    f.rebuildPreds();
    DomInfo d = computeDominators(f);
    LoopInfo li = computeLoops(f, d);
    std::vector<bool> irr = irreducibleBlocks(f, d);
    std::vector<int> order(li.loops.size());
    for (size_t i = 0; i < order.size(); i++) order[i] = static_cast<int>(i);
    std::sort(order.begin(), order.end(), [&](int a, int b) { return li.loops[a].depth > li.loops[b].depth; });
    std::vector<DefSite> ds = defSites(f);   // may go stale; defInst() then answers "unknown"
    std::vector<int> defBlock(f.nvals, -1);
    for (int v = 0; v < f.nvals; v++) defBlock[v] = ds[v].block;
    // Preheaders created for inner loops belong to the enclosing loops.
    std::vector<std::vector<int>> extraBlocks(li.loops.size());
    bool changed = false;
    for (int l : order) {
        const LoopInfo::Loop L = li.loops[l];
        const int h = L.header;
        if (irr[h]) continue;
        auto inL = [&](int b) { return b >= 0 && li.inLoop(b, l); };
        std::vector<int> outside;
        for (int p : f.bb[h].preds) if (!inL(p)) outside.push_back(p);
        if (outside.size() != 1) continue;
        std::vector<int> blocks = L.blocks;
        blocks.insert(blocks.end(), extraBlocks[l].begin(), extraBlocks[l].end());
        std::vector<Opnd> loopStores;
        for (int b : blocks)
            for (const Inst &x : f.bb[b].insts)
                if (x.op == OP_STORE) loopStores.push_back(x.a[0]);
        auto invariant = [&](Opnd o) {
            return o.isConst || defBlock[o.v] < 0 || !inL(defBlock[o.v]);
        };
        auto hoistable = [&](const Inst &x) {
            if (x.dst < 0) return false;
            if (isPure(x.op)) return true;
            if (x.op == OP_DIV || x.op == OP_MOD)
                return rangeOf(f, ds, x.a[1], 8).lo >= 1 || nonZeroOnEdge(f, ds, x.a[1], outside[0], h, d.idom);
            if (x.op == OP_LOAD) {
                if (rangeOf(f, ds, x.a[0], 8).hi >= kMemWords) return false;   // may trap
                for (const Opnd &st : loopStores)
                    if (!mustDiffer(f, ds, st, x.a[0])) return false;
                return true;
            }
            return false;
        };
        int pre = -1;
        bool any = true;
        while (any) {
            any = false;
            for (int b : blocks) {
                // f.bb may grow (preheader), so never hold a reference across the loop body.
                for (size_t i = 0; i + 1 < f.bb[b].insts.size();) {
                    Inst x = f.bb[b].insts[i];
                    bool ok = hoistable(x);
                    for (int a = 0; ok && a < x.n; a++) ok = invariant(x.a[a]);
                    if (!ok) { i++; continue; }
                    if (pre < 0) {
                        pre = makePreheader(f, h, outside[0]);
                        if (pre >= static_cast<int>(li.innermost.size())) {
                            // New block: it lies in the loops that enclose L.
                            li.innermost.push_back(L.parent);
                            li.depth.push_back(L.parent >= 0 ? li.loops[L.parent].depth : 0);
                            for (int a = L.parent; a >= 0; a = li.loops[a].parent) extraBlocks[a].push_back(pre);
                        }
                    }
                    BB &P = f.bb[pre];
                    P.insts.insert(P.insts.end() - 1, x);
                    f.bb[b].insts.erase(f.bb[b].insts.begin() + i);
                    defBlock[x.dst] = pre;
                    ds[x.dst] = DefSite{pre, static_cast<int>(P.insts.size()) - 2, false};
                    any = true;
                    changed = true;
                }
            }
        }
    }
    if (changed) f.rebuildPreds();
    return changed;
}

// ---------------------------------------------------------------------------
// Speculation: move pure, non-trapping work from a block into its only
// predecessor (which ends in a branch). In SSA this never changes a result:
// the hoisted value is simply computed earlier, also on the other path where
// nobody uses it. It gives the per-block scheduler independent work to fill
// latency gaps (for example the next unrolled iteration's division).
// ---------------------------------------------------------------------------

bool speculate(Func &f, int budgetPerEdge, bool maskLoads) {
    f.resolveAll();
    f.rebuildPreds();
    std::vector<DefSite> ds = defSites(f);
    bool changed = false;
    DomInfo d = computeDominators(f);
    // Walk blocks in reverse RPO so work can move up a chain of blocks step by step.
    for (int idx = static_cast<int>(d.rpo.size()) - 1; idx >= 0; idx--) {
        const int s = d.rpo[idx];
        BB &S = f.bb[s];
        if (s == 0 || S.preds.size() != 1 || !S.phis.empty()) continue;
        const int p = S.preds[0];
        if (p == s || f.bb[p].term().op != OP_BR) continue;
        int moved = 0;
        bool storeSeen = false;
        std::vector<Opnd> storeAddrs;   // stores of S passed so far (a load may cross ones it provably misses)
        bool unknownEffect = false;
        std::vector<char> definedHere(f.nvals, 0);
        for (const Inst &x : S.insts) if (x.dst >= 0) definedHere[x.dst] = 1;
        for (size_t i = 0; i + 1 < S.insts.size() && moved < budgetPerEdge;) {
            Inst x = S.insts[i];
            bool ok = x.dst >= 0;
            // A load whose address is in memory only on this path (branch facts)
            // moves up with its address masked to 12 bits: always a valid word,
            // and the same word whenever the original load would have run.
            bool mask = false;
            if (ok) {
                if (isPure(x.op)) ok = true;
                else if (x.op == OP_DIV || x.op == OP_MOD) ok = rangeOf(f, ds, x.a[1], 8).lo >= 1;
                else if (x.op == OP_LOAD) {
                    bool clear = !storeSeen;
                    if (!clear && maskLoads && !unknownEffect) {
                        clear = true;
                        for (Opnd sa : storeAddrs) if (!mustDiffer(f, ds, sa, f.resolve(x.a[0]))) clear = false;
                    }
                    ok = clear && rangeOf(f, ds, x.a[0], 8).hi < kMemWords;
                    if (!ok && maskLoads && clear && !x.a[0].isConst &&
                        rangeAt(f, ds, x.a[0], s, &d.idom).hi < kMemWords) ok = mask = true;
                }
                else ok = false;
            }
            for (int a = 0; ok && a < x.n; a++)
                if (!x.a[a].isConst && x.a[a].v < static_cast<int>(definedHere.size()) && definedHere[x.a[a].v]) ok = false;
            if (x.op == OP_STORE) { storeSeen = true; storeAddrs.push_back(f.resolve(x.a[0])); }
            if (x.op == OP_VSTORE || x.op == OP_VLOAD) { storeSeen = true; unknownEffect = true; }
            if (!ok) { i++; continue; }
            BB &P = f.bb[p];
            if (mask) {
                Inst m;
                m.op = OP_AND; m.dst = f.newVal(); m.n = 2; m.a[0] = x.a[0]; m.a[1] = Opnd::cst(kMemWords - 1);
                P.insts.insert(P.insts.end() - 1, m);
                x.a[0] = Opnd::val(m.dst);
                definedHere.resize(f.nvals, 0);
                ds.resize(f.nvals);
                ds[m.dst] = DefSite{p, static_cast<int>(P.insts.size()) - 2, false};
            }
            P.insts.insert(P.insts.end() - 1, x);
            f.bb[s].insts.erase(f.bb[s].insts.begin() + i);
            definedHere[x.dst] = 0;
            ds[x.dst] = DefSite{p, static_cast<int>(P.insts.size()) - 2, false};
            moved++;
            changed = true;
        }
    }
    return changed;
}

// ---------------------------------------------------------------------------
// Recurrences: values on a cycle of the SSA graph (through loop phis). Their
// dependence chain bounds how fast a loop iteration can go.
// ---------------------------------------------------------------------------

static std::vector<int> recurrenceIds(const Func &f) {
    const int nv = f.nvals;
    std::vector<std::vector<int>> succ(nv);   // operand -> user value
    for (const BB &B : f.bb) {
        if (!B.alive) continue;
        for (const Phi &p : B.phis)
            for (auto &in : p.in) if (!in.second.isConst) succ[in.second.v].push_back(p.dst);
        for (const Inst &x : B.insts)
            if (x.dst >= 0)
                for (int a = 0; a < x.n; a++) if (!x.a[a].isConst) succ[x.a[a].v].push_back(x.dst);
    }
    // Tarjan, iterative.
    std::vector<int> index(nv, -1), low(nv, 0), comp(nv, -1);
    std::vector<char> onStack(nv, 0);
    std::vector<int> st, sccSize;
    int counter = 0, ncomp = 0;
    struct Frame { int v; size_t i; };
    for (int s = 0; s < nv; s++) {
        if (index[s] >= 0) continue;
        std::vector<Frame> call{{s, 0}};
        index[s] = low[s] = counter++;
        st.push_back(s);
        onStack[s] = 1;
        while (!call.empty()) {
            Frame &fr = call.back();
            int v = fr.v;
            if (fr.i < succ[v].size()) {
                int w = succ[v][fr.i++];
                if (index[w] < 0) {
                    index[w] = low[w] = counter++;
                    st.push_back(w);
                    onStack[w] = 1;
                    call.push_back({w, 0});
                } else if (onStack[w]) {
                    low[v] = std::min(low[v], index[w]);
                }
            } else {
                if (low[v] == index[v]) {
                    int size = 0;
                    while (true) {
                        int w = st.back();
                        st.pop_back();
                        onStack[w] = 0;
                        comp[w] = ncomp;
                        size++;
                        if (w == v) break;
                    }
                    sccSize.push_back(size);
                    ncomp++;
                }
                call.pop_back();
                if (!call.empty()) low[call.back().v] = std::min(low[call.back().v], low[v]);
            }
        }
    }
    std::vector<int> rec(nv, -1);
    for (int v = 0; v < nv; v++) if (comp[v] >= 0 && sccSize[comp[v]] > 1) rec[v] = comp[v];
    return rec;
}

// Reassociation: in a chain of adds that is part of a loop recurrence, add the
// recurrence value last, so the loop-carried dependence is one add long and the
// rest of the chain can run in parallel with it (32-bit addition wraps, so it is
// associative and commutative and any order gives the same result).
bool reassociate(Func &f) {
    f.resolveAll();
    std::vector<int> rec = recurrenceIds(f);
    std::vector<DefSite> ds = defSites(f);
    std::vector<int> uses(f.nvals, 0);
    for (BB &B : f.bb) {
        if (!B.alive) continue;
        for (Phi &p : B.phis) for (auto &in : p.in) if (!in.second.isConst) uses[in.second.v]++;
        for (Inst &x : B.insts) for (int a = 0; a < x.n; a++) if (!x.a[a].isConst) uses[x.a[a].v]++;
    }
    bool changed = false;
    for (int b = 0; b < static_cast<int>(f.bb.size()); b++) {
        if (!f.bb[b].alive) continue;
        // Plan all rewrites of this block against the unchanged block, then apply
        // them back to front (trees of single-use adds never overlap).
        std::vector<std::pair<size_t, std::vector<Inst>>> inserts;
        const size_t nins = f.bb[b].insts.size();
        for (size_t i = 0; i < nins; i++) {
            Inst root = f.bb[b].insts[i];
            if (root.op != OP_ADD || root.dst >= static_cast<int>(rec.size()) || rec[root.dst] < 0) continue;
            const int cyc = rec[root.dst];
            std::vector<Opnd> leaves;
            std::vector<Opnd> work{root.a[0], root.a[1]};
            int inner = 0;
            while (!work.empty()) {
                Opnd o = work.back();
                work.pop_back();
                const Inst *d = defInst(f, ds, o);
                if (d && d->op == OP_ADD && uses[o.v] == 1 && ds[o.v].block == b && rec[o.v] == cyc && inner < 16) {
                    inner++;
                    work.push_back(d->a[0]);
                    work.push_back(d->a[1]);
                } else {
                    leaves.push_back(o);
                }
            }
            if (inner == 0) continue;
            std::vector<Opnd> carried, rest;
            uint32_t constSum = 0;
            bool haveConst = false;
            for (Opnd o : leaves) {
                if (o.isConst) { constSum += o.c; haveConst = true; }
                else if (o.v < static_cast<int>(rec.size()) && rec[o.v] == cyc) carried.push_back(o);
                else rest.push_back(o);
            }
            if (carried.size() != 1 || rest.empty()) continue;
            if (haveConst) rest.push_back(Opnd::cst(constSum));
            std::vector<Inst> pre;
            Opnd acc = rest[0];
            for (size_t k = 1; k < rest.size(); k++) {
                Inst a;
                a.op = OP_ADD;
                a.dst = f.newVal();
                a.n = 2;
                a.a[0] = acc;
                a.a[1] = rest[k];
                pre.push_back(a);
                acc = Opnd::val(a.dst);
            }
            Inst &r = f.bb[b].insts[i];
            r.a[0] = carried[0];
            r.a[1] = acc;
            if (!pre.empty()) inserts.push_back({i, pre});
            changed = true;
        }
        // Loop-carried min/max chains: select(lt(p, q), q, p) is max(p, q) and
        // select(lt(p, q), p, q) is min(p, q) (signed). Both are associative and
        // commutative and always return one of their inputs, so a chain
        // acc' = max(max(max(acc, x0), x1), x2) has the same value as
        // max(acc, max(max(x0, x1), x2)); the new form keeps one step on the
        // loop-carried path and puts the others in a balanced tree.
        // kind: 1 = max, 2 = min, 0 = neither. condAt receives the lt's index.
        auto mmKind = [&](const Inst &x, const Inst **cond) -> int {
            if (x.op != OP_SELECT || x.dst < 0 || x.a[0].isConst) return 0;
            const Inst *c = defInst(f, ds, x.a[0]);
            if (!c || c->op != OP_LT || uses[x.a[0].v] != 1 || ds[x.a[0].v].block != b) return 0;
            if (c->a[0] == c->a[1]) return 0;
            *cond = c;
            if (x.a[1] == c->a[1] && x.a[2] == c->a[0]) return 1;
            if (x.a[1] == c->a[0] && x.a[2] == c->a[1]) return 2;
            return 0;
        };
        if (inserts.empty()) {
            std::vector<std::pair<size_t, std::vector<Inst>>> mmInserts;
            // Back to front, so the first root found is the end of its chain.
            for (size_t i = f.bb[b].insts.size(); i-- > 0;) {
                const Inst root = f.bb[b].insts[i];
                const Inst *rc = nullptr;
                const int kind = mmKind(root, &rc);
                if (!kind || root.dst >= static_cast<int>(rec.size()) || rec[root.dst] < 0) continue;
                const int cyc = rec[root.dst];
                const int condVal = root.a[0].v;
                std::vector<Opnd> leaves;
                std::vector<Opnd> work{rc->a[0], rc->a[1]};
                int inner = 0;
                while (!work.empty()) {
                    Opnd o = work.back();
                    work.pop_back();
                    const Inst *d = o.isConst ? nullptr : defInst(f, ds, o);
                    const Inst *dc = nullptr;
                    if (d && ds[o.v].block == b && uses[o.v] == 2 && o.v < static_cast<int>(rec.size()) && rec[o.v] == cyc &&
                        inner < 16 && mmKind(*d, &dc) == kind) {
                        inner++;
                        work.push_back(dc->a[0]);
                        work.push_back(dc->a[1]);
                    } else {
                        leaves.push_back(o);
                    }
                }
                if (inner == 0) continue;
                std::vector<Opnd> carried, rest;
                for (Opnd o : leaves) {
                    if (!o.isConst && o.v < static_cast<int>(rec.size()) && rec[o.v] == cyc) carried.push_back(o);
                    else rest.push_back(o);
                }
                if (carried.size() != 1 || rest.empty()) continue;
                // Index of the root's lt in this block (it must come before the root).
                size_t condAt = i;
                for (size_t j = 0; j < i; j++)
                    if (f.bb[b].insts[j].dst == condVal) { condAt = j; break; }
                if (condAt == i) continue;
                std::vector<Inst> pre;
                auto emit = [&](Opnd p, Opnd q) {
                    Inst c;
                    c.op = OP_LT; c.dst = f.newVal(); c.n = 2; c.a[0] = p; c.a[1] = q;
                    Inst sel;
                    sel.op = OP_SELECT; sel.dst = f.newVal(); sel.n = 3; sel.a[0] = Opnd::val(c.dst);
                    sel.a[1] = kind == 1 ? q : p;
                    sel.a[2] = kind == 1 ? p : q;
                    pre.push_back(c);
                    pre.push_back(sel);
                    return Opnd::val(sel.dst);
                };
                std::vector<Opnd> level = rest;
                while (level.size() > 1) {
                    std::vector<Opnd> next;
                    for (size_t k = 0; k + 1 < level.size(); k += 2) next.push_back(emit(level[k], level[k + 1]));
                    if (level.size() % 2) next.push_back(level.back());
                    level.swap(next);
                }
                const Opnd t = level[0];
                Inst &rcm = f.bb[b].insts[condAt];
                rcm.a[0] = carried[0];
                rcm.a[1] = t;
                Inst &r = f.bb[b].insts[i];
                r.a[1] = kind == 1 ? t : carried[0];
                r.a[2] = kind == 1 ? carried[0] : t;
                if (!pre.empty()) mmInserts.push_back({condAt, pre});
                changed = true;
                break;   // one chain per block per run; ds/uses are stale after this
            }
            for (auto it = mmInserts.rbegin(); it != mmInserts.rend(); ++it) {
                auto &ins = f.bb[b].insts;
                ins.insert(ins.begin() + static_cast<long>(it->first), it->second.begin(), it->second.end());
            }
            if (!mmInserts.empty()) {
                ds = defSites(f);
                uses.resize(f.nvals, 0);
            }
        }
        for (auto it = inserts.rbegin(); it != inserts.rend(); ++it) {
            auto &ins = f.bb[b].insts;
            ins.insert(ins.begin() + it->first, it->second.begin(), it->second.end());
        }
        if (!inserts.empty()) {
            ds = defSites(f);
            uses.resize(f.nvals, 0);
        }
    }
    return changed;
}

// Horner chains h' = h * x + c (32-bit wrapping arithmetic is a commutative
// ring, so any regrouping of the polynomial gives the same bits). A chain of
// n steps has n serial multiply-adds; split it into k interleaved chains in
// y = x^k and combine them at the end:
//   P = sum_j x^j * C_j(y), C_j holds the coefficients whose power is j mod k.
// The critical path drops from about n to about n/k + log2(k) multiply-adds.
bool hornerSplit(Func &f, int registers) {
    f.resolveAll();
    const int nv0 = f.nvals;   // values made here are never split again
    std::vector<DefSite> ds = defSites(f);
    std::vector<int> uses(f.nvals, 0);
    for (BB &B : f.bb) {
        if (!B.alive) continue;
        for (Phi &p : B.phis) for (auto &in : p.in) if (!in.second.isConst) uses[in.second.v]++;
        for (Inst &x : B.insts) for (int a = 0; a < x.n; a++) if (!x.a[a].isConst) uses[x.a[a].v]++;
    }
    bool changed = false;
    for (int b = 0; b < static_cast<int>(f.bb.size()); b++) {
      for (int again = 0; again < 8; again++) {
        bool here = false;
        if (!f.bb[b].alive) continue;
        std::vector<char> consumed(f.bb[b].insts.size(), 0);
        // index of a value's defining instruction in this block, or -1
        auto localDef = [&](Opnd o) -> int {
            if (o.isConst || o.v >= static_cast<int>(ds.size()) || ds[o.v].block != b) return -1;
            const Inst *d = defInst(f, ds, o);
            if (!d) return -1;
            return static_cast<int>(d - &f.bb[b].insts[0]);
        };
        // One step: add(mul(h, x), c) with the mul used once. Returns false if not.
        auto step = [&](int i, Opnd &h, Opnd &x, Opnd &c, int &mulAt, bool xKnown) {
            const Inst &a = f.bb[b].insts[static_cast<size_t>(i)];
            if (a.op != OP_ADD || a.dst < 0) return false;
            for (int side = 0; side < 2; side++) {
                Opnd m = a.a[side];
                int mi = localDef(m);
                if (mi < 0 || uses[m.v] != 1) continue;
                const Inst &mu = f.bb[b].insts[static_cast<size_t>(mi)];
                if (mu.op != OP_MUL || mu.dst >= nv0) continue;
                for (int xs = 0; xs < 2; xs++) {
                    Opnd cx = mu.a[xs], ch = mu.a[1 - xs];
                    if (xKnown && !(cx == x)) continue;
                    if (!xKnown) {
                        // Prefer the side whose other operand continues the chain.
                        int hi = localDef(ch);
                        Opnd h2, x2, c2; int m2;
                        if (!(hi >= 0 && uses[ch.v] == 1)) { if (xs == 0) continue; }
                        else if (!(f.bb[b].insts[static_cast<size_t>(hi)].op == OP_ADD)) { if (xs == 0) continue; }
                        (void)h2; (void)x2; (void)c2; (void)m2;
                    }
                    if (cx.isConst) continue;
                    h = ch; x = cx; c = a.a[1 - side]; mulAt = mi;
                    return true;
                }
            }
            return false;
        };
        for (int i = static_cast<int>(f.bb[b].insts.size()) - 1; i >= 0; i--) {
            if (consumed[static_cast<size_t>(i)]) continue;
            Opnd h, x, c;
            int mulAt;
            if (!step(i, h, x, c, mulAt, false)) continue;
            std::vector<Opnd> coef{c};   // c_n first; reversed later
            std::vector<int> nodes{i, mulAt};
            while (true) {
                int hi = localDef(h);
                if (hi < 0 || uses[h.v] != 1 || consumed[static_cast<size_t>(hi)]) break;
                Opnd h2, c2;
                Opnd x2 = x;
                int m2;
                if (!step(hi, h2, x2, c2, m2, true)) break;
                coef.push_back(c2);
                nodes.push_back(hi);
                nodes.push_back(m2);
                h = h2;
            }
            coef.push_back(h);   // c_0, the innermost value
            for (int nd : nodes) consumed[static_cast<size_t>(nd)] = 1;
            const int n = static_cast<int>(coef.size()) - 1;   // multiply-add steps
            if (n < 6) continue;
            if (localDef(x) > i) continue;
            std::reverse(coef.begin(), coef.end());   // coef[i] multiplies x^(n-i)
            const int k = (n >= 16 && registers >= 16) ? 4 : 2;
            std::vector<Inst> pre;
            auto bin = [&](Op op, Opnd p, Opnd q) {
                Inst t;
                t.op = op; t.dst = f.newVal(); t.n = 2; t.a[0] = p; t.a[1] = q;
                pre.push_back(t);
                return Opnd::val(t.dst);
            };
            const Opnd x2 = bin(OP_MUL, x, x);
            const Opnd y = k == 2 ? x2 : bin(OP_MUL, x2, x2);
            std::vector<Opnd> chain(static_cast<size_t>(k));
            std::vector<char> started(static_cast<size_t>(k), 0);
            for (int ci = 0; ci <= n; ci++) {
                const int j = (n - ci) % k;
                if (!started[static_cast<size_t>(j)]) { chain[static_cast<size_t>(j)] = coef[static_cast<size_t>(ci)]; started[static_cast<size_t>(j)] = 1; }
                else chain[static_cast<size_t>(j)] = bin(OP_ADD, bin(OP_MUL, chain[static_cast<size_t>(j)], y), coef[static_cast<size_t>(ci)]);
            }
            Opnd lo = bin(OP_MUL, x, chain[1]);
            Opnd res0 = chain[0];
            Inst &root = f.bb[b].insts[static_cast<size_t>(i)];
            Inst fin;
            fin.op = OP_ADD; fin.dst = root.dst; fin.n = 2;
            if (k == 2) {
                fin.a[0] = lo; fin.a[1] = res0;
            } else {
                Opnd L = bin(OP_ADD, lo, res0);
                Opnd H = bin(OP_ADD, bin(OP_MUL, x, chain[3]), chain[2]);
                fin.a[0] = bin(OP_MUL, x2, H); fin.a[1] = L;
            }
            pre.push_back(fin);
            auto &ins = f.bb[b].insts;
            ins.erase(ins.begin() + i);
            ins.insert(ins.begin() + i, pre.begin(), pre.end());
            changed = here = true;
            break;   // positions and def sites are stale: rescan this block
        }
        if (!here) break;
        { ds = defSites(f); uses.assign(f.nvals, 0);
            for (BB &B : f.bb) {
                if (!B.alive) continue;
                for (Phi &p : B.phis) for (auto &in : p.in) if (!in.second.isConst) uses[in.second.v]++;
                for (Inst &xx : B.insts) for (int a = 0; a < xx.n; a++) if (!xx.a[a].isConst) uses[xx.a[a].v]++;
            }
        }
      }
    }
    return changed;
}

// Counting selects: select(c, a, a+1) == a + (c == 0) and
// select(c, a+1, a) == a + (c != 0). The test moves off the path through a,
// so a chain of conditional increments costs one add per step instead of an
// add and a select. (c != 0 is c itself when c is 0 or 1, else eq(eq(c,0),0).)
bool selectToAdd(Func &f) {
    f.resolveAll();
    std::vector<DefSite> ds = defSites(f);
    bool changed = false;
    for (int b = 0; b < static_cast<int>(f.bb.size()); b++) {
        if (!f.bb[b].alive) continue;
        for (size_t i = 0; i < f.bb[b].insts.size(); i++) {
            const Inst x = f.bb[b].insts[i];
            if (x.op != OP_SELECT || x.dst < 0 || x.a[0].isConst) continue;
            const Opnd c = x.a[0];
            int incSide = -1;   // 1: true side is a+1; 2: false side is a+1
            Opnd base;
            for (int side = 1; side <= 2 && incSide < 0; side++) {
                const Opnd inc = x.a[side], other = x.a[3 - side];
                const Inst *d = defInst(f, ds, inc);
                if (d && d->op == OP_ADD && d->a[1].isC(1) && d->a[0] == other) { incSide = side; base = other; }
            }
            if (incSide < 0) continue;
            std::vector<Inst> pre;
            auto mk = [&](Op op, Opnd p, Opnd q) {
                Inst t;
                t.op = op; t.dst = f.newVal(); t.n = 2; t.a[0] = p; t.a[1] = q;
                pre.push_back(t);
                return Opnd::val(t.dst);
            };
            Opnd bit;
            if (incSide == 2) {
                bit = mk(OP_EQ, c, Opnd::cst(0));
            } else if (rangeOf(f, ds, c, 6).hi <= 1) {
                bit = c;
            } else {
                bit = mk(OP_EQ, mk(OP_EQ, c, Opnd::cst(0)), Opnd::cst(0));
            }
            Inst &y = f.bb[b].insts[i];
            y.op = OP_ADD; y.n = 2; y.a[0] = base; y.a[1] = bit;
            auto &ins = f.bb[b].insts;
            ins.insert(ins.begin() + static_cast<long>(i), pre.begin(), pre.end());
            i += pre.size();
            changed = true;
        }
        if (changed) ds = defSites(f);
    }
    return changed;
}

// ---------------------------------------------------------------------------
// Machine-specific fusion and strength reduction
// ---------------------------------------------------------------------------

bool fuseOps(Func &f, const Machine &m, bool fuseReductions) {
    f.resolveAll();
    std::vector<int> rec = recurrenceIds(f);
    std::vector<int> uses(f.nvals, 0);
    for (BB &B : f.bb) {
        if (!B.alive) continue;
        for (Phi &p : B.phis) for (auto &in : p.in) if (!in.second.isConst) uses[in.second.v]++;
        for (Inst &x : B.insts) for (int a = 0; a < x.n; a++) if (!x.a[a].isConst) uses[x.a[a].v]++;
    }
    std::vector<DefSite> ds = defSites(f);
    const bool macGood = m.fused_mac && m.lat_mac <= m.lat_mul + m.lat_alu;
    const bool addshGood = m.fused_addsh && m.lat_addsh <= 2 * m.lat_alu;
    bool changed = false;
    int curBlock = -1;
    // Only fuse with a producer in the same block: a producer that LICM hoisted
    // out of a loop must not be pulled back in.
    auto single = [&](Opnd o, Op op) -> const Inst * {
        const Inst *p = defInst(f, ds, o);
        return (p && p->op == op && uses[o.v] == 1 && ds[o.v].block == curBlock) ? p : nullptr;
    };
    for (int bi = 0; bi < static_cast<int>(f.bb.size()); bi++) {
        BB &B = f.bb[bi];
        if (!B.alive) continue;
        curBlock = bi;
        for (Inst &x : B.insts) {
            if (x.op == OP_ADD) {
                bool done = false;
                for (int side = 0; side < 2 && !done && macGood; side++) {
                    const Inst *p = single(x.a[side], OP_MUL);
                    if (!p) continue;
                    Opnd other = x.a[1 - side];
                    // In a reduction (s += a*b) the add is on the loop-carried cycle but
                    // the multiply is not: fusing would make every iteration wait
                    // lat_mac instead of lat_alu. Fuse only when the product is on the
                    // cycle too (Horner: acc = acc*x + c) or there is no cycle.
                    bool addOnCycle = rec[x.dst] >= 0;
                    bool mulOnCycle = addOnCycle && rec[x.a[side].v] == rec[x.dst];
                    if (addOnCycle && !mulOnCycle && m.lat_mac > m.lat_alu && !fuseReductions) continue;
                    Inst y = x;
                    y.op = OP_MAC; y.n = 3; y.a[0] = p->a[0]; y.a[1] = p->a[1]; y.a[2] = other;
                    uses[x.a[side].v]--;
                    x = y;
                    done = changed = true;
                }
                for (int side = 0; side < 2 && !done && addshGood; side++) {
                    const Inst *p = single(x.a[side], OP_SHL);
                    if (!p || !p->a[1].isConst) continue;
                    Opnd other = x.a[1 - side];
                    Inst y = x;
                    y.op = OP_ADDSH; y.n = 2; y.a[0] = other; y.a[1] = p->a[0]; y.k = static_cast<uint8_t>(p->a[1].c & 31);
                    uses[x.a[side].v]--;
                    x = y;
                    done = changed = true;
                }
            } else if (x.op == OP_SUB && macGood && x.a[1].isConst) {
                const Inst *p = single(x.a[0], OP_MUL);
                if (p) {
                    Inst y = x;
                    y.op = OP_MAC; y.n = 3; y.a[0] = p->a[0]; y.a[1] = p->a[1]; y.a[2] = Opnd::cst(0u - x.a[1].c);
                    uses[x.a[0].v]--;
                    x = y;
                    changed = true;
                }
            } else if (x.op == OP_MUL && x.a[1].isConst && m.fused_addsh && m.lat_addsh < m.lat_mul) {
                // y * (2^k + 1) == y + (y << k)
                uint32_t c = x.a[1].c;
                for (int k = 1; k < 31; k++) {
                    if (c == (1u << k) + 1u) {
                        x.op = OP_ADDSH; x.n = 2; x.a[1] = x.a[0]; x.k = static_cast<uint8_t>(k);
                        changed = true;
                        break;
                    }
                }
            } else if (x.op == OP_SHL && x.a[1].isConst && m.lat_mul < m.lat_alu) {
                x.op = OP_MUL;
                x.a[1] = Opnd::cst(1u << (x.a[1].c & 31));
                changed = true;
            }
        }
    }
    return changed;
}

// ---------------------------------------------------------------------------
// If-conversion: small branch arms become straight-line code plus select.
// ---------------------------------------------------------------------------

bool ifConvert(Func &f, const Machine &m) {
    f.resolveAll();
    f.rebuildPreds();
    std::vector<DefSite> ds = defSites(f);
    const int budget = 2 * (m.taken_branch_penalty + 1);
    bool changed = false;
    auto speculatable = [&](const Inst &x) {
        if (isPure(x.op)) return true;
        if (x.op == OP_DIV || x.op == OP_MOD) return rangeOf(f, ds, x.a[1], 8).lo >= 1;
        if (x.op == OP_LOAD) return rangeOf(f, ds, x.a[0], 8).hi < kMemWords;
        return false;
    };
    // Arm S of block a: only reached from a, falls into one block, all work speculatable.
    auto simpleArm = [&](int a, int s, int &join) {
        const BB &S = f.bb[s];
        if (s == a || s == 0 || !S.alive || S.preds.size() != 1 || S.preds[0] != a || !S.phis.empty()) return false;
        if (S.term().op != OP_JMP) return false;
        for (size_t i = 0; i + 1 < S.insts.size(); i++) if (!speculatable(S.insts[i])) return false;
        join = S.term().tgt[0];
        return join != s && join != a;
    };
    for (int a = 0; a < static_cast<int>(f.bb.size()); a++) {
        if (!f.bb[a].alive || f.bb[a].term().op != OP_BR) continue;
        const Opnd c = f.resolve(f.bb[a].term().a[0]);
        const int t = f.bb[a].term().tgt[0], e = f.bb[a].term().tgt[1];
        int jt = -1, je = -1;
        bool armT = simpleArm(a, t, jt), armE = simpleArm(a, e, je);
        int join;
        std::vector<int> arms;
        if (armT && armE && jt == je) { join = jt; arms = {t, e}; }
        else if (armT && jt == e) { join = e; arms = {t}; }
        else if (armE && je == t) { join = t; arms = {e}; }
        else continue;
        int cost = 0;
        for (int s : arms) cost += static_cast<int>(f.bb[s].insts.size()) - 1;
        cost += static_cast<int>(f.bb[join].phis.size());
        if (cost > budget) continue;
        // Value flowing into the join along the "true" and "false" directions.
        auto incoming = [&](const Phi &ph, int from) {
            for (auto &in : ph.in) if (in.first == from) return f.resolve(in.second);
            return Opnd::cst(0);
        };
        BB &A = f.bb[a];
        Inst br = A.term();
        A.insts.pop_back();
        for (int s : arms)
            for (size_t i = 0; i + 1 < f.bb[s].insts.size(); i++) A.insts.push_back(f.bb[s].insts[i]);
        const int fromTrue = (arms.size() == 2 || arms[0] == t) ? t : a;
        const int fromFalse = (arms.size() == 2 || arms[0] == e) ? e : a;
        for (Phi &ph : f.bb[join].phis) {
            Opnd vt = incoming(ph, fromTrue), vf = incoming(ph, fromFalse);
            Opnd v = vt;
            if (vt != vf) {
                Inst sel;
                sel.op = OP_SELECT;
                sel.dst = f.newVal();
                sel.n = 3;
                sel.a[0] = c; sel.a[1] = vt; sel.a[2] = vf;
                A.insts.push_back(sel);
                v = Opnd::val(sel.dst);
            }
            // Drop the inputs of the removed arms and of a itself; keep every
            // other predecessor (the join may even be its own predecessor).
            std::vector<std::pair<int, Opnd>> keep;
            for (auto &in : ph.in) {
                bool fromArm = std::find(arms.begin(), arms.end(), in.first) != arms.end();
                if (!fromArm && in.first != a) keep.push_back(in);
            }
            keep.push_back({a, v});
            ph.in.swap(keep);
        }
        Inst j;
        j.op = OP_JMP;
        j.tgt[0] = join;
        A.insts.push_back(j);
        (void)br;
        for (int s : arms) f.bb[s].alive = false;
        f.rebuildPreds();
        ds = defSites(f);
        changed = true;
    }
    return changed;
}

}  // namespace kopt
