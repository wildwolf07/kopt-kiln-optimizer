// Bounded matrix-product recipes: a triple loop nest computing
//   for i < N: for j < M: s = 0; for k < P: s += A(i,k) * B(k,j); C(i,j) = s
// with constant trip counts and affine addresses becomes a row loop whose body
// walks k outermost: one A(i,k) load feeds M independent accumulators, B loads
// use constant addresses, and the row's M results are stored at the end.
// Optionally two rows share each B load.
#include "passes.h"
#include "cfg.h"

#include <algorithm>
#include <functional>
#include <set>

namespace kopt {
namespace {

bool pureOp(Op op) {
    return op <= OP_SELECT || op == OP_MAC || op == OP_ADDSH;
}

struct Affine {
    bool valid = false;
    int64_t ci = 0, cj = 0, ck = 0, base = 0;
};

struct Nest {
    Func f;
    std::vector<const Inst *> defs;
    Val iv[3] = {-1, -1, -1};
    uint32_t trip[3] = {0, 0, 0};
    Affine a, b, c;     // A(i,k), B(k,j), C(i,j)
    Opnd result;
    unsigned work = 20000;

    const Inst *def(Opnd o) const { return o.isConst || o.v >= static_cast<int>(defs.size()) ? nullptr : defs[o.v]; }
    bool tick(int depth) { if (!work || depth <= 0) return false; --work; return true; }

    bool constant(Opnd o, uint32_t &value, int depth = 24) {
        if (!tick(depth)) return false;
        if (o.isConst) { value = o.c; return true; }
        const Inst *x = def(o);
        if (!x || !pureOp(x->op)) return false;
        uint32_t args[3] = {};
        for (int i = 0; i < x->n; ++i) if (!constant(x->a[i], args[i], depth - 1)) return false;
        return foldConstant(x->op, args[0], args[1], args[2], x->k, value);
    }
    bool invariant(Opnd o, int depth = 24) {
        if (!tick(depth)) return false;
        if (o.isConst || std::find(f.params.begin(), f.params.end(), o.v) != f.params.end()) return true;
        const Inst *x = def(o);
        if (!x || !pureOp(x->op)) return false;
        for (int i = 0; i < x->n; ++i) if (!invariant(x->a[i], depth - 1)) return false;
        return true;
    }
    // Exact affine form over the three induction variables, in 64-bit
    // integers; rejected unless every intermediate stays far from wrapping
    // (checked later through the address extremes).
    Affine affine(Opnd o, int depth = 24) {
        if (!tick(depth)) return {};
        if (o.isConst) return Affine{true, 0, 0, 0, static_cast<int64_t>(o.c)};
        for (int d = 0; d < 3; ++d) if (o.v == iv[d]) {
            Affine r{true, 0, 0, 0, 0};
            (d == 0 ? r.ci : d == 1 ? r.cj : r.ck) = 1;
            return r;
        }
        const Inst *x = def(o);
        if (!x) return {};
        if (x->op == OP_MOV) return affine(x->a[0], depth - 1);
        if (x->op != OP_ADD && x->op != OP_SUB && x->op != OP_MUL && x->op != OP_SHL && x->op != OP_ADDSH) return {};
        Affine p = affine(x->a[0], depth - 1), q = affine(x->a[1], depth - 1);
        if (!p.valid || !q.valid) return {};
        auto scale = [](Affine v, int64_t n) { return Affine{true, v.ci * n, v.cj * n, v.ck * n, v.base * n}; };
        auto constOnly = [](const Affine &v) { return !v.ci && !v.cj && !v.ck; };
        if (x->op == OP_SHL) {
            if (!constOnly(q) || q.base < 0 || q.base > 12) return {};
            return scale(p, int64_t{1} << q.base);
        }
        if (x->op == OP_MUL) {
            if (constOnly(q) && q.base <= 4096) return scale(p, q.base);
            if (constOnly(p) && p.base <= 4096) return scale(q, p.base);
            return {};
        }
        if (x->op == OP_ADDSH) { if (x->k > 12) return {}; q = scale(q, int64_t{1} << x->k); }
        if (x->op == OP_SUB) q = scale(q, -1);
        return Affine{true, p.ci + q.ci, p.cj + q.cj, p.ck + q.ck, p.base + q.base};
    }
};

// Copies, literals and trivial phis only (as for paired-row recipes).
bool prepare(Func &f) {
    unsigned work = 50000;
    for (int round = 0; round < 64; ++round) {
        bool changed = false;
        f.resolveAll();
        for (BB &b : f.bb) {
            for (const Inst &x : b.insts) if (x.op == OP_CONST || x.op == OP_MOV) {
                if (!work--) return false;
                const Opnd o = f.resolve(x.a[0]);
                if (f.resolve(Opnd::val(x.dst)) != o) { f.replaceAll(x.dst, o); changed = true; }
            }
            for (size_t i = 0; i < b.phis.size();) {
                const Phi &p = b.phis[i];
                bool have = false, same = true;
                Opnd value;
                for (const auto &in : p.in) {
                    if (!work--) return false;
                    Opnd o = f.resolve(in.second);
                    if (o == Opnd::val(p.dst)) continue;
                    if (!have) { value = o; have = true; } else if (o != value) same = false;
                }
                if (same) {
                    f.replaceAll(p.dst, have ? value : Opnd::cst(0));
                    b.phis.erase(b.phis.begin() + i); changed = true;
                } else ++i;
            }
        }
        if (!changed) { f.resolveAll(); dce(f); return true; }
    }
    return false;
}

bool extremes(const Affine &v, const uint32_t trip[3], int64_t &lo, int64_t &hi) {
    lo = hi = v.base;
    const int64_t co[3] = {v.ci, v.cj, v.ck};
    for (int d = 0; d < 3; ++d) {
        const int64_t span = co[d] * (static_cast<int64_t>(trip[d]) - 1);
        if (span < 0) lo += span; else hi += span;
    }
    return lo >= 0 && hi < static_cast<int64_t>(kMemWords);
}

bool recognize(const Program &in, Nest &n) {
    if (in.instrCount() > 400 || in.params.size() > 8) return false;
    int loads = 0, stores = 0;
    for (const Block &b : in.blocks) for (const Instr &x : b.ins) {
        loads += x.op == OP_LOAD; stores += x.op == OP_STORE;
        if (!pureOp(x.op) && x.op != OP_LOAD && x.op != OP_STORE &&
            x.op != OP_BR && x.op != OP_JMP && x.op != OP_RET) return false;
    }
    if (loads != 2 || stores != 1) return false;
    std::string err;
    if (!buildSSA(in, n.f, err) || n.f.nvals > 4096 || !prepare(n.f)) return false;
    Func &f = n.f;
    f.rebuildPreds();
    const DomInfo dom = computeDominators(f);
    const LoopInfo li = computeLoops(f, dom);
    if (li.loops.size() != 3) return false;
    // Order the loops outermost first and require a chain of nesting.
    std::vector<int> order = {0, 1, 2};
    std::sort(order.begin(), order.end(), [&](int x, int y) { return li.loops[x].depth < li.loops[y].depth; });
    for (int d = 0; d < 3; ++d) if (li.loops[order[d]].depth != d + 1) return false;
    if (li.loops[order[1]].parent != order[0] || li.loops[order[2]].parent != order[1]) return false;
    int branches = 0;
    for (int b = 0; b < static_cast<int>(f.bb.size()); ++b)
        if (f.bb[b].alive && !f.bb[b].insts.empty() && f.bb[b].term().op == OP_BR) ++branches;
    if (branches != 3) return false;
    n.defs.assign(f.nvals, nullptr);
    for (const BB &b : f.bb) if (b.alive) for (const Inst &x : b.insts) if (x.dst >= 0) n.defs[x.dst] = &x;
    Val acc = -1;
    Opnd accNext;
    for (int d = 0; d < 3; ++d) {
        const auto &L = li.loops[order[d]];
        if (L.latches.size() != 1) return false;
        const BB &H = f.bb[L.header];
        if (H.term().op != OP_BR || H.preds.size() != 2) return false;
        const int latch = L.latches[0];
        const int outside = H.preds[0] == latch ? H.preds[1] : H.preds[0];
        const int t0 = H.term().tgt[0], t1 = H.term().tgt[1];
        if (!L.blocks.empty() && (std::find(L.blocks.begin(), L.blocks.end(), t0) == L.blocks.end() ||
                                  std::find(L.blocks.begin(), L.blocks.end(), t1) != L.blocks.end())) return false;
        const Inst *test = n.def(H.term().a[0]);
        if (!test || test->op != OP_LT || test->a[0].isConst) return false;
        const Val iv = test->a[0].v;
        uint32_t bound;
        if (!n.constant(test->a[1], bound) || bound < 1 || bound > (d == 0 ? 64u : d == 1 ? 8u : 16u)) return false;
        size_t expected = d == 2 ? 2 : 1;
        if (H.phis.size() != expected) return false;
        bool sawIv = false;
        for (const Phi &p : H.phis) {
            if (p.in.size() != 2) return false;
            Opnd start, next;
            for (const auto &e : p.in) (e.first == outside ? start : next) = f.resolve(e.second);
            if (!start.isC(0)) return false;
            if (p.dst == iv) {
                const Inst *x = n.def(next);
                if (!x || x->op != OP_ADD ||
                    !((x->a[0] == Opnd::val(iv) && x->a[1].isC(1)) || (x->a[1] == Opnd::val(iv) && x->a[0].isC(1)))) return false;
                sawIv = true;
            } else if (d == 2) {
                acc = p.dst; accNext = next;
            } else return false;
        }
        if (!sawIv) return false;
        n.iv[d] = iv;
        n.trip[d] = bound;
    }
    if (acc < 0) return false;
    // The accumulator step: s + x*y (add of a mul, or mac).
    const Inst *step = n.def(accNext);
    Opnd x, y;
    if (step && step->op == OP_MAC && step->a[2] == Opnd::val(acc)) { x = step->a[0]; y = step->a[1]; }
    else if (step && step->op == OP_ADD) {
        const Opnd other = step->a[0] == Opnd::val(acc) ? step->a[1] : step->a[1] == Opnd::val(acc) ? step->a[0] : Opnd::cst(0);
        const Inst *mul = n.def(other);
        if (!mul || mul->op != OP_MUL) return false;
        x = mul->a[0]; y = mul->a[1];
    } else return false;
    const Inst *lx = n.def(x), *ly = n.def(y), *st = nullptr;
    if (!lx || !ly || lx->op != OP_LOAD || ly->op != OP_LOAD || lx == ly) return false;
    int storeBlock = -1;
    for (int b = 0; b < static_cast<int>(f.bb.size()); ++b)
        if (f.bb[b].alive) for (const Inst &z : f.bb[b].insts) if (z.op == OP_STORE) { st = &z; storeBlock = b; }
    if (!st || f.resolve(st->a[1]) != Opnd::val(acc)) return false;
    // Once per middle iteration, after the inner loop: in the middle loop,
    // outside the inner one (straight-line apart from the three loop tests).
    if (li.innermost[storeBlock] != order[1]) return false;
    Affine ax = n.affine(lx->a[0]), ay = n.affine(ly->a[0]);
    n.c = n.affine(st->a[0]);
    if (!ax.valid || !ay.valid || !n.c.valid || n.c.ck != 0) return false;
    if (ax.cj != 0) std::swap(ax, ay);
    if (ax.cj != 0 || ay.ci != 0 || ax.ci <= 0) return false;
    n.a = ax; n.b = ay;
    // Return value: invariant pure expression.
    for (const BB &b : f.bb) if (b.alive && b.term().op == OP_RET) {
        if (b.term().n < 1) return false;
        n.result = f.resolve(b.term().a[0]);
    }
    if (!n.invariant(n.result)) return false;
    // Every touched word is in memory, and the written block is disjoint
    // from both read blocks (no trap anywhere, no read sees a new value).
    int64_t alo, ahi, blo, bhi, clo, chi;
    if (!extremes(n.a, n.trip, alo, ahi) || !extremes(n.b, n.trip, blo, bhi) || !extremes(n.c, n.trip, clo, chi)) return false;
    if (!(chi < alo || ahi < clo) || !(chi < blo || bhi < clo)) return false;
    // C(i,j) must be distinct for distinct (i,j) so each word's last write is
    // the one the original performs last (rows in order, j ascending).
    std::set<int64_t> seen;
    for (uint32_t i = 0; i < n.trip[0]; ++i) for (uint32_t j = 0; j < n.trip[1]; ++j)
        if (!seen.insert(n.c.base + n.c.ci * i + n.c.cj * j).second) return false;
    return true;
}

Program emit(const Program &in, Nest &n, const Machine &m, int rows, bool spread) {
    Program p; p.name = in.name; p.params = in.params;
    uint32_t cursor = 0;
    auto fresh = [&]() {
        while (std::find(p.params.begin(), p.params.end(), cursor) != p.params.end()) ++cursor;
        return cursor++;
    };
    auto reg = [](uint32_t r) { return Operand::reg(r); };
    auto imm = [](uint32_t c) { return Operand::imm(c); };
    auto block = [&](const char *label) { Block b; b.label = label; p.blocks.push_back(b); };
    auto inst = [&](Op op, uint32_t dst, std::initializer_list<Operand> args, int k = 0) {
        Instr x; x.op = op; x.dst = dst; x.nsrc = static_cast<int>(args.size()); x.k = k;
        std::copy(args.begin(), args.end(), x.src); p.blocks.back().ins.push_back(x);
    };
    const uint32_t N = n.trip[0], M = n.trip[1], P = n.trip[2];
    const uint32_t rA = fresh(), t = fresh();
    const bool shareC = n.c.ci == n.a.ci;
    const uint32_t rC = shareC ? rA : fresh();
    // spread: separate names per A load (per k and row) and per B load (per
    // column) so schedulers can start loads early.
    std::vector<uint32_t> av(spread ? rows * P : rows), bv(spread ? M : 1), acc(rows * M);
    for (auto &r : av) r = fresh();
    for (auto &r : bv) r = fresh();
    for (auto &r : acc) r = fresh();
    const uint32_t prod = m.fused_mac ? 0 : fresh();
    block("mm_entry");
    inst(OP_CONST, rA, {imm(0)});
    if (!shareC) inst(OP_CONST, rC, {imm(0)});
    Instr j; j.op = OP_JMP; j.target[0] = 1; p.blocks.back().ins.push_back(j);
    block("mm_row");
    for (uint32_t k = 0; k < P; ++k) {
        for (int r = 0; r < rows; ++r) {
            const int64_t off = n.a.base + n.a.ck * k + n.a.ci * r;
            inst(OP_ADD, t, {reg(rA), imm(static_cast<uint32_t>(off))});
            inst(OP_LOAD, av[spread ? k * rows + r : r], {reg(t)});
        }
        for (uint32_t col = 0; col < M; ++col) {
            const int64_t addr = n.b.base + n.b.ck * k + n.b.cj * col;
            const uint32_t bq = bv[spread ? col : 0];
            inst(OP_LOAD, bq, {imm(static_cast<uint32_t>(addr))});
            for (int r = 0; r < rows; ++r) {
                const uint32_t s = acc[r * M + col];
                const uint32_t aq = av[spread ? k * rows + r : r];
                if (k == 0) inst(OP_MUL, s, {reg(aq), reg(bq)});
                else if (m.fused_mac) inst(OP_MAC, s, {reg(aq), reg(bq), reg(s)});
                else { inst(OP_MUL, prod, {reg(aq), reg(bq)}); inst(OP_ADD, s, {reg(s), reg(prod)}); }
            }
        }
    }
    for (int r = 0; r < rows; ++r)
        for (uint32_t col = 0; col < M; ++col) {
            const int64_t off = n.c.base + n.c.cj * col + n.c.ci * r;
            inst(OP_ADD, t, {reg(rC), imm(static_cast<uint32_t>(off))});
            inst(OP_STORE, 0, {reg(t), reg(acc[r * M + col])});
        }
    inst(OP_ADD, rA, {reg(rA), imm(static_cast<uint32_t>(n.a.ci * rows))});
    if (!shareC) inst(OP_ADD, rC, {reg(rC), imm(static_cast<uint32_t>(n.c.ci * rows))});
    inst(OP_LT, t, {reg(rA), imm(static_cast<uint32_t>(n.a.ci * N))});
    Instr br; br.op = OP_BR; br.nsrc = 1; br.src[0] = reg(t); br.target[0] = 1; br.target[1] = 2;
    p.blocks.back().ins.push_back(br);
    block("mm_done");
    // Clone the invariant result computation.
    std::vector<Operand> values(n.f.nvals);
    std::vector<char> have(n.f.nvals, 0);
    for (size_t i = 0; i < n.f.params.size(); ++i) { values[n.f.params[i]] = reg(in.params[i]); have[n.f.params[i]] = 1; }
    std::function<Operand(Opnd)> clone = [&](Opnd o) -> Operand {
        if (o.isConst) return imm(o.c);
        if (have[o.v]) return values[o.v];
        const Inst &x = *n.def(o);
        Instr copy; copy.op = x.op; copy.nsrc = x.n; copy.k = x.k;
        for (int i = 0; i < x.n; ++i) copy.src[i] = clone(x.a[i]);
        copy.dst = fresh(); p.blocks.back().ins.push_back(copy);
        have[o.v] = 1; return values[o.v] = reg(copy.dst);
    };
    const Operand result = clone(n.result);
    inst(OP_RET, 0, {result});
    return p;
}


// Software-pipelined single-row variant: A and B values alternate between two
// registers each, and every load is issued one step before its use, so an
// in-order machine overlaps load latency with the previous multiply-adds.
Program emitPipelined(const Program &in, Nest &n, const Machine &m) {
    Program p; p.name = in.name; p.params = in.params;
    uint32_t cursor = 0;
    auto fresh = [&]() {
        while (std::find(p.params.begin(), p.params.end(), cursor) != p.params.end()) ++cursor;
        return cursor++;
    };
    auto reg = [](uint32_t r) { return Operand::reg(r); };
    auto imm = [](uint32_t c) { return Operand::imm(c); };
    auto block = [&](const char *label) { Block b; b.label = label; p.blocks.push_back(b); };
    auto inst = [&](Op op, uint32_t dst, std::initializer_list<Operand> args) {
        Instr x; x.op = op; x.dst = dst; x.nsrc = static_cast<int>(args.size());
        std::copy(args.begin(), args.end(), x.src); p.blocks.back().ins.push_back(x);
    };
    const uint32_t N = n.trip[0], M = n.trip[1], P = n.trip[2];
    const uint32_t rA = fresh();
    const bool shareC = n.c.ci == n.a.ci;
    const uint32_t rC = shareC ? rA : fresh();
    const uint32_t a[2] = {fresh(), fresh()}, b[2] = {fresh(), fresh()};
    std::vector<uint32_t> acc(M);
    for (auto &r : acc) r = fresh();
    const uint32_t prod = m.fused_mac ? 0 : fresh();
    auto loadA = [&](uint32_t k) {
        const uint32_t r = a[k % 2];
        inst(OP_ADD, r, {reg(rA), imm(static_cast<uint32_t>(n.a.base + n.a.ck * k))});
        inst(OP_LOAD, r, {reg(r)});
    };
    auto loadB = [&](uint32_t g) {
        const uint32_t k = g / M, col = g % M;
        inst(OP_LOAD, b[g % 2], {imm(static_cast<uint32_t>(n.b.base + n.b.ck * k + n.b.cj * col))});
    };
    block("mm_entry");
    inst(OP_CONST, rA, {imm(0)});
    if (!shareC) inst(OP_CONST, rC, {imm(0)});
    Instr j; j.op = OP_JMP; j.target[0] = 1; p.blocks.back().ins.push_back(j);
    block("mm_row");
    loadA(0);
    loadB(0);
    for (uint32_t k = 0; k < P; ++k)
        for (uint32_t col = 0; col < M; ++col) {
            const uint32_t g = k * M + col;
            if (col == 0 && k + 1 < P) loadA(k + 1);
            if (g + 1 < P * M) loadB(g + 1);
            const uint32_t s = acc[col], av = a[k % 2], bv = b[g % 2];
            if (k == 0) inst(OP_MUL, s, {reg(av), reg(bv)});
            else if (m.fused_mac) inst(OP_MAC, s, {reg(av), reg(bv), reg(s)});
            else { inst(OP_MUL, prod, {reg(av), reg(bv)}); inst(OP_ADD, s, {reg(s), reg(prod)}); }
        }
    for (uint32_t col = 0; col < M; ++col) {
        inst(OP_ADD, a[0], {reg(rC), imm(static_cast<uint32_t>(n.c.base + n.c.cj * col))});
        inst(OP_STORE, 0, {reg(a[0]), reg(acc[col])});
    }
    inst(OP_ADD, rA, {reg(rA), imm(static_cast<uint32_t>(n.a.ci))});
    if (!shareC) inst(OP_ADD, rC, {reg(rC), imm(static_cast<uint32_t>(n.c.ci))});
    inst(OP_LT, a[1], {reg(rA), imm(static_cast<uint32_t>(n.a.ci * N))});
    Instr br; br.op = OP_BR; br.nsrc = 1; br.src[0] = reg(a[1]); br.target[0] = 1; br.target[1] = 2;
    p.blocks.back().ins.push_back(br);
    block("mm_done");
    std::vector<Operand> values(n.f.nvals);
    std::vector<char> have(n.f.nvals, 0);
    for (size_t i = 0; i < n.f.params.size(); ++i) { values[n.f.params[i]] = reg(in.params[i]); have[n.f.params[i]] = 1; }
    std::function<Operand(Opnd)> clone = [&](Opnd o) -> Operand {
        if (o.isConst) return imm(o.c);
        if (have[o.v]) return values[o.v];
        const Inst &x = *n.def(o);
        Instr copy; copy.op = x.op; copy.nsrc = x.n; copy.k = x.k;
        for (int i = 0; i < x.n; ++i) copy.src[i] = clone(x.a[i]);
        copy.dst = fresh(); p.blocks.back().ins.push_back(copy);
        have[o.v] = 1; return values[o.v] = reg(copy.dst);
    };
    const Operand result = clone(n.result);
    inst(OP_RET, 0, {result});
    return p;
}

// Column-chunked single-row variant for few registers: C columns at a time,
// the A address computed into the A register itself, and on machines without
// mac the B register reused for the product. Needs C + 3 registers (+1 when C
// has its own row offset).
Program emitChunked(const Program &in, Nest &n, const Machine &m, uint32_t C) {
    Program p; p.name = in.name; p.params = in.params;
    uint32_t cursor = 0;
    auto fresh = [&]() {
        while (std::find(p.params.begin(), p.params.end(), cursor) != p.params.end()) ++cursor;
        return cursor++;
    };
    auto reg = [](uint32_t r) { return Operand::reg(r); };
    auto imm = [](uint32_t c) { return Operand::imm(c); };
    auto block = [&](const char *label) { Block b; b.label = label; p.blocks.push_back(b); };
    auto inst = [&](Op op, uint32_t dst, std::initializer_list<Operand> args) {
        Instr x; x.op = op; x.dst = dst; x.nsrc = static_cast<int>(args.size());
        std::copy(args.begin(), args.end(), x.src); p.blocks.back().ins.push_back(x);
    };
    const uint32_t N = n.trip[0], M = n.trip[1], P = n.trip[2];
    const uint32_t rA = fresh();
    const bool shareC = n.c.ci == n.a.ci;
    const uint32_t rC = shareC ? rA : fresh();
    const uint32_t a = fresh(), b = fresh();
    std::vector<uint32_t> acc(C);
    for (auto &r : acc) r = fresh();
    block("mm_entry");
    inst(OP_CONST, rA, {imm(0)});
    if (!shareC) inst(OP_CONST, rC, {imm(0)});
    Instr j; j.op = OP_JMP; j.target[0] = 1; p.blocks.back().ins.push_back(j);
    block("mm_row");
    for (uint32_t c0 = 0; c0 < M; c0 += C) {
        const uint32_t width = std::min(C, M - c0);
        for (uint32_t k = 0; k < P; ++k) {
            inst(OP_ADD, a, {reg(rA), imm(static_cast<uint32_t>(n.a.base + n.a.ck * k))});
            inst(OP_LOAD, a, {reg(a)});
            for (uint32_t w = 0; w < width; ++w) {
                const uint32_t col = c0 + w, s = acc[w];
                inst(OP_LOAD, b, {imm(static_cast<uint32_t>(n.b.base + n.b.ck * k + n.b.cj * col))});
                if (k == 0) inst(OP_MUL, s, {reg(a), reg(b)});
                else if (m.fused_mac) inst(OP_MAC, s, {reg(a), reg(b), reg(s)});
                else { inst(OP_MUL, b, {reg(a), reg(b)}); inst(OP_ADD, s, {reg(s), reg(b)}); }
            }
        }
        for (uint32_t w = 0; w < width; ++w) {
            inst(OP_ADD, a, {reg(rC), imm(static_cast<uint32_t>(n.c.base + n.c.cj * (c0 + w)))});
            inst(OP_STORE, 0, {reg(a), reg(acc[w])});
        }
    }
    inst(OP_ADD, rA, {reg(rA), imm(static_cast<uint32_t>(n.a.ci))});
    if (!shareC) inst(OP_ADD, rC, {reg(rC), imm(static_cast<uint32_t>(n.c.ci))});
    inst(OP_LT, a, {reg(rA), imm(static_cast<uint32_t>(n.a.ci * N))});
    Instr br; br.op = OP_BR; br.nsrc = 1; br.src[0] = reg(a); br.target[0] = 1; br.target[1] = 2;
    p.blocks.back().ins.push_back(br);
    block("mm_done");
    std::vector<Operand> values(n.f.nvals);
    std::vector<char> have(n.f.nvals, 0);
    for (size_t i = 0; i < n.f.params.size(); ++i) { values[n.f.params[i]] = reg(in.params[i]); have[n.f.params[i]] = 1; }
    std::function<Operand(Opnd)> clone = [&](Opnd o) -> Operand {
        if (o.isConst) return imm(o.c);
        if (have[o.v]) return values[o.v];
        const Inst &x = *n.def(o);
        Instr copy; copy.op = x.op; copy.nsrc = x.n; copy.k = x.k;
        for (int i = 0; i < x.n; ++i) copy.src[i] = clone(x.a[i]);
        copy.dst = fresh(); p.blocks.back().ins.push_back(copy);
        have[o.v] = 1; return values[o.v] = reg(copy.dst);
    };
    const Operand result = clone(n.result);
    inst(OP_RET, 0, {result});
    return p;
}
}  // namespace

std::vector<Program> matmulAlternatives(const Program &in, const Machine &m) {
    Nest n;
    if (!recognize(in, n)) return {};
    std::vector<Program> out;
    out.push_back(emit(in, n, m, 1, false));
    if (n.trip[0] % 2 == 0) out.push_back(emit(in, n, m, 2, false));
    out.push_back(emit(in, n, m, 1, true));
    out.push_back(emitPipelined(in, n, m));
    for (uint32_t C : {1u, 2u, 4u}) if (C <= n.trip[1]) out.push_back(emitChunked(in, n, m, C));
    return out;
}

}  // namespace kopt
