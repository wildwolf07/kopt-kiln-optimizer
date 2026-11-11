// Bounded, source-derived two-row matrix/vector reuse recipes.
#include "passes.h"

#include <algorithm>
#include <array>
#include <functional>
#include <set>

namespace kopt {
namespace {

bool pure(Op op) {
    return op <= OP_SELECT || op == OP_MAC || op == OP_ADDSH;
}

struct Linear {
    bool valid = false;
    uint32_t row = 0, col = 0, base = 0;
};

struct Recipe {
    Func f;
    std::vector<const Inst *> defs;
    Opnd count, result;
    uint32_t rows = 0, cols = 0, stride = 0, a = 0, b = 0, c = 0;
    unsigned work = 20000;

    const Inst *def(Opnd o) const {
        return o.isConst ? nullptr : defs[o.v];
    }
    bool tick(int depth) { if (!work || !depth) return false; --work; return true; }

    bool constant(Opnd o, uint32_t &value, int depth = 32) {
        if (!tick(depth)) return false;
        if (o.isConst) { value = o.c; return true; }
        const Inst *x = def(o);
        if (!x || !pure(x->op)) return false;
        uint32_t args[3] = {};
        for (int i = 0; i < x->n; ++i)
            if (!constant(x->a[i], args[i], depth - 1)) return false;
        return foldConstant(x->op, args[0], args[1], args[2], x->k, value);
    }

    // A return/count is invariant only if its entire dependency graph reaches
    // parameters/literals through total pure operations, never a phi or load.
    bool invariant(Opnd o, int depth = 32) {
        if (!tick(depth)) return false;
        if (o.isConst || std::find(f.params.begin(), f.params.end(), o.v) != f.params.end()) return true;
        const Inst *x = def(o);
        if (!x || !pure(x->op)) return false;
        for (int i = 0; i < x->n; ++i) if (!invariant(x->a[i], depth - 1)) return false;
        return true;
    }

    bool bound(Opnd o, uint32_t &hi, int depth = 16) {
        if (!tick(depth)) return false;
        if (constant(o, hi)) return hi <= 16;
        const Inst *x = def(o);
        if (!x) return false;
        for (int k = 0; k < 2; ++k) {
            uint32_t c;
            if (!constant(x->a[k], c)) continue;
            if (x->op == OP_AND && c <= 16) { hi = c; return true; }
            uint32_t h;
            if (x->op == OP_ADD && c <= 16 && bound(x->a[1-k], h, depth - 1) && h + c <= 16) {
                hi = h + c; return true;
            }
        }
        return false;
    }

    Linear linear(Opnd o, Val row, Val col, int depth = 24) {
        if (!tick(depth)) return {};
        if (o.isConst) return {true, 0, 0, o.c};
        if (o.v == row) return {true, 1, 0, 0};
        if (o.v == col) return {true, 0, 1, 0};
        const Inst *x = def(o);
        if (!x) return {};
        if (x->op == OP_CONST || x->op == OP_MOV) return linear(x->a[0], row, col, depth - 1);
        if (x->op != OP_ADD && x->op != OP_SUB && x->op != OP_MUL && x->op != OP_SHL && x->op != OP_ADDSH) return {};
        Linear a = linear(x->a[0], row, col, depth - 1), b = linear(x->a[1], row, col, depth - 1);
        if (!a.valid || !b.valid) return {};
        auto scale = [](Linear v, uint32_t n) { return Linear{true, v.row*n, v.col*n, v.base*n}; };
        if (x->op == OP_SHL) {
            if (b.row || b.col) return {};
            return scale(a, uint32_t{1} << (b.base & 31));
        }
        if (x->op == OP_MUL) {
            if (!b.row && !b.col) return scale(a, b.base);
            if (!a.row && !a.col) return scale(b, a.base);
            return {};
        }
        if (x->op == OP_ADDSH) b = scale(b, uint32_t{1} << (x->k & 31));
        if (x->op == OP_SUB) b = scale(b, uint32_t{0}-1);
        return {true, a.row+b.row, a.col+b.col, a.base+b.base};
    }
};

// Only expose copies/literals and trivial phis; do not rewrite the CFG, fold
// tests, move effects, or use cached value ranges to recognize a source.
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

bool recognize(const Program &in, Recipe &r) {
    if (in.blocks.size() != 7 || in.params.size() > 8 || in.instrCount() > 160) return false;
    // Check before cleanup: even a dead load or a dead non-total operation
    // prevents the exact two-load/one-store recipe from being recognized.
    int loads = 0, stores = 0;
    for (const Block &b : in.blocks) for (const Instr &x : b.ins) {
        loads += x.op == OP_LOAD; stores += x.op == OP_STORE;
        if (!pure(x.op) && x.op != OP_LOAD && x.op != OP_STORE &&
            x.op != OP_BR && x.op != OP_JMP && x.op != OP_RET) return false;
    }
    if (loads != 2 || stores != 1) return false;
    std::string err;
    if (!buildSSA(in, r.f, err) || r.f.nvals > 2048 || !prepare(r.f)) return false;
    Func &f = r.f;
    if (f.bb.size() != 7) return false;
    auto target = [&](int b, Op op, int edge = 0) {
        if (b < 0 || b >= 7 || f.bb[b].insts.empty() || f.bb[b].term().op != op) return -1;
        return f.bb[b].term().tgt[edge];
    };
    const int oh = target(0, OP_JMP), init = target(oh, OP_BR), exit = target(oh, OP_BR, 1);
    const int ih = target(init, OP_JMP), body = target(ih, OP_BR), store = target(ih, OP_BR, 1);
    if (std::set<int>{0,oh,init,exit,ih,body,store}.size() != 7 ||
        std::min({oh,init,exit,ih,body,store}) < 0 || std::max({oh,init,exit,ih,body,store}) >= 7 ||
        target(body, OP_JMP) != ih || target(store, OP_JMP) != oh || f.bb[exit].term().op != OP_RET) return false;
    if (f.bb[oh].phis.size() != 1 || f.bb[ih].phis.size() != 2) return false;
    for (int b : {0,init,body,store,exit}) if (!f.bb[b].phis.empty()) return false;
    r.defs.assign(f.nvals, nullptr);
    for (const BB &b : f.bb) for (const Inst &x : b.insts) if (x.dst >= 0) r.defs[x.dst] = &x;
    const Inst *ot = r.def(f.bb[oh].term().a[0]), *it = r.def(f.bb[ih].term().a[0]);
    const Val row = f.bb[oh].phis[0].dst;
    if (!ot || !it || ot->op != OP_LT || it->op != OP_LT || ot->a[0] != Opnd::val(row) || it->a[0].isConst) return false;
    const Val col = it->a[0].v;
    const Phi *cp = nullptr, *sp = nullptr;
    for (const Phi &p : f.bb[ih].phis) { if (p.dst == col) cp = &p; else sp = &p; }
    if (!cp || !sp) return false;
    auto incoming = [](const Phi &p, int b, Opnd &o) {
        if (p.in.size() != 2) return false;
        for (const auto &v : p.in) if (v.first == b) { o = v.second; return true; }
        return false;
    };
    auto recurrence = [&](const Phi &p, int entry, int back, bool unit, Opnd &next) {
        Opnd start;
        if (!incoming(p, entry, start) || !start.isC(0) || !incoming(p, back, next)) return false;
        const Inst *x = r.def(next);
        return !unit || (x && x->op == OP_ADD &&
            ((x->a[0] == Opnd::val(p.dst) && x->a[1].isC(1)) ||
             (x->a[1] == Opnd::val(p.dst) && x->a[0].isC(1))));
    };
    Opnd rn, cn, sn;
    if (!recurrence(f.bb[oh].phis[0], 0, store, true, rn) ||
        !recurrence(*cp, init, body, true, cn) || !recurrence(*sp, init, body, false, sn)) return false;
    r.count = ot->a[1]; r.result = f.bb[exit].term().a[0];
    if (!r.invariant(r.count) || !r.invariant(r.result) || !r.bound(r.count, r.rows) ||
        !r.constant(it->a[1], r.cols) || r.cols > 16) return false;
    std::array<const Inst *,2> ld{};
    const Inst *st = nullptr;
    loads = 0;
    for (int b = 0; b < 7; ++b) for (const Inst &x : f.bb[b].insts) {
        if (x.op == OP_LOAD) { if (b != body || loads == 2) return false; ld[loads++] = &x; }
        if (x.op == OP_STORE) { if (b != store || st) return false; st = &x; }
    }
    if (loads != 2 || !st || st->a[1] != Opnd::val(sp->dst)) return false;
    const Inst *sum = r.def(sn), *product = nullptr;
    if (!sum) return false;
    Opnd x, y;
    if (sum->op == OP_MAC && sum->a[2] == Opnd::val(sp->dst)) { x = sum->a[0]; y = sum->a[1]; }
    else if (sum->op == OP_ADD) {
        if (sum->a[0] == Opnd::val(sp->dst)) product = r.def(sum->a[1]);
        if (sum->a[1] == Opnd::val(sp->dst)) product = r.def(sum->a[0]);
        if (!product || product->op != OP_MUL) return false;
        x = product->a[0]; y = product->a[1];
    } else return false;
    if (!((x == Opnd::val(ld[0]->dst) && y == Opnd::val(ld[1]->dst)) ||
          (y == Opnd::val(ld[0]->dst) && x == Opnd::val(ld[1]->dst)))) return false;
    Linear a = r.linear(ld[0]->a[0], row, col), b = r.linear(ld[1]->a[0], row, col), c = r.linear(st->a[0], row, col);
    if (!a.row) std::swap(a,b);
    if (!a.valid || !b.valid || !c.valid || !a.row || a.col != 1 || b.row || b.col != 1 || c.row != 1 || c.col) return false;
    r.stride = a.row; r.a = a.base; r.b = b.base; r.c = c.base;
    // Use widened arithmetic: no accepted address wraps or leaves memory.
    // Empty extents are conservatively checked as one word as well.
    const uint64_t rows = std::max(1u,r.rows), cols = std::max(1u,r.cols);
    const uint64_t ae = uint64_t(r.a) + (rows-1)*r.stride + cols;
    const uint64_t be = uint64_t(r.b) + cols, ce = uint64_t(r.c) + rows;
    auto disjoint = [](uint64_t lo, uint64_t hi, uint64_t l, uint64_t h) { return hi <= l || h <= lo; };
    return ae <= kMemWords && be <= kMemWords && ce <= kMemWords &&
        disjoint(r.a,ae,r.b,be) && disjoint(r.a,ae,r.c,ce) && disjoint(r.b,be,r.c,ce);
}

Program emit(const Program &in, const Recipe &r, bool unrolled) {
    Program p; p.name = in.name; p.params = in.params;
    uint32_t cursor = 0;
    auto fresh = [&]() {
        while (std::find(p.params.begin(), p.params.end(), cursor) != p.params.end()) ++cursor;
        return cursor++;
    };
    auto reg = [](uint32_t n) { return Operand::reg(n); };
    auto imm = [](uint32_t n) { return Operand::imm(n); };
    auto block = [&](const char *label) { Block b; b.label = label; p.blocks.push_back(b); };
    auto inst = [&](Op op, uint32_t dst, std::initializer_list<Operand> args) {
        Instr x; x.op = op; x.dst = dst; x.nsrc = static_cast<int>(args.size());
        std::copy(args.begin(),args.end(),x.src); p.blocks.back().ins.push_back(x);
    };
    auto jump = [&](int to) { Instr x; x.op = OP_JMP; x.target[0] = to; p.blocks.back().ins.push_back(x); };
    auto branch = [&](Operand cond, int yes, int no) {
        Instr x; x.op = OP_BR; x.nsrc = 1; x.src[0] = cond; x.target[0] = yes; x.target[1] = no;
        p.blocks.back().ins.push_back(x);
    };
    block("rp_entry");
    std::vector<Operand> values(r.f.nvals);
    std::vector<char> have(r.f.nvals,0);
    for (size_t i = 0; i < r.f.params.size(); ++i) { values[r.f.params[i]] = reg(in.params[i]); have[r.f.params[i]] = 1; }
    std::function<Operand(Opnd)> clone = [&](Opnd o) -> Operand {
        if (o.isConst) return imm(o.c);
        if (have[o.v]) return values[o.v];
        const Inst &x = *r.def(o);
        Instr copy; copy.op = x.op; copy.nsrc = x.n; copy.k = x.k;
        for (int i = 0; i < x.n; ++i) copy.src[i] = clone(x.a[i]);
        copy.dst = fresh(); p.blocks.back().ins.push_back(copy);
        have[o.v] = 1; return values[o.v] = reg(copy.dst);
    };
    const Operand count = clone(r.count), result = clone(r.result);
    const uint32_t row = fresh(), next = fresh(), test = fresh(), col = fresh();
    const uint32_t ar = fresh(), an = fresh(), s0 = fresh(), s1 = fresh(), bv = fresh(), av = fresh(), addr = fresh(), product = fresh();
    inst(OP_CONST,row,{imm(0)}); jump(1);
    block("rp_head");
    inst(OP_ADD,next,{reg(row),imm(1)}); inst(OP_LT,test,{reg(next),count}); branch(reg(test),2,unrolled?4:6);
    block("rp_pair");
    inst(OP_MUL,ar,{reg(row),imm(r.stride)}); inst(OP_ADD,ar,{reg(ar),imm(r.a)});
    inst(OP_ADD,an,{reg(ar),imm(r.stride)});
    inst(OP_CONST,s0,{imm(0)}); inst(OP_CONST,s1,{imm(0)});
    auto step = [&](Operand j, bool pair) {
        inst(OP_ADD,addr,{j,imm(r.b)}); inst(OP_LOAD,bv,{reg(addr)});
        inst(OP_ADD,addr,{reg(ar),j}); inst(OP_LOAD,av,{reg(addr)});
        inst(OP_MUL,product,{reg(av),reg(bv)}); inst(OP_ADD,s0,{reg(s0),reg(product)});
        if (pair) {
            inst(OP_ADD,addr,{reg(an),j}); inst(OP_LOAD,av,{reg(addr)});
            inst(OP_MUL,product,{reg(av),reg(bv)}); inst(OP_ADD,s1,{reg(s1),reg(product)});
        }
    };
    if (unrolled) {
        for (uint32_t j = 0; j < r.cols; ++j) step(imm(j),true);
        jump(3);
    } else {
        inst(OP_CONST,col,{imm(0)}); jump(3);
        block("rp_inner"); inst(OP_LT,test,{reg(col),imm(r.cols)}); branch(reg(test),4,5);
        block("rp_step"); step(reg(col),true); inst(OP_ADD,col,{reg(col),imm(1)}); jump(3);
    }
    block("rp_store");
    inst(OP_ADD,addr,{reg(row),imm(r.c)}); inst(OP_STORE,0,{reg(addr),reg(s0)});
    inst(OP_ADD,addr,{reg(next),imm(r.c)}); inst(OP_STORE,0,{reg(addr),reg(s1)});
    inst(OP_ADD,row,{reg(row),imm(2)}); jump(1);
    block("rp_tail"); inst(OP_LT,test,{reg(row),count}); branch(reg(test),unrolled?5:7,unrolled?6:8);
    block("rp_single");
    inst(OP_MUL,ar,{reg(row),imm(r.stride)}); inst(OP_ADD,ar,{reg(ar),imm(r.a)}); inst(OP_CONST,s0,{imm(0)});
    for (uint32_t j = 0; j < r.cols; ++j) step(imm(j),false);
    inst(OP_ADD,addr,{reg(row),imm(r.c)}); inst(OP_STORE,0,{reg(addr),reg(s0)}); jump(unrolled?6:8);
    block("rp_done"); inst(OP_RET,0,{result});
    return p;
}

}  // namespace

std::vector<Program> rowPairAlternatives(const Program &in) {
    Recipe r;
    if (!recognize(in,r)) return {};
    return {emit(in,r,false),emit(in,r,true)};
}

}  // namespace kopt
