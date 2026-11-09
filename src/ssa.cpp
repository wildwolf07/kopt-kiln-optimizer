// ssa.cpp - SSA construction (Cytron et al. phi placement on iterated dominance
// frontiers, semi-pruned by "global names"), plus IR utilities.
#include <algorithm>
#include <cstdio>
#include <sstream>
#include <unordered_map>

#include "cfg.h"
#include "ir.h"
#include "passes.h"

namespace kopt {

int Func::succs(int b, int out[2]) const {
    const Inst &t = bb[b].insts.back();
    if (t.op == OP_JMP) { out[0] = t.tgt[0]; return 1; }
    if (t.op == OP_BR) {
        out[0] = t.tgt[0];
        if (t.tgt[1] == t.tgt[0]) return 1;
        out[1] = t.tgt[1];
        return 2;
    }
    return 0;
}

void Func::rebuildPreds() {
    for (BB &b : bb) b.preds.clear();
    for (int b = 0; b < static_cast<int>(bb.size()); b++) {
        if (!bb[b].alive) continue;
        int s[2];
        int ns = succs(b, s);
        for (int i = 0; i < ns; i++) bb[s[i]].preds.push_back(b);
    }
    for (BB &b : bb) {
        if (!b.alive) continue;
        for (Phi &p : b.phis) {
            std::vector<std::pair<int, Opnd>> keep;
            for (auto &in : p.in) {
                bool isPred = std::find(b.preds.begin(), b.preds.end(), in.first) != b.preds.end();
                bool dup = false;
                for (auto &k : keep) if (k.first == in.first) dup = true;
                if (isPred && !dup) keep.push_back(in);
            }
            p.in.swap(keep);
        }
    }
}

void Func::resolveAll() {
    for (BB &b : bb) {
        if (!b.alive) continue;
        for (Phi &p : b.phis)
            for (auto &in : p.in) in.second = resolve(in.second);
        for (Inst &i : b.insts)
            for (int k = 0; k < i.n; k++) i.a[k] = resolve(i.a[k]);
    }
}

bool buildSSA(const Program &p, Func &f, std::string &err) {
    clearIVRanges();   // range facts belong to one function
    f = Func();
    f.name = p.name;
    // Dense register numbering.
    std::unordered_map<uint32_t, int> rid;
    auto reg = [&](uint32_t r) {
        auto it = rid.find(r);
        if (it != rid.end()) return it->second;
        int id = static_cast<int>(rid.size());
        rid.emplace(r, id);
        return id;
    };
    for (uint32_t r : p.params) reg(r);
    for (const Block &b : p.blocks)
        for (const Instr &in : b.ins) {
            if (hasDest(in.op)) reg(in.dst);
            for (int s = 0; s < in.nsrc; s++) if (in.src[s].isReg) reg(in.src[s].v);
        }
    const int R = static_cast<int>(rid.size());

    // Blocks. A synthetic entry is added when the original entry has predecessors,
    // so that the entry block never needs phis.
    bool entryHasPred = false;
    for (const Block &b : p.blocks)
        for (const Instr &in : b.ins) {
            if (in.op == OP_JMP && in.target[0] == 0) entryHasPred = true;
            if (in.op == OP_BR && (in.target[0] == 0 || in.target[1] == 0)) entryHasPred = true;
        }
    const int shift = entryHasPred ? 1 : 0;
    f.bb.resize(p.blocks.size() + shift);
    if (entryHasPred) {
        Inst j;
        j.op = OP_JMP;
        j.tgt[0] = 1;
        f.bb[0].insts.push_back(j);
        f.bb[0].label = "";
    }
    // During construction an operand with isConst=false holds a register index.
    for (size_t bi = 0; bi < p.blocks.size(); bi++) {
        BB &B = f.bb[bi + shift];
        B.label = p.blocks[bi].label;
        for (const Instr &in : p.blocks[bi].ins) {
            Inst x;
            x.op = in.op;
            x.k = static_cast<uint8_t>(in.k);
            x.n = static_cast<uint8_t>(in.nsrc);
            for (int s = 0; s < in.nsrc; s++)
                x.a[s] = in.src[s].isReg ? Opnd::val(reg(in.src[s].v)) : Opnd::cst(in.src[s].v);
            x.dst = hasDest(in.op) ? reg(in.dst) : -1;
            if (in.op == OP_CONST) x.op = OP_MOV;
            if (in.op == OP_JMP) x.tgt[0] = in.target[0] + shift;
            if (in.op == OP_BR) {
                x.tgt[0] = in.target[0] + shift;
                x.tgt[1] = in.target[1] + shift;
                if (x.tgt[0] == x.tgt[1]) {   // br c, X, X == jmp X (reading c has no effect)
                    x.op = OP_JMP;
                    x.n = 0;
                }
            }
            B.insts.push_back(x);
        }
    }
    f.rebuildPreds();
    DomInfo dom = computeDominators(f);
    for (int b = 0; b < static_cast<int>(f.bb.size()); b++)
        if (!dom.reachable(b)) f.bb[b].alive = false;
    f.rebuildPreds();
    dom = computeDominators(f);
    auto df = dominanceFrontiers(f, dom);

    // Global names: registers read in a block before being written there.
    std::vector<char> global(R, 0);
    std::vector<std::vector<int>> defBlocks(R);
    {
        std::vector<int> killedIn(R, -1);
        for (int b : dom.rpo) {
            for (const Inst &x : f.bb[b].insts) {
                for (int s = 0; s < x.n; s++)
                    if (!x.a[s].isConst && killedIn[x.a[s].v] != b) global[x.a[s].v] = 1;
                if (x.dst >= 0) {
                    killedIn[x.dst] = b;
                    auto &v = defBlocks[x.dst];
                    if (v.empty() || v.back() != b) v.push_back(b);
                }
            }
        }
    }
    // Phi placement. The entry block holds the initial definition of every register.
    const int nb = static_cast<int>(f.bb.size());
    std::vector<int> phiReg;                       // per block, phi index -> register
    std::vector<std::vector<int>> blockPhiRegs(nb);
    std::vector<int> hasPhi(nb, -1), inWork(nb, -1);
    for (int r = 0; r < R; r++) {
        if (!global[r]) continue;
        std::vector<int> work = defBlocks[r];
        for (int b : work) inWork[b] = r;
        while (!work.empty()) {
            int b = work.back();
            work.pop_back();
            for (int y : df[b]) {
                if (hasPhi[y] == r) continue;
                hasPhi[y] = r;
                blockPhiRegs[y].push_back(r);
                if (inWork[y] != r) { inWork[y] = r; work.push_back(y); }
            }
        }
    }
    // Values: parameters first.
    f.nvals = 0;
    f.fwd.clear();
    std::vector<std::vector<Opnd>> stack(R);
    std::vector<char> isParamReg(R, 0);
    for (uint32_t pr : p.params) {
        Val v = f.newVal();
        f.params.push_back(v);
        int r = rid.at(pr);
        isParamReg[r] = 1;
        stack[r].push_back(Opnd::val(v));
    }
    for (int r = 0; r < R; r++)
        if (!isParamReg[r]) stack[r].push_back(Opnd::cst(0));
    for (int b = 0; b < nb; b++) {
        for (int r : blockPhiRegs[b]) {
            Phi ph;
            ph.dst = r;   // temporarily the register; renamed below
            f.bb[b].phis.push_back(ph);
        }
    }
    // Rename along the dominator tree (iterative DFS).
    struct Frame { int b; size_t child; std::vector<int> pushed; };
    std::vector<Frame> st;
    st.push_back({0, 0, {}});
    auto enter = [&](Frame &fr) {
        BB &B = f.bb[fr.b];
        for (Phi &ph : B.phis) {
            int r = ph.dst;
            Val v = f.newVal();
            ph.dst = v;
            stack[r].push_back(Opnd::val(v));
            fr.pushed.push_back(r);
        }
        for (Inst &x : B.insts) {
            for (int s = 0; s < x.n; s++)
                if (!x.a[s].isConst) x.a[s] = stack[x.a[s].v].back();
            if (x.dst >= 0) {
                int r = x.dst;
                Val v = f.newVal();
                x.dst = v;
                stack[r].push_back(Opnd::val(v));
                fr.pushed.push_back(r);
            }
        }
        int s[2];
        int ns = f.succs(fr.b, s);
        for (int i = 0; i < ns; i++) {
            BB &S = f.bb[s[i]];
            for (size_t k = 0; k < S.phis.size(); k++) {
                int r = blockPhiRegs[s[i]][k];
                S.phis[k].in.push_back({fr.b, stack[r].back()});
            }
        }
    };
    enter(st.back());
    while (!st.empty()) {
        Frame &top = st.back();
        if (top.child < dom.children[top.b].size()) {
            int c = dom.children[top.b][top.child++];
            st.push_back({c, 0, {}});
            enter(st.back());
        } else {
            for (int r : top.pushed) stack[r].pop_back();
            st.pop_back();
        }
    }
    (void)err;
    return true;
}

std::string verifyFunc(Func &f) {
    f.resolveAll();
    DomInfo d = computeDominators(f);
    std::vector<int> defBlock(f.nvals, -2), defPos(f.nvals, -1);
    for (Val v : f.params) defBlock[v] = -1;   // defined before the entry
    std::ostringstream err;
    for (int b : d.rpo) {
        BB &B = f.bb[b];
        for (Phi &p : B.phis) {
            if (defBlock[p.dst] != -2) err << "value " << p.dst << " defined twice\n";
            defBlock[p.dst] = b;
            defPos[p.dst] = -1;
        }
        for (size_t i = 0; i < B.insts.size(); i++) {
            Inst &x = B.insts[i];
            if (x.dst >= 0) {
                if (defBlock[x.dst] != -2) err << "value " << x.dst << " defined twice\n";
                defBlock[x.dst] = b;
                defPos[x.dst] = static_cast<int>(i);
            }
            if (isTerminator(x.op) != (i + 1 == B.insts.size())) err << "bad terminator placement in block " << b << "\n";
        }
    }
    auto checkUse = [&](Opnd o, int b, int pos, const char *what) {
        if (o.isConst) return;
        if (o.v < 0 || o.v >= f.nvals) { err << "bad value id in " << what << "\n"; return; }
        int db = defBlock[o.v];
        if (db == -2) { err << "use of undefined value " << o.v << " in block " << b << " (" << what << ")\n"; return; }
        if (db == -1) return;
        if (db == b) {
            if (defPos[o.v] >= pos) err << "use before def of " << o.v << " in block " << b << "\n";
        } else if (!d.dominates(db, b)) {
            err << "def of " << o.v << " (block " << db << ") does not dominate use in block " << b << "\n";
        }
    };
    for (int b : d.rpo) {
        BB &B = f.bb[b];
        for (Phi &p : B.phis) {
            if (p.in.size() != B.preds.size()) err << "phi " << p.dst << " in block " << b << " has " << p.in.size() << " inputs for " << B.preds.size() << " preds\n";
            for (auto &in : p.in) {
                if (std::find(B.preds.begin(), B.preds.end(), in.first) == B.preds.end())
                    err << "phi input from non-pred\n";
                checkUse(in.second, in.first, 1 << 30, "phi");
            }
        }
        for (size_t i = 0; i < B.insts.size(); i++)
            for (int k = 0; k < B.insts[i].n; k++) checkUse(B.insts[i].a[k], b, static_cast<int>(i), opName(B.insts[i].op));
    }
    return err.str();
}

static std::string fmt(Func &f, Opnd o) {
    o = f.resolve(o);
    if (o.isConst) return std::to_string(static_cast<int32_t>(o.c));
    return "%" + std::to_string(o.v);
}

std::string dumpFunc(Func &f) {
    std::ostringstream s;
    s << "func " << f.name << "(";
    for (size_t i = 0; i < f.params.size(); i++) s << (i ? ", %" : "%") << f.params[i];
    s << ")\n";
    for (int b = 0; b < static_cast<int>(f.bb.size()); b++) {
        BB &B = f.bb[b];
        if (!B.alive) continue;
        s << "B" << b << " (" << B.label << ") preds:";
        for (int p : B.preds) s << " B" << p;
        s << " freq=" << B.freq << "\n";
        for (Phi &p : B.phis) {
            s << "  %" << p.dst << " = phi";
            for (auto &in : p.in) s << " [B" << in.first << ": " << fmt(f, in.second) << "]";
            s << "\n";
        }
        for (Inst &x : B.insts) {
            s << "  ";
            if (x.dst >= 0) s << "%" << x.dst << " = ";
            s << opName(x.op);
            for (int k = 0; k < x.n; k++) s << (k ? ", " : " ") << fmt(f, x.a[k]);
            if (x.op == OP_ADDSH) s << ", " << int(x.k);
            if (x.op == OP_JMP) s << " B" << x.tgt[0];
            if (x.op == OP_BR) s << ", B" << x.tgt[0] << ", B" << x.tgt[1];
            s << "\n";
        }
    }
    return s.str();
}

}  // namespace kopt
