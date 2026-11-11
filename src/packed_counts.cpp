// Accumulate bounded indexed increments in packed register fields, then
// apply the deltas on the loop exit edge.
#include "passes.h"
#include "cfg.h"

#include <array>
#include <vector>

namespace kopt {
namespace {

bool ordinaryArithmetic(Op op) {
    switch (op) {
    case OP_CONST: case OP_MOV: case OP_ADD: case OP_SUB: case OP_MUL:
    case OP_AND: case OP_OR: case OP_XOR: case OP_SHL: case OP_SHR:
    case OP_LT: case OP_EQ: case OP_SELECT: case OP_MAC: case OP_ADDSH:
        return true;
    default:
        return false;
    }
}

bool splitConstant(const Inst *x, Op op, Opnd &value, uint32_t &constant) {
    if (!x || x->op != op || x->a[0].isConst == x->a[1].isConst) return false;
    const int side = x->a[0].isConst ? 0 : 1;
    constant = x->a[side].c;
    value = x->a[1 - side];
    return true;
}

Opnd emit(Func &f, std::vector<Inst> &code, Op op, Opnd a, Opnd b = {},
          Opnd c = {}) {
    Inst x;
    x.op = op;
    x.dst = f.newVal();
    x.n = op == OP_LOAD ? 1 : (op == OP_SELECT ? 3 : 2);
    x.a[0] = a;
    x.a[1] = b;
    x.a[2] = c;
    code.push_back(x);
    return Opnd::val(x.dst);
}

}  // namespace

bool packIndexedCounts(Func &f) {
    if (f.bb.size() > 64 || f.nvals > 1024) return false;
    f.resolveAll();
    f.rebuildPreds();
    const DomInfo dom = computeDominators(f);
    const LoopInfo loops = computeLoops(f, dom);

    std::vector<int> sites(f.nvals, -1);
    std::vector<const Inst *> definitions(f.nvals, nullptr);
    std::vector<int> uses(f.nvals, 0);
    for (int b = 0; b < static_cast<int>(f.bb.size()); ++b) {
        if (!f.bb[b].alive) continue;
        for (const Phi &phi : f.bb[b].phis) {
            sites[phi.dst] = b;
            for (const auto &edge : phi.in) if (!edge.second.isConst) ++uses[edge.second.v];
        }
        for (const Inst &x : f.bb[b].insts) {
            if (x.dst >= 0) {
                sites[x.dst] = b;
                definitions[x.dst] = &x;
            }
            for (int a = 0; a < x.n; ++a) if (!x.a[a].isConst) ++uses[x.a[a].v];
        }
    }
    const auto def = [&](Opnd o) { return o.isConst ? nullptr : definitions[o.v]; };

    for (const auto &loop : loops.loops) {
        if (loop.blocks.size() != 2 || loop.latches.size() != 1) continue;
        const int head = loop.header, body = loop.latches[0];
        const BB &h = f.bb[head], &b = f.bb[body];
        if (head == body || h.preds.size() != 2 || b.preds != std::vector<int>{head} ||
            !b.phis.empty() || h.term().op != OP_BR || h.term().tgt[0] != body ||
            b.term().op != OP_JMP || b.term().tgt[0] != head) continue;
        const int exit = h.term().tgt[1];
        if (exit == body || exit == head) continue;
        const int entry = h.preds[0] == body ? h.preds[1] : h.preds[0];

        const Inst *test = def(h.term().a[0]);
        if (!test || test->op != OP_LT || test->a[0].isConst) continue;
        const Opnd index = test->a[0], limit = test->a[1];
        uint32_t maximum = 0;
        if (limit.isConst) {
            maximum = limit.c;
        } else {
            // The bound is invariant and has an independent unsigned cap.
            const int site = sites[limit.v];
            if (site < 0 || site == head || !dom.dominates(site, head)) continue;
            Opnd ignored;
            if (!splitConstant(def(limit), OP_AND, ignored, maximum)) continue;
        }
        if (maximum == 0 || maximum > 255) continue;

        bool unitCounter = false;
        for (const Phi &phi : h.phis) {
            if (phi.dst != index.v || phi.in.size() != 2) continue;
            Opnd next;
            bool zeroEntry = false;
            for (const auto &edge : phi.in) {
                if (edge.first == entry) zeroEntry = edge.second.isC(0);
                if (edge.first == body) next = edge.second;
            }
            Opnd previous;
            uint32_t step;
            unitCounter = zeroEntry && splitConstant(def(next), OP_ADD, previous, step) &&
                          previous == index && step == 1;
        }
        if (!unitCounter) continue;

        bool safe = true;
        for (size_t i = 0; i + 1 < h.insts.size(); ++i)
            if (!ordinaryArithmetic(h.insts[i].op)) safe = false;
        const Inst *store = nullptr;
        int loads = 0;
        for (size_t i = 0; i + 1 < b.insts.size(); ++i) {
            const Inst &x = b.insts[i];
            if (x.op == OP_LOAD) {
                ++loads;
            } else if (x.op == OP_STORE && !store) {
                store = &x;
            } else if (!ordinaryArithmetic(x.op)) {
                safe = false;
            }
        }
        if (!safe || !store || loads != 2) continue;

        const Inst *increment = def(store->a[1]);
        Opnd oldCount;
        uint32_t step;
        if (!splitConstant(increment, OP_ADD, oldCount, step) || step != 1 ||
            uses[increment->dst] != 1 || uses[oldCount.v] != 1) continue;
        const Inst *countLoad = def(oldCount);
        if (!countLoad || countLoad->op != OP_LOAD || sites[oldCount.v] != body ||
            sites[increment->dst] != body || countLoad->a[0] != store->a[0]) continue;

        Opnd key, data;
        uint32_t binBase, mask;
        if (!splitConstant(def(store->a[0]), OP_ADD, key, binBase) ||
            !splitConstant(def(key), OP_AND, data, mask) ||
            (mask != 1 && mask != 3 && mask != 7)) continue;
        const Inst *input = def(data);
        if (!input || input->op != OP_LOAD || input == countLoad || sites[data.v] != body) continue;
        uint32_t inputBase = 0;
        if (input->a[0] != index) {
            Opnd addressIndex;
            if (!splitConstant(def(input->a[0]), OP_ADD, addressIndex, inputBase) ||
                addressIndex != index) continue;
        }
        if (uint64_t(inputBase) + maximum > kMemWords || uint64_t(binBase) + mask >= kMemWords ||
            !(inputBase + maximum <= binBase || binBase + mask < inputBase)) continue;

        const int bins = static_cast<int>(mask + 1);
        const int width = bins == 2 ? 16 : (bins == 8 && maximum <= 15 ? 4 : 8);
        const int perWord = 32 / width;
        const int words = (bins + perWord - 1) / perWord;
        const unsigned shift = width == 16 ? 4 : (width == 8 ? 3 : 2);
        std::array<Val, 2> counters{};
        for (int word = 0; word < words; ++word) counters[word] = f.newVal();

        // All body computations except the bin load, increment, and store
        // keep their original values. The sole remaining read is disjoint.
        std::vector<Inst> updated;
        for (size_t i = 0; i + 1 < b.insts.size(); ++i) {
            const Inst &x = b.insts[i];
            if (&x != store && &x != countLoad && &x != increment) updated.push_back(x);
        }
        // A Kiln shift uses only the low five bits of its count. Scaling by
        // field width maps the source's low key bits to one position in a word.
        const Opnd scaled = emit(f, updated, OP_SHL, data, Opnd::cst(shift));
        const Opnd unit = emit(f, updated, OP_SHL, Opnd::cst(1), scaled);
        Opnd upper;
        if (words == 2) upper = emit(f, updated, OP_AND, data, Opnd::cst(perWord));
        std::vector<Phi> phis;
        for (int word = 0; word < words; ++word) {
            Opnd contribution = unit;
            if (words == 2)
                contribution = emit(f, updated, OP_SELECT, upper,
                                    word ? unit : Opnd::cst(0), word ? Opnd::cst(0) : unit);
            const Opnd next = emit(f, updated, OP_ADD, Opnd::val(counters[word]), contribution);
            phis.push_back(Phi{counters[word], {{entry, Opnd::cst(0)}, {body, next}}});
        }
        updated.push_back(b.term());

        BB flush;
        flush.freq = f.bb[exit].freq;
        flush.loopDepth = f.bb[exit].loopDepth;
        const uint32_t fieldMask = (uint32_t{1} << width) - 1;
        for (int bin = 0; bin < bins; ++bin) {
            Opnd count = Opnd::val(counters[bin / perWord]);
            const unsigned offset = (bin % perWord) * width;
            if (offset != 0) count = emit(f, flush.insts, OP_SHR, count, Opnd::cst(offset));
            if (offset + width < 32)
                count = emit(f, flush.insts, OP_AND, count, Opnd::cst(fieldMask));
            const Opnd address = Opnd::cst(binBase + bin);
            const Opnd initial = emit(f, flush.insts, OP_LOAD, address);
            const Opnd sum = emit(f, flush.insts, OP_ADD, initial, count);
            Inst write;
            write.op = OP_STORE;
            write.n = 2;
            write.a[0] = address;
            write.a[1] = sum;
            flush.insts.push_back(write);
        }
        Inst jump;
        jump.op = OP_JMP;
        jump.tgt[0] = exit;
        flush.insts.push_back(jump);

        const int flushId = static_cast<int>(f.bb.size());
        f.bb[body].insts.swap(updated);
        auto &header = f.bb[head];
        header.phis.insert(header.phis.end(), phis.begin(), phis.end());
        header.term().tgt[1] = flushId;
        for (Phi &phi : f.bb[exit].phis)
            for (auto &edge : phi.in) if (edge.first == head) edge.first = flushId;
        f.bb.push_back(std::move(flush));
        f.rebuildPreds();
        clearIVRanges();
        dce(f);
        return true;
    }
    return false;
}

}  // namespace kopt
