#!/usr/bin/env python3
"""Direct tree/pressure scheduling tests against COMP10's official kirlib.

Run: PYTHONDONTWRITEBYTECODE=1 python3 tests/tree_schedule.py
KIT can name an external COMP10 directory; CXX selects the C++17 compiler.
Builds and generated programs live in a temporary directory. No optimizer
candidate selection, sim.cpp execution, or fallback is used as the oracle.
The deep-chain subprocess runs with a 512 KiB stack on POSIX.
"""
import os
from pathlib import Path
import random
import resource
import shlex
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
KIT = Path(os.environ.get("KIT", ROOT.parent / "official-LLH-26/Compilers/COMP10"))
sys.path.insert(0, str(KIT))
import kirlib as K

DRIVER = r'''
#include <algorithm>
#include <cstdlib>
#include <iostream>
#include <iterator>
#include <stdexcept>
#include "backend.h"
#include "passes.h"
using namespace kopt;
static void require(bool ok, const char *why) {
    if (!ok) throw std::runtime_error(why);
}
static bool pure(Op op) {
    switch (op) {
    case OP_MOV: case OP_ADD: case OP_SUB: case OP_MUL: case OP_AND: case OP_OR:
    case OP_XOR: case OP_SHL: case OP_SHR: case OP_LT: case OP_EQ: case OP_SELECT:
    case OP_MAC: case OP_ADDSH: return true;
    default: return false;
    }
}
static bool same(const Inst &a, const Inst &b) {
    if (a.op != b.op || a.dst != b.dst || a.n != b.n || a.k != b.k ||
        a.tgt[0] != b.tgt[0] || a.tgt[1] != b.tgt[1]) return false;
    for (int i = 0; i < 3; ++i) if (a.a[i] != b.a[i]) return false;
    return true;
}
// Check all destinations/operands, exact barrier positions, region membership,
// phi inputs and instruction multiplicity, independently of execution samples.
static void checkPermutation(const Func &old, const Func &now) {
    require(old.nvals == now.nvals && old.params == now.params &&
            old.bb.size() == now.bb.size(), "tree changed CFG/value universe");
    for (size_t b = 0; b < old.bb.size(); ++b) {
        const BB &a = old.bb[b], &z = now.bb[b];
        require(a.alive == z.alive && a.preds == z.preds &&
                a.insts.size() == z.insts.size() && a.phis.size() == z.phis.size(),
                "tree changed block shape");
        for (size_t p = 0; p < a.phis.size(); ++p)
            require(a.phis[p].dst == z.phis[p].dst && a.phis[p].in == z.phis[p].in,
                    "tree changed phi");
        for (size_t i = 0; i < a.insts.size();) {
            if (!a.alive || !pure(a.insts[i].op) || a.insts[i].dst < 0) {
                require(same(a.insts[i], z.insts[i]), "tree moved/changed barrier");
                ++i; continue;
            }
            size_t end = i;
            std::vector<const Inst *> before, after;
            while (end < a.insts.size() && pure(a.insts[end].op) && a.insts[end].dst >= 0) {
                before.push_back(&a.insts[end]); after.push_back(&z.insts[end]); ++end;
            }
            auto byDest = [](const Inst *x, const Inst *y) { return x->dst < y->dst; };
            std::sort(before.begin(), before.end(), byDest);
            std::sort(after.begin(), after.end(), byDest);
            for (size_t j = 0; j < before.size(); ++j)
                require(same(*before[j], *after[j]), "tree lost/duplicated/changed instruction or crossed region");
            i = end;
        }
    }
}
static void guards() {
    // These deliberately malformed direct-API inputs cannot be made through
    // buildSSA. Each invalid six-instruction region must stay untouched.
    for (int kind = 0; kind < 3; ++kind) {
        Func f; f.bb.emplace_back();
        for (int i = 0; i < 8; ++i) f.newVal();
        for (int i = 0; i < 6; ++i) {
            Inst x; x.op = OP_ADD; x.dst = i; x.n = 2;
            x.a[0] = i ? Opnd::val(i - 1) : Opnd::cst(9);
            x.a[1] = Opnd::cst(3); f.bb[0].insts.push_back(x);
        }
        if (kind == 0) f.bb[0].insts[5].dst = 3;  // duplicate definition
        if (kind == 1) f.bb[0].insts[0].a[0] = Opnd::val(5); // forward reference
        if (kind == 2) f.bb[0].insts[0].a[0] = Opnd::val(0); // self reference
        const auto old = f.bb[0].insts;
        require(!schedulePureTrees(f), "invalid region accepted");
        for (size_t i = 0; i < old.size(); ++i)
            require(same(old[i], f.bb[0].insts[i]), "invalid region modified");
    }
    std::cout << "PASS duplicate/forward/self region guards\n";
}
int main(int argc, char **argv) {
    try {
        if (argc == 2 && std::string(argv[1]) == "guards") { guards(); return 0; }
        require(argc == 3, "usage: driver MODE REGISTERS < input.kir");
        const std::string mode = argv[1];
        require(mode == "plain" || mode == "tree" || mode == "pressure" || mode == "combined" || mode == "bottomup" || mode == "bottomupK", "bad mode");
        std::string text((std::istreambuf_iterator<char>(std::cin)), {}), err;
        Program p; Func f;
        require(parseProgram(text, p, err), err.c_str());
        require(buildSSA(p, f, err), err.c_str());
        err = verifyFunc(f); require(err.empty(), err.c_str());
        size_t phis = 0, maxPure = 0;
        for (const BB &b : f.bb) {
            phis += b.phis.size(); size_t run = 0;
            for (const Inst &x : b.insts) {
                run = pure(x.op) && x.dst >= 0 ? run + 1 : 0;
                maxPure = std::max(maxPure, run);
            }
        }
        bool changed = false;
        if (mode == "tree" || mode == "combined") {
            const Func old = f;
            changed = schedulePureTrees(f);
            checkPermutation(old, f);
            err = verifyFunc(f); require(err.empty(), err.c_str());
        }
        Machine m; m.registers = std::atoi(argv[2]);
        BackendOptions opt;
        opt.pressureSchedule = mode == "pressure" || mode == "combined";
        opt.bottomUpSchedule = mode == "bottomup" || mode == "bottomupK";
        opt.preSchedule = opt.pressureSchedule || opt.bottomUpSchedule;
        opt.spillToK = mode == "bottomupK";
        // Exercise these exact transforms, without any SSA optimization pipeline.
        const Program result = lowerToProgram(f, m, opt);
        std::cerr << "changed=" << changed << " phis=" << phis << " maxpure=" << maxPure << '\n';
        std::cout << printProgram(result);
    } catch (const std::exception &e) {
        std::cerr << e.what() << '\n'; return 1;
    }
}
'''

MODES = ("plain", "tree", "pressure", "combined", "bottomup", "bottomupK")
MASK = (1 << 32) - 1


def program(name, body, params="v0,v1,v2,v3"):
    return f"func {name}({params})\nentry:\n" + "\n".join(body) + "\n"


def dag(count, seed=0, base=10):
    """Acyclic mixed operations, deliberately including shared three-way uses."""
    rng = random.Random(seed)
    live = ["v0", "v1", "v2", "v3"]
    out = []
    ops = ("add", "sub", "mul", "xor", "and", "or", "shl", "shr", "lt", "eq",
           "select", "mac", "addsh", "mov")
    for i in range(count):
        dst = f"v{base+i}"
        op = ops[i % len(ops)]
        a, b, c = [rng.choice(live) for _ in range(3)]
        if i % 3 == 0:
            b = c = a  # repeated operands must not duplicate DFS emissions
        args = [a] if op == "mov" else [a, b]
        if op in ("select", "mac"):
            args.append(c)
        if op == "addsh":
            args.append(str(i % 32))
        out.append(f"{op} {dst}, " + ", ".join(args))
        live.append(dst)
    return out


def branch_fixture(count):
    body = dag(count, count)
    # Export a value that has also had a local use, a passing parameter, and
    # values defined on opposite sides of window boundaries.
    body += ["xor v8000, v0, 1", "br v8000, left, right", "left:"]
    body += dag(103, count+1, 1000)
    body += ["add v9000, v10, v105", "add v9000, v9000, v1", "jmp join", "right:"]
    body += dag(97, count+2, 2000)
    body += [f"sub v9000, v{10+count-1}, v106", "jmp join", "join:"]
    body += ["add v9001, v9000, v10", "store 15, v9001", "ret v9001"]
    return program("exports", body)


def loop_fixture():
    body = ["const v7, 4", "mov v8, v2", "jmp loop", "loop:"]
    body += dag(193, 619)
    body += ["add v8, v8, v105", "vstore 3, v8", "sub v7, v7, 1",
             "br v7, loop, done", "done:", "store 14, v8", "ret v8"]
    return program("phi_loop", body)


def barriers_fixture(reverse=False):
    body = dag(97, 17)
    body += ["store 0, v106", "vstore 7, v10", "vload v700, 2"]
    barriers = ["div v701, v2, v1", "load v702, v0", "mod v703, v2, v3"]
    if reverse:
        barriers.reverse()
    for j, barrier in enumerate(barriers):
        # Alternating short/long regions also exercise stamp reuse after skips.
        body += dag((5, 6, 193)[j], 20+j, 1000+j*300)
        body += [barrier, f"vstore {8+j}, v700", f"store {20+j}, v700"]
    body += ["store v0, v700", "load v704, 0", "vstore 12, v704"]
    body += dag(7, 29, 3000)
    body += ["mac v710, v701, v702, v703", "select v711, v700, v710, v704",
             "store 30, v711", "ret v711"]
    return program("barriers", body)


def pressure_fixture(count=900):
    body = []
    for i in range(count):
        body += [f"xor v{10+i}, v0, {i+1}", f"mul v{10+i}, v{10+i}, v{10+i}"]
    body += ["const v9000, 0"]
    body += [f"add v9000, v9000, v{10+i}" for i in range(count)]
    return program("producer_first", body + ["ret v9000"])


def deep_fixture(count=100000):
    body = ["xor v10, v0, 17", "xor v20, v1, 37", "mul v21, v2, 13",
            "add v22, v20, v21"]
    previous = "v22"
    for i in range(count):
        dst = f"v{100+i}"
        body.append(f"xor {dst}, {previous}, {i+1}")
        previous = dst
    # The deep subtree must be visited first; the independent early leaf moves.
    return program("deep", body + [f"add v999998, {previous}, v10", "ret v999998"])


def small_stack():
    _, hard = resource.getrlimit(resource.RLIMIT_STACK)
    limit = 512 * 1024
    resource.setrlimit(resource.RLIMIT_STACK, (min(limit, hard) if hard >= 0 else limit, hard))


def lower(binary, text, mode, registers=8, deep=False):
    out = subprocess.run([str(binary), mode, str(registers)], input=text,
                         capture_output=True, text=True, timeout=90,
                         preexec_fn=small_stack if deep else None)
    assert out.returncode == 0, (mode, out.returncode, out.stderr)
    meta = dict(item.split("=") for item in out.stderr.split())
    return out.stdout, {k: int(v) for k, v in meta.items()}


def samples():
    rng = random.Random(718903)
    edges = [0, 1, 2, 31, 32, 0x7fffffff, 0x80000000, MASK]
    args = [(x, x, x, x) for x in edges]
    args += [(rng.getrandbits(32), rng.getrandbits(32), rng.getrandbits(32),
              rng.getrandbits(32)) for _ in range(24)]
    # Reach each barrier, each trap kind, signed division corner cases, both
    # branch outcomes, pointer aliases, scratch reads and empty/nonempty queues.
    args += [(ptr, div, value, mod) for ptr in (0, 1, 4095, 4096)
             for div, value, mod in ((0, 7, 2), (2, MASK, 0), (MASK, 0x80000000, 3))]
    args += [(0, 2, 7, 3), (1, 2, 7, 3), (3072, 2, 7, 3), (MASK, 2, 7, 3)]
    return [(list(a), [(0, [13, 29, 47]), (3072, [71]), (4095, [83])],
             {2: [] if i % 2 else [0x80000000, 9, 0]}) for i, a in enumerate(args)]


def execute(cp, inp, trace=False):
    args, memory, vin = inp
    result = K.execute(cp, args, memory, vin, 1000000, want_trace=trace)
    assert result.status != "TIMEOUT", "unexpected test timeout"
    return result


def main():
    checks = 0
    inputs = samples()
    fixtures = []
    # Body counts straddle both sides of each 96-instruction boundary.
    for count in (95, 96, 97, 191, 192, 193, 385):
        text = program("mixed", dag(count, count) +
                       [f"store 12, v{10+count-1}", "store 13, v10", f"ret v{10+count-2}"])
        fixtures.append((f"dag-{count}", text, False))
    for count in (96, 97, 192, 193):
        fixtures.append((f"exports-phi-{count}", branch_fixture(count), True))
    fixtures += [("loop-phi", loop_fixture(), True),
                 ("barriers-div-first", barriers_fixture(), False),
                 ("barriers-mod-first", barriers_fixture(True), False),
                 ("trap-terminator", program("explicit", dag(193, 933) + ["trap v106"]), False),
                 ("three-shared", program("shared", [
                     "xor v10, v0, v1", "add v11, v2, v3", "mul v12, v10, v10",
                     "mac v13, v10, v11, v10", "mac v14, v12, v12, v12",
                     "select v15, v13, v13, v14", "select v16, v14, v13, v13",
                     "addsh v17, v16, v16, 31", "sub v18, v15, v17",
                     "store 10, v18", "ret v18"]), False)]
    with tempfile.TemporaryDirectory(prefix="kopt-tree-tests-") as temp:
        td = Path(temp)
        source, binary = td / "driver.cpp", td / "driver"
        source.write_text(DRIVER)
        sources = sorted(str(p) for p in (ROOT / "src").glob("*.cpp")
                         if p.name not in ("main.cpp", "optimizer.cpp"))
        subprocess.run([*shlex.split(os.environ.get("CXX", "c++")), "-std=c++17", "-O1",
                        "-Wall", "-Wextra", "-Werror", "-pedantic", "-I"+str(ROOT / "src"),
                        str(source), *sources, "-o", str(binary)], check=True)
        guard = subprocess.run([str(binary), "guards"], capture_output=True, text=True, check=True)
        print(guard.stdout.strip(), flush=True)
        tree_changes = 0
        observed = set()
        for name, text, require_phi in fixtures:
            original = K.compile_program(K.parse_program(text))
            references = [execute(original, inp) for inp in inputs]
            for r in references:
                observed.add((r.status, str(r.value) if r.status == "TRAP" else "return"))
            for mode in MODES:
                candidate, meta = lower(binary, text, mode, registers=4)
                assert not require_phi or meta["phis"] > 0, (name, "phi coverage absent")
                if mode in ("tree", "combined"):
                    tree_changes += meta["changed"]
                compiled = K.compile_program(K.parse_program(candidate))
                for inp, reference in zip(inputs, references):
                    actual = execute(compiled, inp)
                    diff = K.first_difference(reference, actual)
                    assert not diff, (name, mode, inp, diff, candidate)
                    checks += 1
            print("PASS", name, "(all six direct modes)", flush=True)
        assert tree_changes > 0, "tree transform never exercised"
        assert ("TRAP", "div_by_zero") in observed and ("TRAP", "bad_address") in observed
        assert any(status == "TRAP" and value.startswith("explicit(") for status, value in observed)

        text = pressure_fixture()
        original = K.compile_program(K.parse_program(text))
        cycle_inputs = inputs[:8]
        references = [execute(original, inp) for inp in cycle_inputs]
        cycle_counts, register_counts = {}, {}
        machine = K.load_machine(str(KIT / "machines/machine_default.cfg"))
        for mode in MODES:
            candidate, meta = lower(binary, text, mode)
            if mode in ("tree", "combined"):
                assert meta["changed"] == 1, "producer-first tree was not reordered"
            compiled = K.compile_program(K.parse_program(candidate))
            total = 0
            for inp, reference in zip(cycle_inputs, references):
                actual = execute(compiled, inp, trace=True)
                diff = K.first_difference(reference, actual)
                assert not diff, ("producer-first", mode, inp, diff)
                total += K.time_trace(compiled, actual.trace, machine)
                checks += 1
            cycle_counts[mode] = total
            register_counts[mode] = compiled.nregs
        assert cycle_counts["tree"] < cycle_counts["plain"], cycle_counts
        assert cycle_counts["combined"] < cycle_counts["plain"], cycle_counts
        assert register_counts["tree"] < register_counts["plain"], register_counts
        print("PASS producer-first-900 official cycles:", cycle_counts,
              "registers:", register_counts, flush=True)

        text = deep_fixture()
        original = K.compile_program(K.parse_program(text))
        deep_inputs = [inputs[i] for i in (0, 6, 7)]
        references = [execute(original, inp) for inp in deep_inputs]
        for mode in ("tree", "combined", "bottomup"):
            candidate, meta = lower(binary, text, mode, deep=True)
            assert meta["maxpure"] >= 100000, meta
            if mode != "bottomup": assert meta["changed"] == 1, meta
            compiled = K.compile_program(K.parse_program(candidate))
            for inp, reference in zip(deep_inputs, references):
                actual = execute(compiled, inp)
                diff = K.first_difference(reference, actual)
                assert not diff, ("deep-100k", mode, inp, diff)
                checks += 1
        print("PASS deep-100000 tree + combined + bottom-up lowering with 512 KiB stack", flush=True)
    print(f"PASS {checks} official-interpreter comparisons; region permutation, SSA, "
          "barrier positions, window edges, phi/liveOut, terminators and deep DFS checked")


if __name__ == "__main__":
    main()
