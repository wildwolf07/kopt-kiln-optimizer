#!/usr/bin/env python3
"""Direct counted-loop API regression test; no optimizer.cpp wiring required.

Run: PYTHONDONTWRITEBYTECODE=1 python3 tests/counted_loops.py
Whole-pipeline tests against an already built integrated optimizer:
  python3 tests/counted_loops.py --integrated-bin /path/to/build/kopt-bin
Add --integrated-only to skip the original 4245 direct comparisons.
KIT may name an external COMP10 kit. All generated files/builds live in a temp
directory. Equivalence is checked by the official Python interpreter, not sim.cpp.
"""
import argparse
import os
from pathlib import Path
import random
import re
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
KIT = Path(os.environ.get("KIT", ROOT.parent / "official-LLH-26/Compilers/COMP10"))
sys.path.insert(0, str(KIT))
import kirlib as K  # noqa: E402

DRIVER = r'''
#include <cassert>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <iterator>
#include "loops.h"
#include "backend.h"
#include "passes.h"
using namespace kopt;
int main(int argc, char **argv) {
    assert(argc == 5);
    std::ifstream in(argv[1]);
    std::string text((std::istreambuf_iterator<char>(in)), {}), err;
    Program p; assert(parseProgram(text, p, err));
    std::vector<uint32_t> names;
    Func f = toRegisterForm(p, names);
    const auto oldNames = names;
    const auto oldSize = f.bb.size();
    const int oldVals = f.nvals;
    const auto original = printProgram(fromRegisterForm(f, names));
    const int budget = std::atoi(argv[3]);
    const std::string mode = argv[4];
    const bool unswitch = mode == "unswitch" || mode == "unswitch-lower";
    const bool changed = unswitch ? unswitchLoops(f, budget) :
        unrollCountedLoops(f, names, std::atoi(argv[2]), budget);
    assert(f.nvals == static_cast<int>(names.size()));
    size_t instructions = 0;
    for (const BB &b : f.bb) instructions += b.insts.size();
    if (changed) {
        assert(instructions - p.instrCount() <= static_cast<size_t>(budget));
        if (unswitch) {
            assert(names == oldNames && f.nvals == oldVals);
            assert(f.bb.back().term().op == OP_BR);
        } else {
            assert(f.bb[oldSize + 1].term().op == OP_JMP);
            for (const Inst &x : f.bb[oldSize + 1].insts) assert(x.op != OP_BR);
        }
    } else {
        assert(names == oldNames && f.nvals == oldVals && f.bb.size() == oldSize);
        assert(printProgram(fromRegisterForm(f, names)) == original);
    }
    Program out = fromRegisterForm(f, names);
    Func ssa; assert(buildSSA(out, ssa, err));
    err = verifyFunc(ssa);
    if (!err.empty()) { std::cerr << err; return 2; }
    if (mode == "lower" || mode == "unswitch-lower") {
        // Exercise the existing cleanup, allocator and scheduler on the new CFG.
        simplifyCFG(ssa);
        for (int round = 0; round < 4; round++) {
            computeIVRanges(ssa); sccp(ssa); combineLinear(ssa); simplifyCFG(ssa);
            instSimplify(ssa); gvn(ssa); instSimplify(ssa); dce(ssa);
            deadStores(ssa); simplifyCFG(ssa); licm(ssa);
        }
        strengthReduce(ssa); instSimplify(ssa); gvn(ssa); dce(ssa);
        reassociate(ssa); instSimplify(ssa); gvn(ssa); licm(ssa); dce(ssa);
        Machine m;
        fuseOps(ssa, m); ifConvert(ssa, m); instSimplify(ssa); dce(ssa); simplifyCFG(ssa);
        err = verifyFunc(ssa);
        if (!err.empty()) { std::cerr << err; return 3; }
        out = lowerToProgram(ssa, m, BackendOptions());
    }
    std::cerr << (changed ? "changed" : "unchanged") << '\n';
    std::cout << printProgram(out);
}
'''


def loop(step=1, bound="v1", work=None):
    if work is None:
        work = "add v11, v11, v10"
    return f"""func counted(v0, v1, v2, v3)
entry:
  mov v10, v0
  const v11, 0
  jmp head
head:
  lt v12, v10, {bound}
  br v12, body, done
body:
  {work}
  add v10, v10, {step}
  jmp head
done:
  store 0, v10
  store 1, v12
  ret v11
"""


def integrated_tests(td, driver, optimizer):
    """Check winners AND every dumped candidate, so fallback cannot hide bugs.

Also feed a directly unrolled source through the real optimizer again: its
rotation/threading plans then see the counted guard, chunk and scalar remainder.
"""
    lo, hi = -(1 << 31), (1 << 31) - 1
    near_min = loop(work="vstore 2, v12\n  const v12, 99\n  add v11, v11, v10")
    wrap = loop(2, work="""store 10, v11
  vstore 2, v12
  sub v14, 17, v11
  div v15, 1, v14
  add v11, v11, 1""")
    guarded = loop(work="""store 10, v11
  vstore 2, v12
  vload v14, 3
  vstore 2, v14
  div v15, 1, v14
  add v11, v11, 1""")
    inputs_min = [([lo, lo + n, 0, 0], {}) for n in range(18)]
    inputs_min += [([hi, lo, 0, 0], {}), ([lo + 10, lo + 5, 0, 0], {}),
                   ([hi - 12, hi, 0, 0], {})]
    inputs_wrap = [([hi - (factor - 1) * 2 - 1, hi, 0, 0], {})
                   for factor in (2, 4, 8)] + [([lo, hi, 0, 0], {})]
    inputs_guard = [([i, n, 0, 0], {3: queue})
                    for i, n in ((0, 0), (hi, lo), (0, 33), (lo, lo + 1),
                                 (lo, lo + 17))
                    for queue in ([], [0], [19, 23, 29, 31, 37])]
    fixtures = [("near-min", near_min, inputs_min), ("final-wrap", wrap, inputs_wrap),
                ("guarded-vlog", guarded, inputs_guard)]
    checks = runs = candidates = 0
    factors_seen = set()
    pre_seen = False
    # Both register pressure and preallocation scheduling affect the new CFG.
    machines = ("machine_default.cfg", "machine_few_registers.cfg")
    clean_env = {k: v for k, v in os.environ.items() if not k.startswith("KOPT_")}
    for name, text, inputs in fixtures:
        src = td / (name + ".kir")
        src.write_text(text)
        generated = subprocess.run([str(driver), str(src), "8", "512", "raw"],
                                   capture_output=True, text=True, check=True)
        assert generated.stderr.strip() == "changed", generated.stderr
        cp = K.compile_program(K.parse_program(text))
        references = []
        for args, vin in inputs:
            result = K.execute(cp, [x & 0xFFFFFFFF for x in args], [(10, [123])], vin, 12000)
            assert result.status != "TIMEOUT", (name, args)
            references.append(result)
        if name == "final-wrap":
            assert all(r.status == "TRAP" and r.value == "div_by_zero" and r.mem[10] == 17
                       and len(r.vlog) == 18 for r in references)
        if name == "guarded-vlog":
            assert all(r.status == "RET" and not r.vlog for r in references[:6])
            assert any(r.status == "TRAP" and r.value == "div_by_zero" for r in references)
        for source_kind, source_text in (("original", text), ("counted-source", generated.stdout)):
            for machine in machines:
                mc_path = KIT / "machines" / machine
                mc = K.load_machine(str(mc_path))
                for preschedule in (False, True):
                    run = td / f"integrated-{runs}"
                    run.mkdir()
                    dumps = run / "dumps"
                    dumps.mkdir()
                    source = run / "in.kir"
                    source.write_text(source_text)
                    output = run / "out.kir"
                    env = dict(clean_env, KOPT_STRICT="1", KOPT_DUMP=str(dumps))
                    if not preschedule:
                        env["KOPT_DISABLE"] = "preschedule"
                    result = subprocess.run([str(optimizer), str(source), "--machine", str(mc_path),
                                             "-o", str(output)], capture_output=True, text=True,
                                            env=env, timeout=30)
                    context = (name, source_kind, machine, preschedule)
                    assert result.returncode == 0, (context, result.stderr)
                    dumped = sorted(dumps.glob("cand*.kir"))
                    assert dumped, (context, "no candidates dumped")
                    tags = [p.read_text().splitlines()[0] for p in dumped]
                    factors_seen.update(int(x) for tag in tags for x in re.findall(r"/counted(2|4|8)", tag))
                    if preschedule:
                        assert any(any(marker in tag for marker in ("+pre", "+S", "+KS", "+spread", "+Kspread"))
                                   for tag in tags), context
                        pre_seen = True
                    else:
                        assert not any(any(marker in tag for marker in ("+pre", "+S", "+KS", "+spread", "+Kspread"))
                                       for tag in tags), context
                    for path in [output, *dumped]:
                        program = K.load_program(str(path))
                        K.check_machine_features(program, mc)
                        candidate = K.compile_program(program)
                        for (args, vin), reference in zip(inputs, references):
                            actual = K.execute(candidate, [x & 0xFFFFFFFF for x in args],
                                               [(10, [123])], vin, 20 * reference.steps + 1000)
                            diff = K.first_difference(reference, actual)
                            assert not diff, (context, path.name, args, vin, diff,
                                              path.read_text().splitlines()[0])
                            checks += 1
                    candidates += len(dumped)
                    runs += 1
    assert factors_seen == {2, 4, 8} and pre_seen, (factors_seen, pre_seen)
    print(f"integrated: {checks} official comparisons, {runs} optimizer runs, "
          f"{candidates} dumped candidates; counted2/4/8 and preschedule on/off covered")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--integrated-bin", type=Path, help="already built real optimizer binary")
    parser.add_argument("--integrated-only", action="store_true")
    args = parser.parse_args()
    if args.integrated_only and not args.integrated_bin:
        parser.error("--integrated-only requires --integrated-bin")
    checks = variants = rejects = 0
    rng = random.Random(0xC017ED)
    lo, hi = -(1 << 31), (1 << 31) - 1
    with tempfile.TemporaryDirectory(prefix="kopt-counted-") as temp:
        td = Path(temp)
        (td / "driver.cpp").write_text(DRIVER)
        binary = td / "driver"
        sources = ["loops", "cfg", "kir", "ssa", "passes", "sim", "backend"]
        subprocess.run([os.environ.get("CXX", "c++"), "-std=c++17", "-O1", "-g",
                        "-Wall", "-Wextra", "-pedantic", "-I", str(ROOT / "src"),
                        str(td / "driver.cpp"),
                        *[str(ROOT / "src" / (s + ".cpp")) for s in sources],
                        "-o", str(binary)], check=True)
        if args.integrated_bin:
            integrated_tests(td, binary, args.integrated_bin.resolve())
            if args.integrated_only:
                return

        def transform(text, factor, budget=512, expect=True, mode="raw"):
            nonlocal variants, rejects
            src = td / "input.kir"
            src.write_text(text)
            p = subprocess.run([str(binary), str(src), str(factor), str(budget), mode],
                               capture_output=True, text=True, check=True)
            assert p.stderr.strip() == ("changed" if expect else "unchanged"), p.stderr
            variants += 1
            rejects += not expect
            return K.compile_program(K.parse_program(p.stdout))

        def equivalent(a, b, inputs):
            nonlocal checks
            for args in inputs:
                args = [x & 0xFFFFFFFF for x in args]
                vin = {3: [19, 23, 29, 31, 37]}
                segs = [(10, [7, 11, 13])]
                x = K.execute(a, args, segs, vin, 12000)
                assert x.status != "TIMEOUT", args
                y = K.execute(b, args, segs, vin, 20 * x.steps + 1000)
                diff = K.first_difference(x, y)
                assert not diff, (args, diff)
                checks += 1

        effect_work = """vstore 2, v12
  const v12, 99
  vstore 2, v12
  vload v14, 3
  add v11, v11, v14
  store 10, v11
  load v15, 10
  add v11, v15, v10"""
        # Forced finite trap after six iterations, even after the final increment
        # of a full group crosses INT_MAX. Stores/vlog must match at the trap.
        trap_work = """store 10, v11
  vstore 2, v12
  sub v14, 5, v11
  div v15, 1, v14
  add v11, v11, 1"""
        memory_work = """store 10, v11
  vstore 2, v12
  add v14, v11, v2
  load v15, v14
  add v11, v11, 1"""
        for factor in (2, 3, 4, 8):
            for step in (1, 2, 7, 65536):
                offset = (factor - 1) * step
                inputs = [[i, n, 0, 0] for i, n in (
                    (hi, lo), (0, -1), (0, 0), (lo, lo), (hi, hi),
                    (lo, lo + offset - 1), (lo, lo + offset),
                    (lo, lo + offset + 1), (-offset - 1, 0),
                    (-offset, 0), (-offset + 1, 0), (hi - offset, hi))]
                for _ in range(50):
                    start = rng.randint(lo, hi - 100 * step)
                    inputs.append([start, start + rng.randint(-1, 32) * step, 0, 0])
                for work in (None, effect_work):
                    text = loop(step, work=work)
                    a = K.compile_program(K.parse_program(text))
                    for mode in ("raw", "lower"):
                        b = transform(text, factor, mode=mode)
                        equivalent(a, b, inputs)
                text = loop(step, work=trap_work)
                a = K.compile_program(K.parse_program(text))
                for mode in ("raw", "lower"):
                    b = transform(text, factor, mode=mode)
                    equivalent(a, b, [[hi - offset - 1, hi, 0, 0], [lo, hi, 0, 0],
                                      [0, 20 * step, 0, 0]])
                text = loop(step, work=memory_work)
                a = K.compile_program(K.parse_program(text))
                b = transform(text, factor)
                equivalent(a, b, [[0, 20 * step, 4094, 0], [lo, hi, 4094, 0]])

            for bound in (lo, lo + factor - 2, lo + factor - 1, lo + factor,
                          -1, 0, 33, hi):
                text = loop(bound=str(bound))
                a = K.compile_program(K.parse_program(text))
                b = transform(text, factor, expect=bound >= lo + factor - 1)
                equivalent(a, b, [[i, 0, 0, 0] for i in
                                  (max(lo, bound - 17), bound, min(hi, bound + 1), hi)])

        # The header compare may be read AND clobbered in B; it is also read on
        # the exit. Sparse names must not allocate the illegal register 1000000.
        text = loop(work=effect_work).replace("v11", "v999999")
        b = transform(text, 4)
        equivalent(K.compile_program(K.parse_program(text)), b,
                   [[-10, 13, 0, 0], [lo, lo + 7, 0, 0], [hi, lo, 0, 0]])
        # Constant-first induction addition is equivalent and is accepted.
        text = loop().replace("add v10, v10, 1", "add v10, 1, v10")
        b = transform(text, 4)
        equivalent(K.compile_program(K.parse_program(text)), b, [[0, 13, 0, 0]])
        # Multiple external entries, with a branch that also has a bypass edge.
        text = loop().replace("  jmp head\nhead:", """  br v2, left, right
left:
  jmp head
right:
  br v3, head, done
head:""", 1)
        b = transform(text, 4)
        equivalent(K.compile_program(K.parse_program(text)), b,
                   [[0, 13, a, c] for a in (0, 1) for c in (0, 1)])

        for factor, step in ((2, hi), (3, hi // 2), (8, hi // 7)):
            text = loop(step, work=trap_work)
            a = K.compile_program(K.parse_program(text))
            for mode in ("raw", "lower"):
                b = transform(text, factor, mode=mode)
                equivalent(a, b, [[lo, hi, 0, 0], [lo, -1, 0, 0]])

        # Two eligible loops: at budget 24 either fits individually, but only
        # one may be transformed because each adds 19 instructions.
        text = loop().replace("done:\n", """done:
  const v10, 0
  jmp head2
head2:
  lt v12, v10, v1
  br v12, body2, done2
body2:
  add v11, v11, v10
  add v10, v10, 1
  jmp head2
done2:
""")
        b = transform(text, 4, budget=24)
        assert b.opnames.count("br") == 4
        equivalent(K.compile_program(K.parse_program(text)), b, [[0, 13, 0, 0]])

        invalid = [
            loop(step=0), loop(step=-1), loop(step=2147483648),
            loop(step=2147483647),  # (factor-1)*step cannot be represented
            loop().replace("  lt v12", "  vstore 5, v11\n  lt v12"),
            loop().replace("  br v12, body, done", "  br v12, done, body"),
            loop().replace("lt v12, v10, v1", "lt v10, v10, v1").replace("br v12", "br v10"),
            loop().replace("lt v12, v10, v1", "lt v1, v10, v1").replace("br v12", "br v1"),
            loop(bound="v10"), loop(work="add v1, v1, 0"),
            loop(work="add v10, v10, 1"),
            loop().replace("add v10, v10, 1", "mov v10, v2"),
            loop().replace("  jmp head\ndone:", "  br v2, head, done\ndone:"),
        ]
        for text in invalid:
            transform(text, 4, expect=False)
        for factor, budget in ((0, 512), (1, 512), (4, 0), (4, 23), (2147483647, 512)):
            transform(loop(), factor, budget, expect=False)
        # Minimal dynamic-bound loop footprint is exactly 24 instructions at U=4.
        transform(loop(), 4, 24)
        unswitch_source = """func unswitch(v0, v1, v2, v3)
entry:
  const v10, 0
  const v11, 0
  jmp head
head:
  lt v12, v10, v0
  br v12, guard, done
guard:
  store 10, v10
  vstore 2, v12
  br v1, risky, safe
risky:
  vload v14, 3
  div v15, v14, v2
  store v3, v15
  add v11, v11, v15
  jmp latch
safe:
  add v11, v11, 7
  jmp latch
latch:
  br v1, inc_true, inc_false
inc_true:
  vstore 9, v1
  add v10, v10, 1
  jmp head
inc_false:
  add v10, v10, 1
  jmp head
done:
  store 0, v10
  store 1, v12
  ret v11
"""
        original = K.compile_program(K.parse_program(unswitch_source))
        unswitch_inputs = [[n, flag, divisor, addr]
                           for n in (-1, 0, 1, 5, 17)
                           for flag in (0, 1, 2, -1, lo)
                           for divisor in (0, 1, 7)
                           for addr in (20, 4096)]
        for mode in ("unswitch", "unswitch-lower"):
            candidate = transform(unswitch_source, 0, mode=mode)
            equivalent(original, candidate, unswitch_inputs)
        # This loop has no invariant branch condition, and the branch flag may
        # not be written even if the write leaves its value unchanged.
        transform(loop(), 0, mode="unswitch", expect=False)
        transform(unswitch_source.replace("  store 10, v10", "  mov v1, v1\n  store 10, v10"),
                  0, mode="unswitch", expect=False)
        transform(unswitch_source.replace("  jmp head\nhead:", "  br v3, head, safe\nhead:", 1),
                  0, mode="unswitch", expect=False)
        transform(unswitch_source, 0, budget=1, mode="unswitch", expect=False)
        # Original loop as entry is deliberately unsupported.
        entry_loop = """func entry_loop(v0, v1)
head:
  br v1, body, done
body:
  add v0, v0, 1
  jmp head
done:
  ret v0
"""
        transform(entry_loop, 0, mode="unswitch", expect=False)
        # Useful in the actual cycle model after register allocation/scheduling.
        text = loop()
        a = transform(text, 1, expect=False, mode="lower")
        b = transform(text, 4, mode="lower")
        machine = K.load_machine(str(KIT / "machines/machine_default.cfg"))
        cycles = []
        for program in (a, b):
            result = K.execute(program, [0, 128, 0, 0], [], {}, 12000, True)
            assert result.status == "RET"
            cycles.append(K.time_trace(program, result.trace, machine))
        assert cycles[1] < cycles[0], cycles
        print(f"default-machine 128-iteration sum: {cycles[0]} -> {cycles[1]} cycles")
    print(f"{checks} official-interpreter comparisons passed; "
          f"{variants} variants ({rejects} rejected); SSA verification passed")


if __name__ == "__main__":
    main()
