#!/usr/bin/env python3
"""Direct rematerialization checks; no optimizer search/fallback can mask bugs."""
from pathlib import Path
import os
import random
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
KIT = Path(os.environ.get("KIT", ROOT.parent / "official-LLH-26/Compilers/COMP10"))
sys.path.insert(0, str(KIT))
sys.dont_write_bytecode = True
import kirlib as K

DRIVER = r'''
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <iterator>
#include "backend.h"
#include "passes.h"
namespace kopt { bool rematerialize(Func &, const Machine &); }
using namespace kopt;
int main(int argc, char **argv) {
    const bool lower = argc == 5 && std::string(argv[1]) == "lower";
    if (argc != 4 && !lower) return 2;
    std::string text((std::istreambuf_iterator<char>(std::cin)), {}), err;
    Program p; Func f;
    if (!parseProgram(text, p, err) || !buildSSA(p, f, err)) return 3;
    Machine m;
    if (lower) {
        std::ifstream file(argv[2]);
        const std::string cfg((std::istreambuf_iterator<char>(file)), {});
        if (!parseMachine(cfg, m, err)) { std::cerr << err; return 7; }
        instSimplify(f); gvn(f); dce(f); simplifyCFG(f);
        const int before = f.nvals;
        const bool changed = std::atoi(argv[3]) != 0 && rematerialize(f, m);
        err = verifyFunc(f); if (!err.empty()) { std::cerr << err; return 5; }
        std::cerr << "changed=" << changed << " clones=" << f.nvals - before << '\n';
        const int bits = std::atoi(argv[4]);
        BackendOptions opt; opt.preSchedule = (bits & 1) != 0;
        opt.spillToK = (bits & 2) != 0; opt.spreadColors = (bits & 4) != 0;
        opt.pressureSchedule = (bits & 8) != 0;
        std::cout << printProgram(lowerToProgram(f, m, opt));
        return 0;
    }
    m.lat_load = std::atoi(argv[2]); m.fused_addsh = std::atoi(argv[3]);
    const int before = f.nvals, expected = std::atoi(argv[1]);
    if (rematerialize(f, m) != (expected > 0) || f.nvals - before != expected) return 4;
    err = verifyFunc(f); if (!err.empty()) { std::cerr << err; return 5; }
    // A budget-limited invocation can intentionally leave eligible roots.
    if (expected < 64 && rematerialize(f, m)) return 6;
    BackendOptions opt; opt.preSchedule = false;
    std::cout << printProgram(lowerToProgram(f, m, opt));
}
'''


def straight(op="add v2, v0, 7", gap=9, anchor=True):
    lines = ["func remat(v0, v1)", "entry:", "store 9, v1", op,
             "xor v3, v2, v2", "store 10, v3"]
    lines += ["vstore 4, v1"] * gap
    lines += ["add v4, v2, v1", "store 11, v4"]
    if anchor:
        lines += ["vstore 3, v0"]
    return "\n".join(lines + ["ret v1"]) + "\n"


def pressure_batch(lanes):
    """Tag a runtime input batch before/after computing its checksum.

    Every input contributes to the result; there is no padding/dead work.
    v0 remains needed independently of the tag, so rematerializing the tag
    removes one long-lived value without extending its parameter's lifetime.
    """
    lines = ["func pressure_batch(v0)", "entry:",
             "xor v1, v0, 2654435769", "store 10, v1"]
    lines += [f"vload v{10+i}, 1" for i in range(lanes)]
    lines += ["mul v100, v10, v11"]
    lines += [f"add v100, v100, v{10+i}" for i in range(2, lanes)]
    lines += ["shl v110, v100, 5", "xor v100, v100, v110", "store 12, v1",
              "xor v101, v100, v0", "mul v102, v101, 3", "add v103, v102, 19",
              "store 11, v103", "ret v103"]
    return "\n".join(lines) + "\n"


def pressure_proof(binary, edges, rng):
    checks = 0
    # Include pressure scheduling, spill and spreading alternatives.
    # No search/fallback is involved. Compare the best before/after alternatives.
    modes = (0, 1, 2, 3, 5, 7, 9, 11, 13, 15)
    required_wins = {(3, "few_registers"), (7, "slow_memory"),
                     (8, "slow_memory")}
    # Pressure scheduling beats rematerialization on the 8-lane/few-register
    # case; only require the independently measured remaining wins.
    wins = set()
    for lanes in (3, 7, 8):
        text = pressure_batch(lanes)
        original = K.compile_program(K.parse_program(text))
        inputs = [([123], {1: list(range(7, 7 + lanes))})]
        inputs += [([p], {1: [q] * lanes}) for p in edges for q in edges]
        inputs += [([rng.getrandbits(32)], {1: [rng.getrandbits(32) for _ in range(lanes)]})
                   for _ in range(64)]
        # Preserve the first observable store and exact vload underflow trap.
        inputs += [([123], {1: list(range(n))}) for n in (0, lanes - 1)]
        oracle = [K.execute(original, args, [], vin, 20000) for args, vin in inputs]
        for machine in ("few_registers", "default", "slow_memory"):
            cfg = KIT / "machines" / f"machine_{machine}.cfg"
            mc = K.load_machine(str(cfg))
            timings = [[], []]
            for remat in (0, 1):
                for bits in modes:
                    out = subprocess.run([str(binary), "lower", str(cfg), str(remat), str(bits)],
                                         input=text, capture_output=True, text=True, check=True)
                    assert ("changed=1 clones=2" if remat else "changed=0 clones=0") in out.stderr
                    program = K.parse_program(out.stdout)
                    K.check_machine_features(program, mc)
                    cp = K.compile_program(program)
                    for i, ((args, vin), expected) in enumerate(zip(inputs, oracle)):
                        actual = K.execute(cp, args, [], vin, 20000, want_trace=i == 0)
                        diff = K.first_difference(expected, actual)
                        assert not diff, ("pressure", lanes, machine, remat, bits, i, diff)
                        if i == 0:
                            timings[remat].append(K.time_trace(cp, actual.trace, mc))
                        checks += 1
            before, after = min(timings[0]), min(timings[1])
            if after < before:
                wins.add((lanes, machine))
            print(f"PRESSURE lanes={lanes} {machine}: best {before} -> {after}; "
                  f"modes={modes} before={timings[0]} after={timings[1]}")
    assert required_wins <= wins, ("missing measured wins", required_wins - wins)
    return checks


def main():
    fixtures = [("separated/repeated", straight(), 2, 4, 1),
                ("nearby", straight(gap=0), 0, 4, 1),
                ("leaf-lifetime", straight(anchor=False), 0, 4, 1),
                ("no-load-saving", straight(), 0, 1, 1),
                ("trap", straight("div v2, v0, v1"), 0, 4, 1),
                ("shift", straight("shl v2, v0, v1"), 2, 4, 1),
                ("addsh", straight("addsh v2, v0, v1, 3"), 2, 4, 1),
                ("unsupported-addsh", straight("addsh v2, v0, v1, 3"), 0, 4, 0),
                ("not-a-leaf", straight("shl v8, v0, 3\nadd v2, v8, 7"), 0, 4, 1)]
    branch = """func branched(v0, v1)
entry:
  add v2, v0, 7
  br v1, left, right
left:
  store 10, v2
  vstore 3, v0
  ret v1
right:
  store 11, v2
  vstore 3, v0
  ret v1
"""
    fixtures.append(("branches", branch, 2, 4, 1))
    phi = branch.replace("ret v1", "mov v9, v2\n  jmp done", 1)
    phi = phi.replace("ret v1", "mov v9, v1\n  jmp done", 1)
    fixtures.append(("phi-user", phi + "done:\n  ret v9\n", 0, 4, 1))
    loop = ("func looped(v0, v1)\nentry:\nadd v2, v0, 7\nconst v20, 3\njmp body\nbody:\n"
            "store 10, v2\n" + "vstore 4, v1\n" * 9 +
            "store 11, v2\nvstore 3, v0\nsub v20, v20, 1\nbr v20, body, done\ndone:\nret v1\n")
    fixtures.append(("loop", loop, 2, 4, 1))
    budget = (["func budget(v0, v1)", "entry:"] +
              [f"add v{v}, v0, {v}" for v in range(2, 42)] +
              [f"store 10, v{v}" for v in range(2, 42)] +
              [f"store 11, v{v}" for v in range(2, 42)] + ["vstore 3, v0", "ret v1"])
    fixtures.append(("budget", "\n".join(budget) + "\n", 64, 4, 1))
    many = ("func many(v0, v1)\nentry:\nadd v2, v0, 7\n" +
            "store 10, v2\n" * 10 + "vstore 3, v0\nret v1\n")
    fixtures.append(("use-limit", many, 0, 4, 1))

    edges = [0, 1, 7, 31, 32, 0x7fffffff, 0x80000000, 0xffffffff]
    rng = random.Random(180818)
    inputs = [(a, b) for a in edges for b in edges]
    inputs += [(rng.getrandbits(32), rng.getrandbits(32)) for _ in range(64)]
    checks = 0
    with tempfile.TemporaryDirectory() as temp:
        td = Path(temp)
        driver = td / "driver.cpp"
        driver.write_text(DRIVER)
        binary = td / "driver"
        sources = sorted(str(p) for p in (ROOT / "src").glob("*.cpp")
                         if p.name not in ("main.cpp", "optimizer.cpp"))
        subprocess.run([os.environ.get("CXX", "c++"), "-std=c++17", "-O0", "-Wall", "-Wextra",
                        "-Werror", "-pedantic", "-I" + str(ROOT / "src"), str(driver),
                        *sources, "-o", str(binary)], check=True)
        for name, text, expected, load, fused in fixtures:
            out = subprocess.run([str(binary), str(expected), str(load), str(fused)],
                                 input=text, capture_output=True, text=True)
            assert out.returncode == 0, (name, out.returncode, out.stderr)
            a, b = [K.compile_program(K.parse_program(t)) for t in (text, out.stdout)]
            for args in inputs:
                x = K.execute(a, list(args), [], {}, 20000)
                y = K.execute(b, list(args), [], {}, 20000)
                diff = K.first_difference(x, y)
                assert not diff, (name, args, diff, out.stdout)
                checks += 1
            print("PASS", name)
        checks += pressure_proof(binary, edges, rng)
    print(f"{checks} official-interpreter comparisons; SSA, clone counts, non-budget idempotence checked")


if __name__ == "__main__":
    main()
