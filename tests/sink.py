#!/usr/bin/env python3
"""Direct sinking semantics and official timing; no optimizer fallback."""
from pathlib import Path
import json
import os
import random
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
KIT = Path(os.environ.get("KIT", ROOT.parent / "official-LLH-26/Compilers/COMP10"))
sys.dont_write_bytecode = True
sys.path.insert(0, str(KIT))
import kirlib as K

DRIVER = r'''
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <iterator>
#include "backend.h"
#include "cfg.h"
#include "passes.h"
namespace kopt { bool sinkInstructions(Func &); }
using namespace kopt;
int main(int argc, char **argv) {
    if (argc != 5) return 2;
    const std::string text((std::istreambuf_iterator<char>(std::cin)), {});
    std::ifstream file(argv[1]);
    const std::string cfg((std::istreambuf_iterator<char>(file)), {});
    std::string err; Machine m; Program p; Func f;
    if (!parseMachine(cfg, m, err) || !parseProgram(text, p, err) || !buildSSA(p, f, err)) {
        std::cerr << err; return 3;
    }
    const int nv = f.nvals;
    const bool changed = std::atoi(argv[2]) != 0 && sinkInstructions(f);
    if (f.nvals != nv) return 4;  // Sinking must not clone anything.
    err = verifyFunc(f); if (!err.empty()) { std::cerr << err; return 5; }
    if (std::atoi(argv[2]) != 0 && sinkInstructions(f)) return 6;  // Stable in one sweep.
    std::cerr << "changed=" << changed << '\n';
    if (std::string(argv[4]) == "ssa") { std::cout << dumpFunc(f); return 0; }
    const int bits = std::atoi(argv[3]);
    BackendOptions opt;
    opt.preSchedule = (bits & 1) != 0; opt.spillToK = (bits & 2) != 0;
    opt.spreadColors = (bits & 4) != 0; opt.pressureSchedule = (bits & 8) != 0;
    std::cout << printProgram(lowerToProgram(f, m, opt));
}
'''


def lower(binary, text, machine, apply, bits=0, fmt="kir"):
    result = subprocess.run([str(binary), str(machine), str(int(apply)), str(bits), fmt],
                            input=text, text=True, capture_output=True, check=True)
    return result.stdout, "changed=1" in result.stderr


def fixtures():
    return {
        "same-block": ("""func same(v0, v1)
entry:
  mul v2, v0, 7
  vstore 3, v1
  store 10, v1
  add v3, v2, v1
  ret v3
""", True),
        "cold-branch": ("""func cold(v0, v1)
entry:
  mul v2, v0, 7
  br v1, cold, hot
cold:
  store 10, v2
  ret v0
hot:
  ret v0
""", True),
        "multiuser-pinned": ("""func shared(v0, v1)
entry:
  mul v2, v0, 7
  store 10, v2
  vstore 3, v1
  store 11, v2
  ret v0
""", False),
        "repeated-operands": ("""func repeated(v0, v1)
entry:
  mul v2, v0, 7
  vstore 3, v1
  xor v3, v2, v2
  ret v3
""", True),
        "phi-pinned": ("""func phiuser(v0, v1)
entry:
  mul v2, v0, 7
  br v1, left, right
left:
  vstore 3, v1
  jmp join
right:
  mov v2, v0
  jmp join
join:
  ret v2
""", False),
        "join": ("""func joined(v0, v1)
entry:
  mul v2, v0, 7
  br v1, left, right
left:
  vstore 3, v0
  jmp join
right:
  store 10, v1
  jmp join
join:
  xor v3, v2, v1
  ret v3
""", True),
        "volatile-operand": ("""func vol(v0, v1)
entry:
  vload v2, 1
  mul v3, v2, v0
  vstore 3, v1
  store 10, v1
  ret v3
""", True),
        "load-pinned": ("""func memory(v0, v1)
entry:
  load v2, v0
  store 10, v1
  vstore 3, v1
  ret v2
""", False),
        "division-pinned": ("""func division(v0, v1)
entry:
  div v2, v0, v1
  store 10, v0
  vstore 3, v1
  ret v2
""", False),
        "cross-trap": ("""func trapping(v0, v1)
entry:
  mul v2, v0, 7
  store 10, v1
  div v3, v1, v0
  vstore 3, v3
  ret v2
""", True),
        "zero-initial": ("""func zero(v0, v1)
entry:
  add v2, v0, v999
  vstore 3, v1
  xor v3, v2, v1
  ret v3
""", True),
        "preheader-pinned": ("""func preheader(v0, v1)
entry:
  mul v2, v0, 7
  and v3, v1, 7
  jmp head
head:
  store 10, v2
  sub v3, v3, 1
  and v3, v3, 7
  br v3, head, done
done:
  ret v0
""", False),
        "loop-local": ("""func local(v0, v1)
entry:
  and v3, v1, 7
  jmp head
head:
  mul v2, v0, 7
  vstore 3, v0
  store 10, v2
  sub v3, v3, 1
  and v3, v3, 7
  br v3, head, done
done:
  ret v0
""", True),
        "loop-exit-phi-pinned": ("""func exiting(v0, v1)
entry:
  and v3, v1, 7
  jmp head
head:
  mul v2, v0, 7
  sub v3, v3, 1
  and v3, v3, 7
  br v3, head, done
done:
  ret v2
""", False),
        "adjacent": ("func adjacent(v0, v1)\nentry:\nmul v2, v0, 7\nret v2\n", False),
        "dominated-operands": ("""func operanddefs(v0, v1)
entry:
  br v1, left, right
left:
  vload v2, 1
  mul v3, v2, v0
  jmp deeper
deeper:
  vstore 3, v1
  ret v3
right:
  ret v0
""", True),
        "phi-operand": ("""func phioperand(v0, v1)
entry:
  br v1, left, right
left:
  add v2, v0, 1
  jmp join
right:
  sub v2, v0, 1
  jmp join
join:
  mul v3, v2, v0
  jmp later
later:
  vstore 3, v1
  ret v3
""", True),
        "nested-loop-pinned": ("""func nested(v0, v1)
entry:
  const v3, 2
  jmp outer
outer:
  mul v2, v0, 7
  const v4, 2
  jmp inner
inner:
  store 10, v2
  sub v4, v4, 1
  br v4, inner, latch
latch:
  sub v3, v3, 1
  br v3, outer, done
done:
  ret v1
""", False),
        "dependency-chain": ("""func chain(v0, v1)
entry:
  mul v2, v0, 7
  vstore 3, v1
  add v3, v2, v1
  vstore 3, v0
  xor v4, v3, v0
  ret v4
""", True),
        "irreducible-pinned": ("""func irreducible(v0, v1)
entry:
  mul v2, v0, 7
  const v3, 3
  br v1, a, b
a:
  sub v3, v3, 1
  br v3, b, done
b:
  store 10, v2
  sub v3, v3, 1
  br v3, a, done
done:
  ret v0
""", False),
    }


def pressure_case(lanes):
    lines = ["func late_tag(v0, v1)", "entry:", "xor v2, v0, 2654435769"]
    lines += [f"vload v{10+i}, 1" for i in range(lanes)]
    lines += ["mul v100, v10, v11"]
    lines += [f"add v100, v100, v{10+i}" for i in range(2, lanes)]
    lines += ["shl v110, v100, 5", "xor v100, v100, v110", "store 12, v2",
              "xor v101, v100, v0", "mul v102, v101, 3", "add v103, v102, 19",
              "store 11, v103", "ret v103"]
    return "\n".join(lines) + "\n"


def cold_case():
    lines = ["func cold_outputs(v0, v1)", "entry:"]
    lines += [f"mul v{10+i}, v0, {3+i*2}" for i in range(8)]
    lines += ["br v1, cold, hot", "cold:"]
    lines += [f"store {100+i}, v{10+i}" for i in range(8)]
    lines += ["ret v0", "hot:", "ret v0"]
    return "\n".join(lines) + "\n"


def timing_proof(binary, inputs, artifacts):
    modes = (0, 1, 2, 3, 5, 7, 9, 11)
    cases = [("pressure3", pressure_case(3), 3),
             ("pressure8", pressure_case(8), 8), ("cold8", cold_case(), 0)]
    rows, wins, checks = [], set(), 0
    for name, text, lanes in cases:
        original = K.compile_program(K.parse_program(text))
        if artifacts:
            (artifacts / (name + ".kir")).write_text(text)
        streams = ({1: list(range(7, 7 + lanes))}, {}, {1: [0xffffffff] * max(0, lanes - 1)})
        references = [(args, vin, K.execute(original, list(args), [], vin, 20000))
                      for args in inputs for vin in streams]
        for machine in ("few_registers", "default", "slow_memory"):
            cfg = KIT / "machines" / f"machine_{machine}.cfg"
            mc = K.load_machine(str(cfg))
            timings = [[], []]
            for apply in (0, 1):
                for bits in modes:
                    output, changed = lower(binary, text, cfg, apply, bits)
                    assert changed == bool(apply), (name, "did not sink")
                    program = K.parse_program(output); K.check_machine_features(program, mc)
                    compiled = K.compile_program(program)
                    for args, vin, expected in references:
                        actual = K.execute(compiled, list(args), [], vin, 20000)
                        diff = K.first_difference(expected, actual)
                        assert not diff, (name, machine, bits, apply, args, vin, diff)
                        checks += 1
                    pair = []
                    for condition in (0, 1):
                        result = K.execute(compiled, [123, condition], [], streams[0], 20000, want_trace=True)
                        pair.append(K.time_trace(compiled, result.trace, mc))
                    timings[apply].append(pair)
                    if artifacts:
                        (artifacts / f"{name}-{machine}-{apply}-{bits}.kir").write_text(output)
            for condition in (0, 1):
                before = [t[condition] for t in timings[0]]
                after = [t[condition] for t in timings[1]]
                if min(after) < min(before): wins.add((name, machine, condition))
                row = dict(case=name, machine=machine, condition=condition, modes=modes,
                           before=before, after=after, best_before=min(before), best_after=min(after))
                rows.append(row)
                print(f"CYCLES {name} {machine} cond={condition}: best {min(before)} -> {min(after)}; "
                      f"before={before} after={after}")
    required = {("pressure3", "few_registers", 0), ("pressure8", "slow_memory", 0),
                ("cold8", "few_registers", 0), ("cold8", "few_registers", 1),
                ("cold8", "default", 0), ("cold8", "default", 1)}
    assert required <= wins, ("missing measured wins", required - wins)
    if artifacts:
        (artifacts / "timing.json").write_text(json.dumps(rows, indent=2) + "\n")
    return checks


def main():
    edges = [0, 1, 7, 31, 32, 4095, 4096, 0x7fffffff, 0x80000000, 0xffffffff]
    rng = random.Random(608818)
    inputs = [(a, b) for a in edges for b in edges]
    inputs += [(rng.getrandbits(32), rng.getrandbits(32)) for _ in range(80)]
    checks = 0
    with tempfile.TemporaryDirectory() as tmp:
        td = Path(tmp); driver = td / "driver.cpp"; binary = td / "driver"
        driver.write_text(DRIVER)
        sources = sorted(str(p) for p in (ROOT / "src").glob("*.cpp")
                         if p.name not in ("main.cpp", "optimizer.cpp"))
        subprocess.run([os.environ.get("CXX", "c++"), "-std=c++17", "-O1", "-Wall", "-Wextra",
                        "-Werror", "-pedantic", "-I" + str(ROOT / "src"), str(driver),
                        *sources, "-o", str(binary)], check=True)
        cfg = KIT / "machines/machine_few_registers.cfg"
        # An iterative forest walk must handle deep use chains without C++
        # recursion or repeatedly erasing/inserting into instruction vectors.
        chain = ["func deep(v0, v1)", "entry:", "add v2, v0, 7"]
        for v in range(3, 12003):
            chain += ["vstore 3, v1", f"add v{v}, v{v-1}, v0"]
        chain += ["ret v12002"]
        _, changed = lower(binary, "\n".join(chain) + "\n", cfg, True, fmt="ssa")
        assert changed, "deep-chain stress did not move"
        capped = ["func capped(v0, v1)"]
        for b in range(257):
            capped += [f"b{b}:", f"jmp b{b+1}" if b < 256 else "ret v0"]
        _, changed = lower(binary, "\n".join(capped) + "\n", cfg, True, fmt="ssa")
        assert not changed, "block cap ignored"
        print("PASS deep-chain and block-cap")
        for name, (text, expected_change) in fixtures().items():
            original = K.compile_program(K.parse_program(text))
            for bits in (0, 1, 2, 3, 9, 11):
                output, changed = lower(binary, text, cfg, True, bits)
                assert changed == expected_change, (name, bits, changed)
                again, _ = lower(binary, text, cfg, True, bits)
                assert output == again, (name, "nondeterministic")
                optimized = K.compile_program(K.parse_program(output))
                for args in inputs:
                    for vin in ({}, {1: [13]}):
                        x = K.execute(original, list(args), [], vin, 20000)
                        y = K.execute(optimized, list(args), [], vin, 20000)
                        diff = K.first_difference(x, y)
                        assert not diff, (name, bits, args, vin, diff, output)
                        checks += 1
            print("PASS", name)
        artifact_dir = Path(sys.argv[1]).resolve() if len(sys.argv) == 2 else None
        if artifact_dir: artifact_dir.mkdir(parents=True, exist_ok=True)
        checks += timing_proof(binary, inputs, artifact_dir)
    print(f"{checks} official-interpreter comparisons; SSA verification and determinism passed")


if __name__ == "__main__":
    main()
