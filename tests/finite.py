#!/usr/bin/env python3
"""Finite-domain proof gates and direct official semantics/timing tests."""
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
#include <fstream>
#include <iostream>
#include <iterator>
#include "passes.h"
namespace kopt { bool finiteFunction(const Program &, const Machine &, Program &); }
using namespace kopt;
bool poisonRanges() {
    Program p; Func f; std::string err;
    if (!parseProgram("func seed(v0)\nentry:\nand v1,v0,7\nret v1\n", p, err) ||
        !buildSSA(p, f, err)) return false;
    computeVRP(f);
    return true;
}
int main(int argc, char **argv) {
    if (argc != 2) return 2;
    const std::string text((std::istreambuf_iterator<char>(std::cin)), {});
    std::ifstream file(argv[1]);
    const std::string cfg((std::istreambuf_iterator<char>(file)), {});
    std::string err; Program p; Machine m;
    if (!parseProgram(text, p, err) || !parseMachine(cfg, m, err)) { std::cerr << err; return 3; }
    // Guard against range facts leaking across functions that reuse SSA IDs:
    // seed value 1 is [0,7], but fresh value 1 is an unbounded second parameter.
    if (!poisonRanges()) return 11;
    Program probe; Func fresh;
    if (!parseProgram("func probe(v0,v1)\nentry:\nlt v3,v1,4096\nbr v3,load,done\n"
                      "load:\nload v2,v1\nret v2\ndone:\nret 0\n", probe, err) ||
        !buildSSA(probe, fresh, err)) return 12;
    const auto facts = memoryFacts(fresh);
    int loads = 0;
    for (const BlockMemInfo &b : facts) for (bool safe : b.safe) { loads++; if (safe) return 13; }
    if (loads != 1) return 13;
    if (!poisonRanges()) return 11;
    Program out = p;
    const bool changed = finiteFunction(p, m, out);
    if (!changed && printProgram(out) != printProgram(p)) return 4;
    if (out.name != p.name || out.params != p.params) return 5;
    if (changed) {
        for (const Block &b : out.blocks) for (const Instr &x : b.ins)
            if (isMemOp(x.op) || x.op == OP_TRAP) return 6;
        Func f; if (!buildSSA(out, f, err)) return 7;
        err = verifyFunc(f); if (!err.empty()) { std::cerr << err; return 8; }
        Program again;
        if (!poisonRanges()) return 11;
        if (!finiteFunction(p, m, again) || printProgram(again) != printProgram(out)) return 9;
        Program alias = p;
        if (!poisonRanges()) return 11;
        if (!finiteFunction(alias, m, alias) || printProgram(alias) != printProgram(out)) return 10;
    }
    std::cerr << "changed=" << changed << '\n';
    std::cout << printProgram(out);
}
'''


def recurrence(mask=7):
    return f"""func recurrence(v0, v1)
entry:
  and v2, v0, {mask}
  const v3, 97
  const v4, 11
  jmp body
body:
  mul v3, v3, 1664525
  add v3, v3, v2
  xor v3, v3, v4
  shl v5, v3, 5
  xor v3, v3, v5
  sub v4, v4, 1
  br v4, body, done
done:
  ret v3
"""


def fixtures():
    result = {
        "recurrence3": (recurrence(), True),
        "recurrence6": (recurrence(63), True),
        "sign31": ("""func signedbit(v999999, v0)
entry:
  and v2, v999999, 2147483648
  lt v3, v2, 0
  select v4, v3, 4294967295, 2147483648
  ret v4
""", True),
        "two-params-six-bits": ("""func combined(v0, v999999, v1)
entry:
  and v2, v0, 2147483651
  and v3, 44, v999999
  mul v4, v2, 13
  xor v5, v3, v4
  ret v5
""", True),
        "duplicate-masks": ("""func duplicates(v0)
entry:
  and v1, v0, 3
  and v2, 3, v0
  and v3, v0, 4
  mul v4, v1, 7
  xor v5, v4, v2
  add v6, v5, v3
  ret v6
""", True),
        "zero-initial": ("""func zeros(v0, v1)
entry:
  and v2, v0, 7
  add v3, v2, v999999
  ret v3
""", True),
        "zero-params": ("func zeroargs()\nentry:\nadd v2, v999999, 9\nret v2\n", True),
        "unused-params": ("func unused(v1,v0,v999999)\nentry:\nret 4294967295\n", True),
        "overwritten-param": ("func overwritten(v0)\nentry:\nconst v0, 17\nret v0\n", True),
        "mask-union-too-wide": ("func wide(v0)\nentry:\nand v1,v0,15\nand v2,v0,112\nadd v3,v1,v2\nret v3\n", False),
        "two-params-too-wide": ("func widepair(v0,v1)\nentry:\nand v2,v0,15\nand v3,v1,15\nxor v4,v2,v3\nret v4\n", False),
        "raw-ret": ("func raw(v0)\nentry:\nret v0\n", False),
        "raw-branch": ("func rawbranch(v0)\nentry:\nbr v0,a,b\na:\nret 1\nb:\nret 2\n", False),
        "raw-arithmetic": ("func rawmath(v0)\nentry:\nadd v1,v0,7\nret v1\n", False),
        "raw-phi": ("""func rawphi(v0,v1)
entry:
  and v2,v1,1
  br v2,a,b
a:
  mov v3,v0
  jmp join
b:
  const v3,3
  jmp join
join:
  ret v3
""", False),
        "masked-trap": ("func trapcase(v0)\nentry:\nand v1,v0,3\ndiv v2,17,v1\nret v2\n", False),
        "trap-last-projection": ("""func late_trap(v0)
entry:
  and v1,v0,63
  eq v2,v1,63
  br v2,bad,good
bad:
  div v3,1,0
  ret v3
good:
  ret v1
""", False),
        "trap-outside-mask": ("func rawdiv(v0)\nentry:\nand v1,v0,3\nshr v2,v0,2\ndiv v3,v1,v2\nret v3\n", False),
        "explicit-trap": ("func explicit(v0)\nentry:\ntrap 7\n", False),
        "unreachable-trap": ("func deadtrap(v0)\nentry:\nret 3\ndead:\ntrap 7\n", False),
        "infinite": ("func infinite(v0)\nentry:\nand v1,v0,3\njmp loop\nloop:\njmp loop\n", False),
        "infinite-last-projection": ("""func partial(v0)
entry:
  and v1,v0,63
  eq v2,v1,63
  br v2,loop,done
loop:
  jmp loop
done:
  ret v1
""", False),
        "all-six-bits-reduce": ("""func reduced(v0)
entry:
  and v1,v0,63
  lt v2,v1,32
  select v3,v2,7,9
  ret v3
""", True),
        "shared-parity-subtables": ("""func parity(v0)
entry:
  and v1,v0,63
  shr v2,v1,1
  xor v1,v1,v2
  shr v2,v1,2
  xor v1,v1,v2
  shr v2,v1,4
  xor v1,v1,v2
  and v1,v1,1
  ret v1
""", True),
        "zero-mask": ("func zeromask(v0)\nentry:\nand v1,v0,0\nret v1\n", True),
        "safe-division": ("func safediv(v0)\nentry:\nand v1,v0,7\nadd v2,v1,1\ndiv v3,2147483648,v2\nret v3\n", True),
    }
    for name, operation in (("load", "load v2, 0"), ("store", "store 0, 7"),
                            ("scratch", "store 4095, 7"), ("vload", "vload v2, 0"),
                            ("vstore", "vstore 0, 7")):
        result[name] = (f"func effects(v0)\nentry:\n{operation}\nret 7\n", False)
        result["unreachable-" + name] = (f"func deadeffects(v0)\nentry:\nret 7\ndead:\n{operation}\nret 7\n", False)
    for name, count, mask, accepted in (("per-case-at-limit", 9998, 0, True),
                                        ("per-case-over", 9999, 0, False),
                                        ("total-over", 8000, 63, False)):
        text = f"""func budget(v0)
entry:
  and v1,v0,{mask}
  const v2,{count}
  jmp loop
loop:
  sub v2,v2,1
  br v2,loop,done
done:
  ret v1
"""
        result[name] = (text, accepted)
    result["instruction-cap"] = ("func capped(v0)\nentry:\n" + "const v1,7\n" * 8000 + "ret v1\n", False)
    blocks = ["func blockcap(v0)"]
    for i in range(257): blocks += [f"b{i}:", f"jmp b{i+1}" if i < 256 else "ret 7"]
    result["block-cap"] = ("\n".join(blocks) + "\n", False)
    return result


def invoke(binary, text, cfg):
    run = subprocess.run([str(binary), str(cfg)], input=text, text=True,
                         capture_output=True, check=True, timeout=20)
    return run.stdout, "changed=1" in run.stderr


def main():
    rng = random.Random(608816)
    edges = [0, 1, 7, 31, 63, 64, 0x7fffffff, 0x80000000, 0xffffffff]
    checks = 0
    artifact = Path(sys.argv[1]).resolve() if len(sys.argv) == 2 else None
    if artifact: artifact.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory() as tmp:
        td = Path(tmp); driver = td / "driver.cpp"; binary = td / "driver"
        driver.write_text(DRIVER)
        sources = sorted(str(p) for p in (ROOT / "src").glob("*.cpp")
                         if p.name not in ("main.cpp", "optimizer.cpp"))
        subprocess.run([os.environ.get("CXX", "c++"), "-std=c++17", "-O1", "-Wall", "-Wextra",
                        "-Werror", "-pedantic", "-I" + str(ROOT / "src"), str(driver),
                        *sources, "-o", str(binary)], check=True)
        machines = [KIT / "machines" / f"machine_{m}.cfg" for m in
                    ("default", "few_registers", "slow_memory", "no_fused", "wide_fast")]
        timing = []
        for name, (text, expected) in fixtures().items():
            output, changed = invoke(binary, text, machines[0])
            assert changed == expected, (name, changed)
            print("PASS", name, "accepted" if changed else "rejected", flush=True)
            if not changed: continue
            p = K.parse_program(text); original = K.compile_program(p)
            result = K.parse_program(output); optimized = K.compile_program(result)
            if name in ("sign31", "all-six-bits-reduce"):
                assert len(result.instrs) == 3, (name, "two-leaf reduction", output)
            if name == "shared-parity-subtables":
                assert len(result.instrs) <= 24, (name, "subtables not shared", output)
            if name in ("unused-params", "overwritten-param", "zero-params"):
                assert len(result.instrs) == 1, (name, output)
            # 256 full-bit patterns + random values + edge cases. These vary
            # unselected high bits, so testing is independent of the table keys.
            args = [[((i * (2*j+1)) * 0x01010101) & 0xffffffff for j in range(len(p.params))]
                    for i in range(256)]
            args += [[rng.getrandbits(32) for _ in p.params] for _ in range(128)]
            args += [[e for _ in p.params] for e in edges]
            # Also cover all 64 projected states of the two-parameter fixture.
            if name == "two-params-six-bits":
                args += [[(i & 3) | ((i & 4) << 29), ((i >> 3) & 1) * 4 |
                          ((i >> 4) & 1) * 8 | ((i >> 5) & 1) * 32, 0xffffffff] for i in range(64)]
            for inp in args:
                segments = [(0, [rng.getrandbits(32), 17]), (4095, [13])]
                vin = {0: [rng.getrandbits(32)]}
                a = K.execute(original, inp, segments, vin, 20001)
                b = K.execute(optimized, inp, segments, vin, 20001)
                diff = K.first_difference(a, b)
                assert not diff, (name, inp, diff, output)
                checks += 1
            for cfg in machines:
                other, accepted = invoke(binary, text, cfg)
                assert accepted and other == output, (name, "machine instability")
                mc = K.load_machine(str(cfg)); K.check_machine_features(result, mc)
                if name.startswith("recurrence"):
                    before = after = 0
                    for i in range(64 if name.endswith("6") else 8):
                        inp = [i, 0xffffffff]
                        a = K.execute(original, inp, [], {}, 20001, want_trace=True)
                        b = K.execute(optimized, inp, [], {}, 20001, want_trace=True)
                        before += K.time_trace(original, a.trace, mc)
                        after += K.time_trace(optimized, b.trace, mc)
                    assert after < before, (name, cfg.name, before, after)
                    row = dict(case=name, machine=cfg.stem, before=before, after=after)
                    timing.append(row); print("CYCLES", row, flush=True)
            if artifact:
                (artifact / (name + "-before.kir")).write_text(text)
                (artifact / (name + "-after.kir")).write_text(output)
        if artifact: (artifact / "timing.json").write_text(json.dumps(timing, indent=2) + "\n")
    print(f"{checks} official-interpreter comparisons; proof gates, SSA, determinism, aliasing passed")


if __name__ == "__main__":
    main()
