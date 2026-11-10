#!/usr/bin/env python3
"""Direct BDD/packed equivalence and official timing, independent source tables."""
from pathlib import Path
import json
import os
import random
import runpy
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
namespace kopt { bool finitePackedFunction(const Program &, const Machine &, Program &); }
using namespace kopt;
int main(int argc, char **argv) {
    if (argc != 3) return 2;
    std::string text((std::istreambuf_iterator<char>(std::cin)), {}), err;
    std::ifstream file(argv[1]); const std::string cfg((std::istreambuf_iterator<char>(file)), {});
    Program p; Machine m;
    if (!parseProgram(text, p, err) || !parseMachine(cfg, m, err)) { std::cerr << err; return 3; }
    const bool packed = std::string(argv[2]) == "packed";
    auto transform = [&](const Program &in, Program &out) {
        return packed ? finitePackedFunction(in, m, out) : finiteFunction(in, m, out);
    };
    Program out = p;
    const bool accepted = transform(p, out);
    if (!accepted && printProgram(out) != printProgram(p)) return 4;
    if (out.name != p.name || out.params != p.params) return 5;
    if (accepted) {
        for (const Block &b : out.blocks) for (const Instr &x : b.ins) {
            if (isMemOp(x.op) || x.op == OP_TRAP) return 6;
            if (hasDest(x.op)) for (uint32_t param : p.params) if (param == x.dst) return 7;
        }
        if (packed && (out.instrCount() > 96 || out.blocks.size() > 32)) return 8;
        Func f;
        if (!buildSSA(out, f, err)) return 9;
        err = verifyFunc(f); if (!err.empty()) { std::cerr << err; return 10; }
        Program again;
        if (!transform(p, again) || printProgram(again) != printProgram(out)) return 11;
        Program alias = p;
        if (!transform(alias, alias) || printProgram(alias) != printProgram(out)) return 12;
    }
    std::cerr << "accepted=" << accepted << '\n';
    std::cout << printProgram(out);
}
'''


def invoke(binary, text, cfg, mode):
    result = subprocess.run([str(binary), str(cfg), mode], input=text, text=True,
                            capture_output=True, check=True, timeout=20)
    return result.stdout, "accepted=1" in result.stderr


def table_source(values, positions, params=(999999, 0)):
    """Write an ordinary source decision tree, never a stored optimizer answer.

    positions gives (parameter index, source bit) in the evaluator's key order.
    Each raw parameter is masked first, including duplicate/complementary uses.
    """
    lines = ["func source_table(" + ",".join(f"v{p}" for p in params) + ")", "entry:"]
    for j, (p, bit) in enumerate(positions):
        lines += [f"and v{100+j}, v{params[p]}, {1 << bit}"]
    if not positions: return "\n".join(lines + [f"ret {values[0]}"]) + "\n"
    lines += ["jmp n0_0"]

    def walk(level, key):
        lines.append(f"n{level}_{key}:")
        if level == len(positions):
            lines.append(f"ret {values[key]}")
        else:
            high = key | (1 << level)
            lines.append(f"br v{100+level}, n{level+1}_{high}, n{level+1}_{key}")
            walk(level + 1, key); walk(level + 1, high)
    walk(0, 0)
    return "\n".join(lines) + "\n"


def recurrence(field_mask):
    return f"""func mixer(v0, v1)
entry:
  and v2, v0, 63
  const v3, 97
  const v4, 11
  jmp loop
loop:
  mul v3, v3, 1664525
  add v3, v3, v2
  xor v3, v3, v4
  shl v5, v3, 5
  xor v3, v3, v5
  sub v4, v4, 1
  br v4, loop, done
done:
  and v3, v3, {field_mask}
  ret v3
"""


def fixtures():
    rng = random.Random(725608)
    cases = {}
    dense = [(0, i) for i in range(6)]
    for width in (1, 2, 4, 8, 16):
        values = [rng.randrange(1 << width) for _ in range(64)]
        values[0], values[-1] = 0, (1 << width) - 1
        accepted = width <= 8  # 16-bit * 64 entries would need 32 words.
        cases[f"dense{width}"] = (table_source(values, dense), accepted, dense)
    for width in (16, 32):
        positions = [(0, i) for i in range(4)]
        values = [rng.getrandbits(width) for _ in range(16)]
        values[0], values[-1] = 0, (1 << width) - 1
        cases[f"full{width}"] = (table_source(values, positions), True, positions)
    sparse = [(0, i) for i in (1, 7, 29, 31)]
    multi = [(0, i) for i in (0, 9, 31)] + [(1, i) for i in (1, 12, 31)]
    for name, positions in (("sparse-sign31", sparse), ("two-params-sign31", multi)):
        values = [rng.randrange(256) for _ in range(1 << len(positions))]
        values[0], values[-1] = 0, 255
        cases[name] = (table_source(values, positions), True, positions)
    for name, base in (("unsigned-base", 0xfffffff0), ("signed-base", 0x80000000)):
        values = [base + rng.randrange(16) for _ in range(64)]
        values[0], values[-1] = base, base + 15
        cases[name] = (table_source(values, dense), True, dense)
    positions = [(0, i) for i in range(3)]
    wrap = [((0xfffffffd + i) & 0xffffffff) for i in range(8)]
    cases["base-wrap-full32"] = (table_source(wrap, positions), True, positions)
    cases["constant"] = (table_source([0xffffffff] * 64, dense), True, dense)
    cases["repeated-packed-words"] = (table_source([i % 4 for i in range(64)], dense), True, dense)
    cases["full32-too-many"] = (table_source([0xffffffff if i & 1 else i for i in range(64)], dense), False, dense)
    for mask in (1, 3, 15, 255):
        cases[f"recurrence{mask}"] = (recurrence(mask), True, dense)
    return cases


def main():
    rng = random.Random(750608)
    artifact = Path(sys.argv[1]).resolve() if len(sys.argv) == 2 else None
    if artifact: artifact.mkdir(parents=True, exist_ok=True)
    checks, timings = 0, []
    old = runpy.run_path(str(ROOT / "tests/finite.py"))
    with tempfile.TemporaryDirectory() as tmp:
        td = Path(tmp); driver = td / "driver.cpp"; binary = td / "driver"
        driver.write_text(DRIVER)
        sources = sorted(str(p) for p in (ROOT / "src").glob("*.cpp") if p.name not in ("main.cpp", "optimizer.cpp"))
        subprocess.run([os.environ.get("CXX", "c++"), "-std=c++17", "-O1", "-Wall", "-Wextra",
                        "-Werror", "-pedantic", "-I" + str(ROOT / "src"), str(driver), *sources,
                        "-o", str(binary)], check=True)
        machines = [KIT / "machines" / f"machine_{m}.cfg" for m in
                    ("default", "few_registers", "slow_memory", "no_fused", "wide_fast")]
        for name, (text, expected) in old["fixtures"]().items():
            _, accepted = invoke(binary, text, machines[0], "bdd")
            assert accepted == expected, ("inherited BDD gate", name)
            if not expected:
                _, accepted = invoke(binary, text, machines[0], "packed")
                assert not accepted, ("inherited packed gate", name)
        print("PASS all inherited proof/budget gates", flush=True)
        for name, (text, expected, positions) in fixtures().items():
            packed, accepted = invoke(binary, text, machines[0], "packed")
            assert accepted == expected, (name, accepted)
            if not accepted:
                print("PASS rejected", name, flush=True); continue
            bdd, accepted = invoke(binary, text, machines[0], "bdd")
            assert accepted
            p = K.parse_program(text)
            original, pbdd, ppacked = [K.compile_program(K.parse_program(t)) for t in (text, bdd, packed)]
            projected = []
            for key in range(1 << len(positions)):
                args = [0] * len(p.params)
                for bit, (param, source) in enumerate(positions):
                    args[param] |= ((key >> bit) & 1) << source
                projected.append(args)
            inputs = projected + [[(i * (2*j+1) * 0x01010101) & 0xffffffff for j in range(len(p.params))]
                                  for i in range(256)]
            inputs += [[rng.getrandbits(32) for _ in p.params] for _ in range(256)]
            inputs += [[v] * len(p.params) for v in (0, 1, 31, 32, 0x7fffffff, 0x80000000, 0xffffffff)]
            for args in inputs:
                segments = [(0, [19, 0xffffffff]), (4095, [7])]; vin = {0: [17]}
                reference = K.execute(original, args, segments, vin, 20001)
                for mode, cp in (("bdd", pbdd), ("packed", ppacked)):
                    result = K.execute(cp, args, segments, vin, 20001)
                    diff = K.first_difference(reference, result)
                    assert not diff, (name, mode, args, diff, packed)
                    checks += 1
            for cfg in machines:
                output, accepted = invoke(binary, text, cfg, "packed")
                assert accepted and output == packed, (name, "machine instability")
                mc = K.load_machine(str(cfg)); K.check_machine_features(K.parse_program(packed), mc)
                before = after = source = 0
                for args in projected:
                    for mode, cp in (("original", original), ("bdd", pbdd), ("packed", ppacked)):
                        run = K.execute(cp, args, [], {}, 20001, want_trace=True)
                        cycles = K.time_trace(cp, run.trace, mc)
                        if mode == "original": source += cycles
                        elif mode == "bdd": before += cycles
                        else: after += cycles
                row = dict(case=name, machine=cfg.stem, original=source, bdd=before, packed=after,
                           bdd_instructions=len(K.parse_program(bdd).instrs), packed_instructions=len(K.parse_program(packed).instrs))
                timings.append(row)
                if name in ("dense4", "dense8", "recurrence15", "recurrence255"):
                    print("CYCLES", row, flush=True)
            if artifact:
                for mode, output in (("original", text), ("bdd", bdd), ("packed", packed)):
                    (artifact / f"{name}-{mode}.kir").write_text(output)
            print("PASS", name, flush=True)
        if artifact: (artifact / "timing.json").write_text(json.dumps(timings, indent=2) + "\n")
        assert any(r["packed"] < r["bdd"] for r in timings if r["case"].startswith("recurrence")), "no recurrence win"
    print(f"{checks} official comparisons; proof gates, field bounds, SSA, aliasing, determinism passed")


if __name__ == "__main__":
    main()
