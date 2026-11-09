#!/usr/bin/env python3
"""Kit-free compatibility tests with hand-calculated outputs and negative controls.

Uses the compiled binary directly in strict mode, then exercises the public
wrapper from another working directory. An interpreter shared with the optimizer
is not an independent equivalence oracle; run bench/fuzz/regress with the kit too.
"""
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
BIN = ROOT / "build" / "kopt-bin"
FIXTURES = ROOT / "tests" / "smoke"
# Independent inputs and expected return/trap observations (32-bit unsigned).
CASES = {
    "arithmetic": [("args -1", "RET 1"), ("args 2147483647", "RET 1"),
                   ("args 2", "RET 7")],
    "loop": [("args 0", "RET 0"), ("args 5", "RET 10"), ("args -1", "RET 105")],
    "guard": [("args 0", "RET 77"), ("args -1", "RET 2147483648"),
              ("args 3", "RET 3579139412")],
    "memory": [("args 3", "RET 42")],
    "scratch": [("args 9", "RET 16"), ("args -1", "RET 6")],
    "volatile": [("args 7\nvin 5 11 13", "RET 24")],
    "traps": [("args 0", "TRAP div_by_zero"), ("args 1", "TRAP bad_address")],
    "explicit": [("args 91", "TRAP explicit(91)")],
    "fused": [("args 6 7", "RET 73")],
    "signed_arithmetic": [("args -7", "RET 4294967289"), ("args 7", "RET 7"),
                          ("args -2147483648", "RET 268435456"),
                          ("args 2147483647", "RET 4026531856")],
}
# Own machine combinations; none are copied from the starter kit.
BASE_MACHINE = {
    "registers": 6, "issue_width": 1, "mem_ports": 1,
    "reg_spill_penalty": 6, "taken_branch_penalty": 3,
    "icache_size": 48, "icache_penalty": 1,
    "lat_alu": 1, "lat_mul": 4, "lat_div": 15, "lat_load": 5,
    "lat_mac": 4, "lat_addsh": 2, "fused_mac": 1, "fused_addsh": 1,
}
MACHINES = [
    {"registers": 6, "issue_width": 1},
    {"registers": 4, "reg_spill_penalty": 9},
    {"registers": 7, "fused_mac": 0, "fused_addsh": 0},
    {"registers": 10, "lat_load": 13, "lat_div": 17},
    {"registers": 12, "issue_width": 3, "mem_ports": 2},
]


def run(args, cwd, expected=0):
    env = dict(os.environ)
    for key in list(env):
        if key.startswith("KOPT_"):
            del env[key]
    env["KOPT_STRICT"] = "1"
    p = subprocess.run([str(x) for x in args], cwd=cwd, env=env,
                       capture_output=True, text=True, timeout=30)
    if p.returncode != expected:
        raise AssertionError("command failed: %s\n%s\n%s" % (args, p.stdout, p.stderr))
    if "optimizer failed" in p.stderr:
        raise AssertionError("wrapper fallback masked a failure: " + p.stderr)
    return p.stdout


def main():
    checked = 0
    with tempfile.TemporaryDirectory(prefix="kopt smoke ") as temp:
        td = Path(temp)
        for mi, overrides in enumerate(MACHINES):
            machine = dict(BASE_MACHINE, **overrides)
            cfg = td / ("machine %d.cfg" % mi)
            cfg.write_text("".join("%s = %s\n" % pair for pair in machine.items()))
            for name, cases in CASES.items():
                src = FIXTURES / (name + ".kir")
                out, repeat, wrapped = (td / x for x in ("out.kir", "repeat.kir", "wrapped.kir"))
                run([BIN, src, "--machine", cfg, "-o", out], td)
                run([BIN, src, "--machine", cfg, "-o", repeat], td)
                if out.read_bytes() != repeat.read_bytes():
                    raise AssertionError("non-deterministic output: " + name)
                # Exercise executable bits, arbitrary cwd and paths containing spaces.
                run([ROOT / "kopt", src, "--machine", cfg, "-o", wrapped], td)
                if out.read_bytes() != wrapped.read_bytes():
                    raise AssertionError("wrapper differs: " + name)
                if machine.get("fused_mac") == 0:
                    if re.search(r"^\s*(mac|addsh)\s", out.read_text(), re.M):
                        raise AssertionError("unsupported fused instruction: " + name)
                for ii, (input_text, expected) in enumerate(cases):
                    inp = td / ("input %d.in" % ii)
                    inp.write_text(input_text + "\n")
                    for program in (src, out):
                        observation = run([BIN, "--sim", program, "--machine", cfg,
                                           "--input", inp], td).split(" cycles=", 1)[0]
                        if observation != expected:
                            raise AssertionError("%s: expected %s, got %s" %
                                                 (program, expected, observation))
                    run([BIN, "--check", src, out, "--machine", cfg,
                         "--input", inp, "--random", 80], td)
                checked += 1
        # The comparator must reject corruption in each observable category.
        controls = [
            ("arithmetic", "ret v4", "ret 123", "args 2"),
            ("memory", "store 19, v2", "store 19, 0", "args 3"),
            ("volatile", "vstore 6, v3", "vstore 6, 0", "args 7\nvin 5 11 13"),
            ("traps", "div v1, 1, v0", "mov v1, 0", "args 0"),
        ]
        for name, before, after, input_text in controls:
            src = FIXTURES / (name + ".kir")
            text = src.read_text()
            if before not in text:
                raise AssertionError("negative control no longer applies: " + name)
            mutant, inp = td / "mutant.kir", td / "control.in"
            mutant.write_text(text.replace(before, after))
            inp.write_text(input_text + "\n")
            result = run([BIN, "--check", src, mutant, "--machine", cfg,
                          "--input", inp, "--random", 0], td, expected=1)
            if "MISMATCH" not in result:
                raise AssertionError("negative control did not detect corruption")
    print("PASS: %d program/machine pairs; 4 negative controls" % checked)


if __name__ == "__main__":
    main()
