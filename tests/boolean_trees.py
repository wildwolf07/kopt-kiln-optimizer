#!/usr/bin/env python3
"""Differential test for boolean-tree rewriting.

Generates straight-line and small-loop programs mixing and/or/xor, not
(xor with 0xFFFFFFFF), add and sub over few operands and assorted constants,
including add/sub pairs whose operands share bits (where the bitwise rules must
not apply). Every dumped candidate and the output are compared with the
original on generated inputs, plus edge values, using the kit's interpreter.
"""
import argparse
import os
from pathlib import Path
import random
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
KIT = Path(os.environ.get("KIT", ROOT.parent / "official-LLH-26/Compilers/COMP10"))
sys.path.insert(0, str(KIT))
import kirlib as K  # noqa: E402

CONSTS = ["0", "-1", "0xFFFFFFFF", "1", "7", "0x80000000", "0x0F0F0F0F", "255"]


def program(rng):
    lines = ["func gen(v0, v1, v2)", "entry:"]
    vals = ["v0", "v1", "v2"]
    n = 3
    for _ in range(rng.randrange(4, 14)):
        n += 1
        d = "v%d" % n
        op = rng.choice(["and", "or", "xor", "xor", "add", "sub", "not", "and", "or"])
        a = rng.choice(vals[-4:] + vals[:3])
        b = rng.choice(vals + CONSTS[:3] if rng.random() < 0.85 else CONSTS)
        if op == "not":
            lines.append("  xor %s, %s, %s" % (d, a, rng.choice(["-1", "0xFFFFFFFF"])))
        else:
            if rng.random() < 0.5:
                a, b = b, a
            if a in CONSTS and b in CONSTS:
                b = "v0"
            lines.append("  %s %s, %s, %s" % (op, d, a, b))
        vals.append(d)
    k = rng.random()
    if k < 0.3:
        lines.append("  store 5, %s" % vals[-2])
    lines.append("  ret %s" % vals[-1])
    return "\n".join(lines) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--count", type=int, default=400)
    ap.add_argument("--seed", type=int, default=9101)
    ap.add_argument("--bin", default=str(ROOT / "build/kopt-bin"))
    a = ap.parse_args()
    rng = random.Random(a.seed)
    machines = ["default", "few_registers", "no_fused", "wide_fast"]
    env = {k: v for k, v in os.environ.items() if not k.startswith("KOPT_")}
    edge = [0, 1, 2, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0x0F0F0F0F, 0xF0F0F0F0, 0xAAAAAAAA, 0x55555555]
    checks = candidates = shrunk = 0
    with tempfile.TemporaryDirectory() as td:
        for i in range(a.count):
            text = program(rng)
            src = Path(td) / ("b%d.kir" % i)
            src.write_text(text)
            orig = K.compile_program(K.load_program(str(src)))
            dump = Path(td) / ("d%d" % i)
            dump.mkdir()
            machine = KIT / "machines" / ("machine_%s.cfg" % machines[i % len(machines)])
            p = subprocess.run([a.bin, str(src), "--machine", str(machine), "-o", str(dump / "out.kir")],
                               env=dict(env, KOPT_DUMP=str(dump)), capture_output=True, text=True, timeout=60)
            if p.returncode != 0:
                raise AssertionError("kopt failed: %s\n%s" % (p.stderr[-400:], text))
            r = random.Random(i)
            args = [[r.choice(edge) if r.random() < 0.5 else r.getrandbits(32) for _ in range(3)] for _ in range(24)]
            for f in sorted(dump.glob("*.kir")):
                cand = K.compile_program(K.load_program(str(f)))
                candidates += 1
                for arg in args:
                    x = K.execute(orig, arg, [], {}, 100000)
                    y = K.execute(cand, arg, [], {}, 100000)
                    d = K.first_difference(x, y)
                    if d:
                        raise AssertionError("%s (%s) differs on %s: %s\n%s" % (
                            f.name, f.read_text().split("\n", 1)[0], arg, d, text))
                    checks += 1
            if (dump / "out.kir").read_text().count("\n") < text.count("\n"):
                shrunk += 1
    print("PASS boolean trees: %d programs (%d shorter), %d candidates, %d official comparisons"
          % (a.count, shrunk, candidates, checks))


if __name__ == "__main__":
    main()
