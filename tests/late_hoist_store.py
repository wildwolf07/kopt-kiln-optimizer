#!/usr/bin/env python3
"""Differential test for join hoisting, partially dead stores and register-touch
polishing (candidates tagged /joinhoist, /deadstore and /lru).

Generates loops over a small array with overlapping reads and writes (adjacent
offsets, computed and possibly aliasing addresses), stores that are overwritten
on one path but read or trapped on another, pure and effectful branch arms,
volatile output, possibly-trapping division and out-of-range stores. Programs
use many register names so that small-register machines spill. Every dumped
candidate with one of the tags (including ones kept out of selection) is
compared with the original on generated inputs using the kit's interpreter.
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

TAGS = ("/joinhoist", "/deadstore", "/lru", "/window")
REGS = ["v1", "v2", "v3", "v4", "v5", "v6"]


class Gen:
    def __init__(self, rng):
        self.rng = rng
        self.lines = []
        self.n = 0
        self.tmp = 30

    def label(self, base):
        self.n += 1
        return "%s%d" % (base, self.n)

    def t(self):
        self.tmp += 1
        return "v%d" % self.tmp

    def emit(self, s):
        self.lines.append("  " + s)

    def operand(self):
        if self.rng.random() < 0.65:
            return self.rng.choice(REGS + ["v20"])
        return str(self.rng.choice([0, 1, 2, 3, 7, 15, 100, 0xFFFFFFFF, 0x80000000]))

    def addr(self, idx):
        """An address near the loop index: aliasing is likely."""
        rng = self.rng
        a = self.t()
        k = rng.random()
        if k < 0.5:
            self.emit("add %s, %s, %d" % (a, idx, rng.choice([0, 1, 1, 2, 3])))
        elif k < 0.8:
            self.emit("and %s, %s, 15" % (a, self.operand()))
        elif k < 0.9:
            self.emit("sub %s, %s, %d" % (a, idx, rng.choice([1, 2])))   # may go below 0: trap
        else:
            self.emit("add %s, %s, %s" % (a, self.operand(), rng.choice(["0", "4090", "3000"])))
        return a

    def pure(self, reg):
        rng = self.rng
        self.emit("%s %s, %s, %s" % (rng.choice(["add", "xor", "and", "or", "sub", "mul", "shl", "shr", "lt", "eq"]),
                                     reg, self.operand(), self.operand()))

    def step(self, idx, depth):
        rng = self.rng
        for _ in range(rng.randrange(1, 4)):
            k = rng.random()
            reg = rng.choice(REGS)
            if k < 0.35:
                self.pure(reg)
            elif k < 0.55:
                self.emit("load %s, %s" % (reg, self.addr(idx)))
            elif k < 0.8:
                self.emit("store %s, %s" % (self.addr(idx), self.operand()))
            elif k < 0.87:
                d = self.t()
                self.emit("and %s, %s, 3" % (d, self.operand()))
                self.emit("div %s, %s, %s" % (reg, self.operand(), d))
            elif k < 0.94:
                self.emit("vstore 1, %s" % self.operand())
            else:
                self.emit("select %s, %s, %s, %s" % (reg, self.operand(), self.operand(), self.operand()))
        if depth > 0 and rng.random() < 0.7:
            c = self.t()
            self.emit("lt %s, %s, %s" % (c, self.operand(), self.operand()))
            a, b, j = self.label("A"), self.label("B"), self.label("J")
            self.emit("br %s, %s, %s" % (c, a, b))
            self.lines.append(a + ":")
            if rng.random() < 0.5:
                for _ in range(rng.randrange(1, 3)):
                    self.pure(rng.choice(REGS))
            else:
                self.step(idx, depth - 1)
            self.emit("jmp " + j)
            self.lines.append(b + ":")
            if rng.random() < 0.5:
                self.pure(rng.choice(REGS))
            else:
                self.step(idx, depth - 1)
            self.emit("jmp " + j)
            self.lines.append(j + ":")

    def program(self):
        rng = self.rng
        self.lines = ["func gen(v0, v9, v20)", "entry:"]
        for r in REGS:
            self.emit("and %s, v9, %d" % (r, rng.choice([1, 3, 15, 255])) if rng.random() < 0.6
                      else "const %s, %d" % (r, rng.randrange(0, 9)))
        self.emit("and v7, v0, 15")
        self.emit("const v8, 0")
        self.emit("jmp head")
        self.lines.append("head:")
        headStore = rng.random() < 0.4
        if headStore:
            # The header recomputes an address the body stored to on the
            # previous iteration: same name, new instance, different word.
            self.emit("add v40, v8, %d" % rng.choice([0, 1, 2]))
            if rng.random() < 0.5:
                self.emit("load v41, v40")
                self.emit("add v1, v1, v41")
            self.emit("store v40, %s" % rng.choice(["v8", "v1", "7"]))
        self.emit("lt v10, v8, v7")
        self.emit("br v10, body, exit")
        self.lines.append("body:")
        if rng.random() < 0.4:
            # Bubble-like adjacent pair: overwritten on the continuing path.
            x, y, c, lo, hi = self.t(), self.t(), self.t(), self.t(), self.t()
            p1 = self.t()
            self.emit("add %s, v8, 1" % p1)
            self.emit("load %s, v8" % x)
            self.emit("load %s, %s" % (y, p1))
            self.emit("lt %s, %s, %s" % (c, y, x))
            self.emit("select %s, %s, %s, %s" % (lo, c, y, x))
            self.emit("select %s, %s, %s, %s" % (hi, c, x, y))
            self.emit("store v8, %s" % lo)
            self.emit("store %s, %s" % (p1, hi))
        self.step("v8", 2)
        if headStore and rng.random() < 0.8:
            self.emit("store v40, %s" % self.operand())
        self.emit("add v8, v8, 1")
        self.emit("jmp head")
        self.lines.append("exit:")
        self.emit("xor v11, v1, v2")
        self.emit("add v11, v11, v3")
        self.emit("mul v12, v4, 31")
        self.emit("add v11, v11, v12")
        self.emit("xor v11, v11, v5")
        self.emit("add v11, v11, v6")
        self.emit("ret v11")
        return "\n".join(self.lines) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--count", type=int, default=200)
    ap.add_argument("--seed", type=int, default=7301)
    ap.add_argument("--inputs", type=int, default=40)
    ap.add_argument("--bin", default=str(ROOT / "build/kopt-bin"))
    a = ap.parse_args()
    rng = random.Random(a.seed)
    machines = ["default", "few_registers", "wide_fast", "slow_memory"]
    applied = candidates = checks = 0
    seen = {t: 0 for t in TAGS}
    env = {k: v for k, v in os.environ.items() if not k.startswith("KOPT_")}
    with tempfile.TemporaryDirectory() as td:
        for i in range(a.count):
            text = Gen(rng).program()
            src = Path(td) / ("g%d.kir" % i)
            src.write_text(text)
            orig = K.compile_program(K.load_program(str(src)))
            dump = Path(td) / ("d%d" % i)
            dump.mkdir()
            machine = KIT / "machines" / ("machine_%s.cfg" % machines[i % len(machines)])
            p = subprocess.run([a.bin, str(src), "--machine", str(machine), "-o", str(dump / "out.kir")],
                               env=dict(env, KOPT_DUMP=str(dump)), capture_output=True, text=True, timeout=120)
            if p.returncode != 0:
                raise AssertionError("kopt failed on program %d: %s\n%s" % (i, p.stderr[-500:], text))
            files = []
            for f in sorted(dump.glob("*.kir")):
                head = f.read_text().split("\n", 1)[0]
                tags = [t for t in TAGS if t in head]
                if tags:
                    files.append(f)
                    for t in tags:
                        seen[t] += 1
            if files:
                applied += 1
            files.append(dump / "out.kir")
            inputs = K.generate_inputs(3, a.inputs, a.seed * 1000 + i)
            for f in files:
                cand = K.compile_program(K.load_program(str(f)))
                candidates += 1
                for inp in inputs:
                    x = K.execute(orig, inp.args, inp.segments, inp.vin, 100000)
                    if x.status == "TIMEOUT":
                        continue
                    y = K.execute(cand, inp.args, inp.segments, inp.vin, 20 * x.steps + 1000)
                    diff = K.first_difference(x, y)
                    if diff:
                        raise AssertionError("%s (%s) differs on %s: %s\n%s" % (
                            f.name, f.read_text().split("\n", 1)[0], inp.args, diff, text))
                    checks += 1
    if applied < a.count // 10:
        raise AssertionError("tagged candidates in only %d of %d programs" % (applied, a.count))
    print("PASS late hoist/store/lru: %d programs (%d with tagged candidates; %s), %d candidates, %d official comparisons"
          % (a.count, applied, ", ".join("%s %d" % (t, n) for t, n in seen.items()), candidates, checks))


if __name__ == "__main__":
    main()
