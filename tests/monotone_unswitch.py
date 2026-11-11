#!/usr/bin/env python3
"""Differential test for monotone unswitching ("msplit" loop plans).

Generates random loops whose branch conditions read registers that are written
mostly (not always) behind one side of the branch, plus loads, stores, volatile
output, possibly-trapping division and an optional enclosing loop. Every dumped
candidate built by an msplit plan is compared with the original program on
generated inputs using the kit's interpreter, so fallback to another candidate
cannot hide a wrong transformation. Near misses (a tested register also written
on the stable side) must be rejected by the pass; if not, a comparison fails.
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

REGS = ["v1", "v2", "v3", "v4", "v5"]


class Gen:
    def __init__(self, rng):
        self.rng = rng
        self.lines = []
        self.blocks = 0
        self.tmp = 20

    def label(self, base):
        self.blocks += 1
        return "%s%d" % (base, self.blocks)

    def t(self):
        self.tmp += 1
        return "v%d" % self.tmp

    def emit(self, s):
        self.lines.append("  " + s)

    def operand(self):
        r = self.rng.random()
        if r < 0.6:
            return self.rng.choice(REGS)
        return str(self.rng.choice([0, 1, 2, 3, 5, 7, 8, 15, 16, 0xFFFFFFFF, 0x80000000]))

    def write(self, reg):
        rng = self.rng
        k = rng.random()
        if k < 0.35:
            self.emit("add %s, %s, %s" % (reg, reg, rng.choice(["1", "1", "2", "0xFFFFFFFF", self.operand()])))
        elif k < 0.55:
            self.emit("%s %s, %s, %s" % (rng.choice(["xor", "and", "or", "sub", "mul", "shl", "shr", "lt", "eq"]),
                                         reg, self.operand(), self.operand()))
        elif k < 0.7:
            a = self.t()
            self.emit("and %s, %s, 31" % (a, self.operand()))
            self.emit("load %s, %s" % (reg, a))
        elif k < 0.8:
            a = self.t()
            self.emit("and %s, %s, 7" % (a, self.operand()))
            self.emit("div %s, %s, %s" % (reg, self.operand(), a))
        else:
            self.emit("select %s, %s, %s, %s" % (reg, self.operand(), self.operand(), self.operand()))

    def effect(self):
        rng = self.rng
        k = rng.random()
        if k < 0.5:
            a = self.t()
            self.emit("and %s, %s, 15" % (a, self.operand()))
            self.emit("add %s, %s, 32" % (a, a))
            self.emit("store %s, %s" % (a, self.operand()))
        elif k < 0.8:
            self.emit("vstore 0, %s" % self.operand())
        else:
            a = self.t()
            self.emit("add %s, %s, %s" % (a, self.operand(), rng.choice(["0", "4000", "100"])))
            self.emit("store %s, 1" % a)   # may trap with bad_address

    def cond(self, regs):
        rng = self.rng
        c = self.t()
        a = rng.choice(regs)
        k = rng.random()
        if k < 0.45:
            self.emit("lt %s, %s, %s" % (c, a, self.operand()))
        elif k < 0.6:
            self.emit("lt %s, %s, %s" % (c, self.operand(), a))
        elif k < 0.75:
            self.emit("eq %s, %s, %s" % (c, a, self.operand()))
        else:
            u = self.t()
            self.emit("add %s, %s, %s" % (u, a, self.operand()))
            self.emit("and %s, %s, %s" % (c, u, rng.choice(["1", "3", self.operand()])))
        return c

    def body(self, depth, mono, allowed):
        """Straight-line work then maybe an if; jumps to the returned join label."""
        rng = self.rng
        for _ in range(rng.randrange(0, 3)):
            reg = rng.choice(REGS)
            # Monotone registers are written only where allowed, with rare violations.
            if reg in mono and not allowed and rng.random() < 0.9:
                continue
            self.write(reg)
        if rng.random() < 0.5:
            self.effect()
        if depth > 0 and rng.random() < 0.8:
            c = self.cond(mono if rng.random() < 0.8 else REGS)
            then, els, join = self.label("T"), self.label("E"), self.label("J")
            swap = rng.random() < 0.3
            self.emit("br %s, %s, %s" % (c, els if swap else then, then if swap else els))
            self.lines.append(then + ":")
            self.body(depth - 1, mono, True)
            self.emit("jmp " + join)
            self.lines.append(els + ":")
            self.body(depth - 1, mono, allowed)
            self.emit("jmp " + join)
            self.lines.append(join + ":")

    def program(self):
        rng = self.rng
        mono = rng.sample(REGS, rng.choice([1, 1, 2]))
        self.lines = ["func gen(v0, v9)", "entry:"]
        for r in REGS:
            self.emit("and %s, v9, %d" % (r, rng.choice([1, 3, 7, 15])) if rng.random() < 0.5
                      else "const %s, %d" % (r, rng.randrange(0, 9)))
        self.emit("and v6, v0, 15")
        outer = rng.random() < 0.3
        self.emit("const v8, 0")
        self.emit("jmp outer")
        self.lines.append("outer:")
        self.emit("const v7, 0")
        self.emit("jmp head")
        self.lines.append("head:")
        self.emit("lt v10, v7, v6")
        self.emit("br v10, body0, exit")
        self.lines.append("body0:")
        self.body(2, mono, False)
        self.emit("add v7, v7, 1")
        self.emit("jmp head")
        self.lines.append("exit:")
        if outer:
            self.emit("add v8, v8, 1")
            self.emit("lt v11, v8, 3")
            self.emit("br v11, outer, done")
            self.lines.append("done:")
        self.emit("xor v12, v1, v2")
        self.emit("add v12, v12, v3")
        self.emit("mul v13, v4, 31")
        self.emit("add v12, v12, v13")
        self.emit("xor v12, v12, v5")
        self.emit("ret v12")
        return "\n".join(self.lines) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--count", type=int, default=300)
    ap.add_argument("--seed", type=int, default=4411)
    ap.add_argument("--inputs", type=int, default=40)
    ap.add_argument("--bin", default=str(ROOT / "build/kopt-bin"))
    a = ap.parse_args()
    rng = random.Random(a.seed)
    machines = ["default", "wide_fast", "few_registers"]
    applied = candidates = checks = 0
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
            run_env = dict(env, KOPT_STRICT="1", KOPT_DUMP=str(dump))
            p = subprocess.run([a.bin, str(src), "--machine", str(machine), "-o", str(dump / "out.kir")],
                               env=run_env, capture_output=True, text=True, timeout=120)
            if p.returncode != 0:
                raise AssertionError("kopt failed on program %d: %s\n%s" % (i, p.stderr[-500:], text))
            files = [f for f in dump.glob("cand*.kir") if "/msplit" in f.read_text().split("\n", 1)[0]]
            files.append(dump / "out.kir")
            if len(files) > 1:
                applied += 1
            inputs = K.generate_inputs(2, a.inputs, a.seed * 1000 + i)
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
                        raise AssertionError("%s differs on %s: %s\n%s" % (f.name, inp.args, diff, text))
                    checks += 1
    if applied < a.count // 10:
        raise AssertionError("msplit applied to only %d of %d programs" % (applied, a.count))
    print("PASS monotone unswitch: %d programs (%d with msplit candidates), %d candidates, %d official comparisons"
          % (a.count, applied, candidates, checks))


if __name__ == "__main__":
    main()
