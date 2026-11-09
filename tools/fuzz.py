#!/usr/bin/env python3
"""fuzz.py - differential testing of kopt on random KIR programs.

Generates random but valid programs that stress the rules of KIR_SPEC.md
section 7: traps (div/mod by zero, bad addresses, explicit traps), volatile
I/O ordering, memory aliasing, irreducible and unreachable control flow, odd
shift amounts and signed edge values. Each program is optimized by kopt for a
random machine, then compared with the original by the kit's reference
interpreter (kirlib) on many inputs. Any difference is saved as a reproducer.

  KIT=/path/to/COMP10 tools/fuzz.py --count 500 --seed 1
"""
import argparse
import multiprocessing as mp
import os
import random
import subprocess
import sys
import tempfile

KIT = os.environ.get("KIT", os.path.join(os.path.dirname(__file__), "..", "..",
                                         "official-LLH-26", "Compilers", "COMP10"))
KIT = os.path.abspath(KIT)
sys.path.insert(0, KIT)
import kirlib as K  # noqa: E402

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
KOPT = os.path.join(ROOT, "kopt")
FAILDIR = os.path.join(ROOT, "tests", "fuzz_failures")

BIN = ["add", "sub", "mul", "and", "or", "xor", "shl", "shr", "lt", "eq"]
LITS = [0, 1, 2, 3, 4, 5, 7, 8, 16, 31, 32, 33, 63, 64, 100, 255, 1000, 3071, 3072, 4095, 4096,
        -1, -2, -8, 0x7FFFFFFF, -2147483648, 0xFFFF, 12345]


def rand_machine(rng):
    return {
        "issue_width": rng.choice([1, 2, 2, 3, 4]),
        "mem_ports": rng.choice([1, 1, 2]),
        "registers": rng.choice([4, 5, 6, 8, 8, 12, 16]),
        "reg_spill_penalty": rng.choice([0, 3, 5, 8]),
        "taken_branch_penalty": rng.choice([0, 1, 2, 4]),
        "icache_size": rng.choice([8, 16, 32, 64, 128]),
        "icache_penalty": rng.choice([0, 1, 2, 4]),
        "lat_alu": rng.choice([1, 1, 2]),
        "lat_mul": rng.choice([1, 2, 3, 5]),
        "lat_div": rng.choice([4, 12, 20]),
        "lat_load": rng.choice([1, 2, 4, 12]),
        "lat_mac": rng.choice([1, 2, 3, 5]),
        "lat_addsh": rng.choice([1, 2]),
        "fused_mac": rng.choice([0, 1]),
        "fused_addsh": rng.choice([0, 1]),
    }


class Gen(object):
    def __init__(self, rng, mc):
        self.rng = rng
        self.mc = mc
        self.nregs = rng.randint(3, 20)
        self.nparams = rng.randint(0, min(4, self.nregs))
        # none: no memory at all; bounded: every address provably < 3072 (so kopt
        # may use the scratch region for spills); any: anything, including traps.
        self.memmode = rng.choice(["none", "bounded", "any", "any"])
        self.counted = rng.random() < 0.5

    def reg(self):
        return "v%d" % self.rng.randrange(self.nregs)

    def src(self):
        if self.rng.random() < 0.7:
            return self.reg()
        return str(self.rng.choice(LITS))

    def addr(self):
        r = self.rng.random()
        if self.memmode == "bounded":
            if r < 0.7:
                return None, "and %s, %s, %d" % ("{t}", self.reg(), self.rng.choice([7, 15, 63, 255, 2047]))
            return str(self.rng.choice([0, 1, 5, 64, 1000, 3071])), None
        if r < 0.45:
            return None, "and %s, %s, %d" % ("{t}", self.reg(), self.rng.choice([7, 15, 63, 255]))
        if r < 0.6:
            return str(self.rng.choice([0, 1, 5, 64, 3071, 3072, 4095])), None
        if r < 0.7:
            return str(self.rng.choice([4096, -1, 99999])), None
        return self.reg(), None   # anything: may trap

    def instr(self, out):
        rng = self.rng
        r = rng.random()
        d = self.reg()
        if r < 0.40:
            out.append("%s %s, %s, %s" % (rng.choice(BIN), d, self.src(), self.src()))
        elif r < 0.47:
            out.append("const %s, %d" % (d, rng.choice(LITS)))
        elif r < 0.52:
            out.append("mov %s, %s" % (d, self.src()))
        elif r < 0.57:
            out.append("select %s, %s, %s, %s" % (d, self.src(), self.src(), self.src()))
        elif r < 0.63:
            out.append("%s %s, %s, %s" % (rng.choice(["div", "mod"]), d, self.src(),
                                          rng.choice([self.src(), self.src(), "1", "-1", "7", "8", "0"])))
        elif r < 0.73 and self.memmode != "none":
            a, pre = self.addr()
            if pre:
                t = self.reg()
                out.append(pre.replace("{t}", t))
                a = t
            out.append("load %s, %s" % (d, a))
        elif r < 0.82 and self.memmode != "none":
            a, pre = self.addr()
            if pre:
                t = self.reg()
                out.append(pre.replace("{t}", t))
                a = t
            out.append("store %s, %s" % (a, self.src()))
        elif r < 0.87:
            out.append("vload %s, %s" % (d, rng.choice(["0", "1", "2", self.reg()])))
        elif r < 0.91:
            out.append("vstore %s, %s" % (rng.choice(["0", "1", "3"]), self.src()))
        elif r < 0.95 and self.mc["fused_mac"]:
            out.append("mac %s, %s, %s, %s" % (d, self.src(), self.src(), self.src()))
        elif self.mc["fused_addsh"]:
            out.append("addsh %s, %s, %s, %d" % (d, self.src(), self.src(), rng.randrange(32)))
        else:
            out.append("add %s, %s, %s" % (d, self.src(), self.src()))

    def program(self):
        rng = self.rng
        nb = rng.randint(1, 9)
        labels = ["b%d" % i for i in range(nb)]
        # A loop counter register that bounds every back edge, so most runs end.
        ctr = "v%d" % self.nregs
        lines = ["func f(%s)" % ", ".join("v%d" % i for i in range(self.nparams))]
        for i, lab in enumerate(labels):
            lines.append("%s:" % lab)
            body = []
            if i == 0:
                body.append("const %s, %d" % (ctr, rng.choice([3, 10, 40])))
            for _ in range(rng.randint(0, 7)):
                self.instr(body)
            lines.extend("  " + b for b in body)
            r = rng.random()
            later = labels[i + 1:] or [labels[-1]]
            if r < 0.30 and i < nb - 1 and self.counted:
                # counted self-loop: add i, i, s ; lt c, i, n ; br c, self, next
                iv, c = self.reg(), self.reg()
                n = rng.choice([self.reg(), str(rng.choice([0, 5, 17, 40, -3, 2147483647, -2147483648]))])
                if iv == c:
                    c = ctr
                lines.append("  add %s, %s, %d" % (iv, iv, rng.choice([1, 1, 2, 3])))
                lines.append("  lt %s, %s, %s" % (c, iv, n))
                lines.append("  br %s, %s, %s" % (c, lab, rng.choice(later)))
            elif r < 0.08:
                lines.append("  trap %s" % self.src())
            elif r < 0.2 or i == nb - 1:
                lines.append("  ret %s" % self.src())
            elif r < 0.45:
                lines.append("  jmp %s" % rng.choice(later))
            elif r < 0.75:
                lines.append("  br %s, %s, %s" % (self.src(), rng.choice(later), rng.choice(labels)))
            else:
                # bounded back edge (possibly into the middle of a loop: irreducible)
                tgt = rng.choice(labels[:i + 1])
                lines.append("  sub %s, %s, 1" % (ctr, ctr))
                lines.append("  br %s, %s, %s" % (ctr, tgt, rng.choice(later)))
        return "\n".join(lines) + "\n"


def ptr_program(rng, mc):
    """A loop whose memory address is a pointer that grows only in some rounds
    (output cursors, merges). The address may or may not reach the scratch
    region (3072+) depending on the base, the step and the trip count, which is
    exactly what the trip-count range bounds must get right."""
    g = Gen(rng, mc)
    g.memmode = "bounded"
    g.nregs = rng.randint(8, 16)
    g.nparams = 2
    n, i, j, k, m, c, a = ("v%d" % (g.nregs + x) for x in range(7))
    base = rng.choice([0, 64, 1000, 2900, 3000, 3040, 3060, 3064, 3070, 3071])
    mask = rng.choice([7, 15, 31, 63])
    step = rng.choice([1, 1, 2, 3, -1, 0])
    k0 = rng.choice([0, 1, 5, 40])
    filler = lambda: [ln for _ in range(rng.randint(0, 5)) for ln in (lambda o: (g.instr(o), o)[1])([])]
    L = ["func f(v0, v1)", "entry:",
         "  and %s, v0, %d" % (n, mask), "  and %s, v1, %d" % (m, rng.choice([3, 7, 15])),
         "  const %s, 0" % i, "  const %s, 0" % j, "  const %s, %d" % (k, k0)]
    L += ["  " + x for x in filler()]
    L += ["  jmp head", "head:", "  lt %s, %s, %s" % (c, i, n), "  br %s, body, exit" % c, "body:"]
    L += ["  " + x for x in filler()]
    if rng.random() < 0.5:
        # cursor: k moves by `step` in some rounds, i always grows
        L += ["  and %s, %s, 1" % (c, g.reg()), "  br %s, inc, latch" % c,
              "inc:", "  add %s, %s, %d" % (k, k, step), "  jmp latch",
              "latch:", "  add %s, %s, %d" % (i, i, rng.choice([1, 1, 2]))]
    else:
        # merge: i or j grows (j only while j < m), k grows every round
        L += ["  lt %s, %s, %s" % (c, j, m), "  br %s, both, onlyi" % c,
              "both:", "  and %s, %s, 1" % (c, g.reg()), "  br %s, inci, incj" % c,
              "inci:", "  add %s, %s, 1" % (i, i), "  jmp latch",
              "incj:", "  add %s, %s, 1" % (j, j), "  jmp latch",
              "onlyi:", "  add %s, %s, 1" % (i, i), "  jmp latch",
              "latch:", "  add %s, %s, %d" % (k, k, max(step, 1))]
    L += ["  add %s, %s, %d" % (a, k, base)]
    L.append(rng.choice(["  store %s, %s" % (a, g.reg()), "  load %s, %s" % (g.reg(), a)]))
    L += ["  " + x for x in filler()]
    L += ["  jmp head", "exit:", "  add %s, %s, %d" % (a, k, base), "  load %s, %s" % (c, a)]
    L += ["  " + x for x in filler()]
    L += ["  ret %s" % rng.choice([c, g.reg()])]
    return "\n".join(L) + "\n"


def write_machine(path, mc):
    with open(path, "w") as f:
        for k, v in mc.items():
            f.write("%s = %d\n" % (k, v))


def one(args):
    idx, seed, ninputs = args
    rng = random.Random(seed * 1000003 + idx)
    mc = rand_machine(rng)
    src = ptr_program(rng, mc) if rng.random() < 0.25 else Gen(rng, mc).program()
    with tempfile.TemporaryDirectory() as td:
        pin, pout, pm = (os.path.join(td, n) for n in ("in.kir", "out.kir", "m.cfg"))
        with open(pin, "w") as f:
            f.write(src)
        write_machine(pm, mc)
        try:
            orig = K.parse_program(src)
        except K.KirError as e:
            return ("BADGEN", idx, str(e), src, mc)
        env = dict(os.environ, KOPT_STRICT="1")
        p = subprocess.run([os.path.join(ROOT, "build", "kopt-bin"), pin, "--machine", pm, "-o", pout],
                           capture_output=True, text=True, timeout=30, env=env)
        if p.returncode != 0:
            return ("KOPT-EXIT", idx, p.stderr[-400:], src, mc)
        try:
            opt = K.load_program(pout)
            K.check_machine_features(opt, mc)
        except K.KirError as e:
            return ("INVALID", idx, str(e), src, mc)
        cp0, cp1 = K.compile_program(orig), K.compile_program(opt)
        for inp in K.generate_inputs(len(orig.params), ninputs, seed * 7919 + idx):
            a = K.execute(cp0, inp.args, inp.segments, inp.vin, 20000)
            if a.status == "TIMEOUT":
                continue
            b = K.execute(cp1, inp.args, inp.segments, inp.vin, 20 * a.steps + 1000)
            diff = K.first_difference(a, b)
            if diff:
                return ("MISMATCH", idx, diff + "\n" + K.format_input(inp), src, mc)
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--count", type=int, default=200)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--inputs", type=int, default=150)
    ap.add_argument("--jobs", type=int, default=os.cpu_count())
    a = ap.parse_args()
    jobs = [(i, a.seed, a.inputs) for i in range(a.count)]
    bad = 0
    with mp.Pool(a.jobs) as pool:
        for res in pool.imap_unordered(one, jobs):
            if res is None:
                continue
            kind, idx, msg, src, mc = res
            bad += 1
            os.makedirs(FAILDIR, exist_ok=True)
            base = os.path.join(FAILDIR, "s%d_%d" % (a.seed, idx))
            with open(base + ".kir", "w") as f:
                f.write(src)
            write_machine(base + ".cfg", mc)
            with open(base + ".txt", "w") as f:
                f.write(kind + "\n" + msg + "\n")
            print("%s #%d: %s" % (kind, idx, msg.splitlines()[0] if msg else ""))
    print("%d/%d programs failed" % (bad, a.count))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
