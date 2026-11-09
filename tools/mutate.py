#!/usr/bin/env python3
"""mutate.py - robustness check against the hidden-test variations.

The hidden tests include practice programs with renamed registers and
shuffled blocks. For every bench program this renames the registers at
random, moves every block except the entry to a random place, runs kopt on
both versions, checks both outputs against the original (kit's kirlib), and
reports where the mutated program ends up slower than the original.

  tools/mutate.py [--machine default] [--seed 1] [names...]
"""
import argparse
import glob
import multiprocessing as mp
import os
import random
import re
import subprocess
import sys
import tempfile
import zlib

KIT = os.environ.get("KIT", os.path.join(os.path.dirname(__file__), "..", "..",
                                         "official-LLH-26", "Compilers", "COMP10"))
KIT = os.path.abspath(KIT)
sys.path.insert(0, KIT)
import kirlib as K  # noqa: E402

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
KOPT = os.path.join(ROOT, "kopt")


def mutate(src, rng):
    lines = src.splitlines()
    # Rename every register vN to a random fresh name.
    regs = sorted(set(re.findall(r"\bv(\d+)\b", src)), key=int)
    perm = list(range(len(regs) + 50))
    rng.shuffle(perm)
    mapping = {r: "v%d" % perm[i] for i, r in enumerate(regs)}
    lines = [re.sub(r"\bv(\d+)\b", lambda m: mapping[m.group(1)], ln) if not ln.lstrip().startswith(";") else ln
             for ln in lines]
    # Split into header and blocks; keep the entry block first.
    head, blocks, cur = [], [], None
    for ln in lines:
        s = ln.strip()
        if not s or s.startswith(";"):
            continue
        if s.startswith("func"):
            head.append(ln)
        elif s.endswith(":") and not s.startswith(("v", " ")) and " " not in s:
            cur = [ln]
            blocks.append(cur)
        elif cur is not None:
            cur.append(ln)
        else:
            head.append(ln)
    rest = blocks[1:]
    rng.shuffle(rest)
    out = head + blocks[0] + [ln for b in rest for ln in b]
    return "\n".join(out) + "\n"



def one(args):
    name, machine, seed = args
    rng = random.Random(zlib.crc32(("%s/%d" % (name, seed)).encode()))
    src_path = os.path.join(KIT, "bench", name + ".kir")
    with open(src_path) as f:
        src = f.read()
    msrc = mutate(src, rng)
    with tempfile.TemporaryDirectory() as td:
        pm = os.path.join(td, "m.kir")
        o1, o2 = os.path.join(td, "o1.kir"), os.path.join(td, "o2.kir")
        with open(pm, "w") as f:
            f.write(msrc)
        try:
            K.parse_program(msrc)
        except K.KirError as e:
            return (name, "BADMUT", str(e))
        for s, o in ((src_path, o1), (pm, o2)):
            r = subprocess.run([KOPT, s, "--machine", machine, "-o", o], capture_output=True, text=True, timeout=60)
            if r.returncode != 0:
                return (name, "KOPT-EXIT", r.stderr[-300:])
        orig = K.compile_program(K.parse_program(src))
        inp_file = os.path.join(KIT, "bench", name + ".in")
        np_ = len(K.parse_program(src).params)
        inputs = [K.load_input(inp_file, np_)] if os.path.exists(inp_file) else []
        inputs += list(K.generate_inputs(len(K.parse_program(src).params), 40, 991))
        res = []
        for o in (o1, o2):
            prog = K.load_program(o)
            cp = K.compile_program(prog)
            total = 0
            for i, inp in enumerate(inputs):
                a = K.execute(orig, inp.args, inp.segments, inp.vin, 200000)
                if a.status == "TIMEOUT":
                    continue
                b = K.execute(cp, inp.args, inp.segments, inp.vin, 20 * a.steps + 1000)
                d = K.first_difference(a, b)
                if d:
                    return (name, "MISMATCH", d)
            res.append(o)
        # cycles on the sample input
        out = subprocess.run([os.path.join(ROOT, "build", "kopt-bin"), "--sim", o1, "--machine", machine,
                              "--input", inp_file], capture_output=True, text=True).stdout
        out2 = subprocess.run([os.path.join(ROOT, "build", "kopt-bin"), "--sim", o2, "--machine", machine,
                               "--input", inp_file], capture_output=True, text=True).stdout
        c1 = int(re.search(r"cycles=(\d+)", out).group(1))
        c2 = int(re.search(r"cycles=(\d+)", out2).group(1))
        return (name, "OK", (c1, c2))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--machine", default="default")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("names", nargs="*")
    a = ap.parse_args()
    machine = os.path.join(KIT, "machines", "machine_%s.cfg" % a.machine)
    names = a.names or sorted(os.path.basename(p)[:-4] for p in glob.glob(os.path.join(KIT, "bench", "*.kir")))
    t1 = t2 = 0
    bad = 0
    worse = []
    with mp.Pool(os.cpu_count()) as pool:
        for name, kind, info in pool.imap_unordered(one, [(n, machine, a.seed) for n in names]):
            if kind != "OK":
                bad += 1
                print("%s %s: %s" % (kind, name, str(info).splitlines()[0] if info else ""))
                continue
            c1, c2 = info
            t1 += c1
            t2 += c2
            if c2 > c1:
                worse.append((c2 - c1, name, c1, c2))
    for d, n, c1, c2 in sorted(worse, reverse=True)[:15]:
        print("  %-24s %6d -> %6d (+%d)" % (n, c1, c2, d))
    print("original %d, mutated %d cycles; %d failures" % (t1, t2, bad))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
