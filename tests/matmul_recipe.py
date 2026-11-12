#!/usr/bin/env python3
"""Differential test for matrix-product recipes (candidates named "matmul").

Generates triple loop nests in the shape a front end produces for
C[i][j] = sum_k A[i][k] * B[k][j] with varied trip counts, bases, strides,
operand order, mac or mul+add accumulation and return values, plus near misses
that the recognizer must reject or still handle exactly: C overlapping A or B,
out-of-range addresses (traps), duplicate C words, a store inside the inner
loop, extra effects and a nonzero accumulator start. Every dumped candidate and
the output are compared with the original on generated inputs.
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


def program(rng):
    N = rng.choice([1, 2, 3, 4, 4, 5, 6, 8])
    M = rng.choice([1, 2, 3, 4, 4, 5, 8])
    P = rng.choice([1, 2, 3, 4, 4, 6, 8])
    lda = rng.choice([P, P, P + 1, 8])
    ldb = rng.choice([M, M, M + 2, 8])
    ldc = rng.choice([M, M, M + 1, 8])
    abase = rng.choice([0, 0, 10, 100])
    bbase = abase + N * lda + rng.choice([0, 0, 3, 50])
    cbase = bbase + P * ldb + rng.choice([0, 0, 7, 200])
    kind = rng.random()
    note = "ok"
    if kind < 0.08:
        cbase = abase + rng.randrange(0, max(1, N * lda)); note = "C overlaps A"
    elif kind < 0.14:
        cbase = bbase + rng.randrange(0, max(1, P * ldb)); note = "C overlaps B"
    elif kind < 0.19:
        cbase = 4096 - rng.randrange(1, 8); note = "C out of range"
    elif kind < 0.23:
        ldc = 0; note = "duplicate C words"
    swap = rng.random() < 0.5
    mac = rng.random() < 0.3
    inner_store = rng.random() < 0.05
    extra = rng.random() < 0.05
    start = "0" if rng.random() < 0.95 else "1"
    ret = rng.choice(["0", "v90", "7"])
    L = ["func mm(v90)", "entry:", "  const v0, 0", "  jmp h1",
         "h1:", "  lt v2, v0, %d" % N, "  br v2, b1, x1",
         "b1:", "  const v3, 0", "  jmp h2",
         "h2:", "  lt v5, v3, %d" % M, "  br v5, b2, x2",
         "b2:", "  const v6, %s" % start, "  const v7, 0", "  jmp h3",
         "h3:", "  lt v9, v7, %d" % P, "  br v9, b3, x3",
         "b3:",
         "  mul v11, v0, %d" % lda, "  add v12, v11, v7", "  add v12, v12, %d" % abase, "  load v13, v12",
         "  mul v16, v7, %d" % ldb, "  add v17, v16, v3", "  add v18, v17, %d" % bbase, "  load v19, v18"]
    x, y = ("v13", "v19") if not swap else ("v19", "v13")
    if mac:
        L.append("  mac v6, %s, %s, v6" % (x, y))
    else:
        L += ["  mul v20, %s, %s" % (x, y), "  add v6, v6, v20"]
    if inner_store:
        L.append("  store %d, v6" % (cbase,))
    if extra:
        L.append("  vstore 1, v6")
    L += ["  add v7, v7, 1", "  jmp h3",
          "x3:", "  mul v26, v0, %d" % ldc, "  add v27, v26, %d" % cbase, "  add v28, v27, v3", "  store v28, v6",
          "  add v3, v3, 1", "  jmp h2",
          "x2:", "  add v0, v0, 1", "  jmp h1",
          "x1:", "  ret %s" % ret]
    return "\n".join(L) + "\n", note


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--count", type=int, default=150)
    ap.add_argument("--seed", type=int, default=6401)
    ap.add_argument("--bin", default=str(ROOT / "build/kopt-bin"))
    a = ap.parse_args()
    rng = random.Random(a.seed)
    machines = ["default", "slow_memory", "wide_fast", "no_fused", "few_registers"]
    env = {k: v for k, v in os.environ.items() if not k.startswith("KOPT_")}
    applied = candidates = checks = 0
    with tempfile.TemporaryDirectory() as td:
        for i in range(a.count):
            text, note = program(rng)
            src = Path(td) / ("m%d.kir" % i)
            src.write_text(text)
            orig = K.compile_program(K.load_program(str(src)))
            dump = Path(td) / ("d%d" % i)
            dump.mkdir()
            machine = KIT / "machines" / ("machine_%s.cfg" % machines[i % len(machines)])
            p = subprocess.run([a.bin, str(src), "--machine", str(machine), "-o", str(dump / "out.kir")],
                               env=dict(env, KOPT_DUMP=str(dump)), capture_output=True, text=True, timeout=120)
            if p.returncode != 0:
                raise AssertionError("kopt failed: %s\n%s" % (p.stderr[-400:], text))
            files = [f for f in sorted(dump.glob("*.kir")) if "matmul" in f.read_text().split("\n", 1)[0]]
            if files:
                applied += 1
            files.append(dump / "out.kir")
            r = random.Random(i)
            inputs = []
            for _ in range(12):
                mem = [r.choice([0, 1, 2, 0xFFFFFFFF, 0x80000000, r.getrandbits(32), r.randrange(100)]) for _ in range(512)]
                inputs.append(([r.getrandbits(32)], [(0, mem)]))
            for f in files:
                cand = K.compile_program(K.load_program(str(f)))
                candidates += 1
                for args, seg in inputs:
                    xr = K.execute(orig, args, seg, {}, 200000)
                    yr = K.execute(cand, args, seg, {}, 20 * xr.steps + 1000)
                    d = K.first_difference(xr, yr)
                    if d:
                        raise AssertionError("%s (%s) differs [%s]: %s\n%s" % (
                            f.name, f.read_text().split("\n", 1)[0], note, d, text))
                    checks += 1
    if applied < a.count // 4:
        raise AssertionError("matmul candidates in only %d of %d programs" % (applied, a.count))
    print("PASS matmul recipe: %d programs (%d with matmul candidates), %d candidates, %d official comparisons"
          % (a.count, applied, candidates, checks))


if __name__ == "__main__":
    main()
