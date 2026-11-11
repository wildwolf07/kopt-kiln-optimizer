#!/usr/bin/env python3
"""Differential test for cross-iteration load pipelining ("across" candidates).

Generates sieve-like loop nests: an outer loop reads word BASE + i first, and an
inner loop stores to BASE2 + j with j starting at MULT*i + JB and stepping by an
invariant or constant amount. Bases, start multipliers, offsets, steps, extra
same-iteration stores and initial memory vary, including near misses where an
inner or outer store does write the next iteration's word (the pass must reject
those). Every dumped "across" candidate is compared with the original on
official-interpreter runs, so selection or fallback cannot hide an error.
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
    base = rng.choice([0, 100, 512, 3000, 4000])
    base2 = base + rng.choice([0, 0, 0, 1, -1, 2])
    mult = rng.choice([1, 2, 2, 2, 3])
    jb = rng.choice([0, 0, 1, -1, 2])
    i0 = rng.choice([1, 2, 2, 3])
    s = rng.choice([1, 1, 2])
    mask = rng.choice([15, 31, 127])
    step = rng.choice(["v4", "v4", "1", "3", "v30"])
    lines = ["func gen(v0, v9)", "entry:",
             "  and v1, v0, %d" % mask, "  add v0, v1, %d" % rng.choice([0, 2, 3]),
             "  const v3, 0", "  const v4, %d" % i0, "  add v30, v4, 1", "  jmp head",
             "head:", "  lt v5, v4, v0", "  br v5, body, exit",
             "body:", "  add v6, %d, v4" % base, "  load v7, v6"]
    if rng.random() < 0.3:
        off = rng.choice([0, -1, 2, s])          # s: writes the next word (reject)
        lines += ["  add v40, v6, %d" % off, "  add v41, v7, 1", "  store v40, v41"]
    if rng.random() < 0.2:
        lines += ["  vstore 1, v7"]
    lines += ["  and v8, v7, %d" % rng.choice([1, 3, 0xFFFFFFFF]), "  eq v8, v8, 0", "  br v8, then, next",
              "then:", "  add v3, v3, 1"]
    if mult == 1:
        lines += ["  mov v10, v4"]
    elif mult == 2:
        lines += [rng.choice(["  mul v10, v4, 2", "  shl v10, v4, 1", "  add v10, v4, v4"])]
    else:
        lines += ["  mul v10, v4, 3"]
    if jb:
        lines += ["  add v10, v10, %d" % jb]
    lines += ["  jmp ih", "ih:", "  lt v12, v10, v0", "  br v12, ib, next",
              "ib:", "  add v13, %d, v10" % base2,
              "  store v13, %s" % rng.choice(["1", "v4", "v10"]),
              "  add v10, v10, %s" % step, "  jmp ih",
              "next:", "  add v4, v4, %d" % s, "  add v30, v4, 1", "  jmp head",
              "exit:", "  ret v3"]
    return "\n".join(lines) + "\n", base


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--count", type=int, default=200)
    ap.add_argument("--seed", type=int, default=6601)
    ap.add_argument("--inputs", type=int, default=30)
    ap.add_argument("--bin", default=str(ROOT / "build/kopt-bin"))
    a = ap.parse_args()
    rng = random.Random(a.seed)
    machines = ["default", "slow_memory", "no_fused"]
    env = {k: v for k, v in os.environ.items() if not k.startswith("KOPT_")}
    applied = candidates = checks = 0
    with tempfile.TemporaryDirectory() as td:
        for i in range(a.count):
            text, base = program(rng)
            src = Path(td) / ("p%d.kir" % i)
            src.write_text(text)
            orig = K.compile_program(K.load_program(str(src)))
            dump = Path(td) / ("d%d" % i)
            dump.mkdir()
            machine = KIT / "machines" / ("machine_%s.cfg" % machines[i % len(machines)])
            p = subprocess.run([a.bin, str(src), "--machine", str(machine), "-o", str(dump / "out.kir")],
                               env=dict(env, KOPT_STRICT="1", KOPT_DUMP=str(dump)),
                               capture_output=True, text=True, timeout=120)
            if p.returncode != 0:
                raise AssertionError("kopt failed on program %d: %s\n%s" % (i, p.stderr[-500:], text))
            files = [f for f in dump.glob("cand*.kir") if f.read_text().startswith("; across")]
            if files:
                applied += 1
            files.append(dump / "out.kir")
            inputs = []
            for k in range(a.inputs):
                words = [rng.choice([0, 0, 0, 1, 2, rng.getrandbits(32)]) for _ in range(150)]
                lo = max(0, min(base, 4096 - 150))
                inputs.append(K.Inputs([rng.choice([rng.randrange(0, 200), rng.getrandbits(32)]), rng.getrandbits(32)],
                                       [(lo, words)], {}))
            for f in files:
                cand = K.compile_program(K.load_program(str(f)))
                candidates += 1
                for inp in inputs:
                    x = K.execute(orig, inp.args, inp.segments, inp.vin, 200000)
                    if x.status == "TIMEOUT":
                        continue
                    y = K.execute(cand, inp.args, inp.segments, inp.vin, 20 * x.steps + 1000)
                    diff = K.first_difference(x, y)
                    if diff:
                        raise AssertionError("%s differs on %s: %s\n%s" % (f.name, inp.args, diff, text))
                    checks += 1
    if applied < a.count // 10:
        raise AssertionError("across candidates on only %d of %d programs" % (applied, a.count))
    print("PASS pipeline across: %d programs (%d with across candidates), %d candidates, %d official comparisons"
          % (a.count, applied, candidates, checks))


if __name__ == "__main__":
    main()
