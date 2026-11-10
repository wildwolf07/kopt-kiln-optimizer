#!/usr/bin/env python3
"""Paired independent sorting kernels with varied bases, strides and ordering."""
import argparse
import json
import os
from pathlib import Path
import random
import tempfile

import bench as B


def source(index):
    base, step = (index % 4) * 17, 1 + (index // 4) % 2
    compare = "lt v10,v9,v7" if index % 2 else "lt v10,v7,v9"
    return f"""func generated(v0)
entry:
  and v1,v0,15
  const v2,0
  jmp outer
outer:
  lt v3,v2,v1
  br v3,start,done
start:
  sub v4,v1,1
  sub v4,v4,v2
  mul v4,v4,{step}
  add v4,v4,{base}
  const v5,{base}
  jmp head
head:
  lt v6,v5,v4
  br v6,body,next
body:
  load v7,v5
  add v8,v5,{step}
  load v9,v8
  {compare}
  br v10,swap,advance
swap:
  store v5,v9
  store v8,v7
  jmp advance
advance:
  add v5,v5,{step}
  jmp head
next:
  add v2,v2,1
  jmp outer
done:
  ret v1
"""


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--baseline", required=True)
    ap.add_argument("--candidate", default=str(Path(B.ROOT) / "kopt"))
    ap.add_argument("--cases", type=int, default=8)
    ap.add_argument("--seed", type=int, default=2215)
    ap.add_argument("--save", required=True)
    a = ap.parse_args()
    if a.cases < 1:
        ap.error("cases must be positive")
    rng, rows = random.Random(a.seed), []
    binaries = [str(Path(p).resolve()) for p in (a.baseline, a.candidate)]
    os.environ["KOPT_STRICT"] = "1"
    with tempfile.TemporaryDirectory(prefix="rolling-sweep-") as temp:
        for i in range(a.cases):
            p = Path(temp) / f"generated{i}.kir"
            p.write_text(source(i))
            inp = B.K.Inputs([13], [(0, [rng.getrandbits(32) for _ in range(256)])], {})
            p.with_suffix(".in").write_text(B.K.format_input(inp))
            for machine in ("default", "few_registers", "no_fused", "slow_memory", "wide_fast"):
                cfg = Path(B.KIT) / "machines" / f"machine_{machine}.cfg"
                pair = []
                for binary in binaries:
                    B.KOPT = binary
                    row = B.check_one((p.stem, str(p), str(cfg), 100, False, False, 180, a.seed + 1, 40))
                    assert row["ok"], (i, machine, binary, row)
                    pair.append(row)
                row = dict(case=i, machine=machine, before=pair[0], after=pair[1])
                rows.append(row)
                print(i, machine, pair[0]["r1"], "->", pair[1]["r1"], flush=True)
    Path(a.save).write_text(json.dumps(dict(seed=a.seed, rows=rows), indent=2) + "\n")
    print(f"PASS {len(rows)} generated pairs: full behavior, features and determinism")


if __name__ == "__main__":
    main()
