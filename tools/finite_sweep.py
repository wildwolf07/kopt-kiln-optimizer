#!/usr/bin/env python3
"""Compare complete optimizers on generated, finally-masked recurrences.

The inputs are generated here, independently of the kit corpus. Both versions
receive identical sources, inputs and machines. bench.check_one uses the kit's
independent interpreter and verifies complete behavior and repeat output.
"""
import argparse
import json
from pathlib import Path
import random
import tempfile

import bench as B


def recurrence(index, seed, wide=False):
    rng = random.Random(seed + index)
    if wide:
        mask = (1 << (7 + index % 4)) - 1
        field = (1 << (1 << (index % 4))) - 1
        lines = ["func generated(v0)", "entry:", f"and v2,v0,{mask}",
                 f"const v3,{5+index}", "jmp body", "body:",
                 f"mul v2,v2,{rng.randrange(1,1000)|1}",
                 f"add v2,v2,{rng.randrange(1000)}", "shr v4,v2,5",
                 "xor v2,v2,v4", f"and v2,v2,{mask}", "sub v3,v3,1",
                 "br v3,body,done", "done:", "shr v4,v2,3", "xor v2,v2,v4",
                 f"and v5,v2,{field}", "ret v5"]
        return "\n".join(lines) + "\n"
    mask = (1 << (1 + index % 6)) - 1
    lines = ["func generated(v0)", "entry:", "mov v2,v0", f"const v3,{7+index}",
             "jmp body", "body:", f"mul v2,v2,{rng.randrange(1,1000)|1}",
             f"add v2,v2,{rng.randrange(1000)}", "shl v4,v2,3", "xor v2,v2,v4",
             "sub v3,v3,1", "br v3,body,done", "done:", f"and v5,v2,{mask}", "ret v5"]
    return "\n".join(lines) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--baseline", required=True)
    ap.add_argument("--candidate", default=str(Path(B.ROOT) / "kopt"))
    ap.add_argument("--cases", type=int, default=12)
    ap.add_argument("--seed", type=int, default=1818)
    ap.add_argument("--random", type=int, default=100)
    ap.add_argument("--wide", action="store_true", help="generate 7-10-bit nonlinear domains")
    ap.add_argument("--save", required=True)
    args = ap.parse_args()
    if args.cases < 1 or args.random < 1:
        ap.error("cases and random must be positive")
    binaries = [str(Path(args.baseline).resolve()), str(Path(args.candidate).resolve())]
    rows = []
    with tempfile.TemporaryDirectory(prefix="kopt-finite-sweep-") as tmp:
        for i in range(args.cases):
            src = Path(tmp) / f"case{i}.kir"
            src.write_text(recurrence(i, args.seed, args.wide))
            src.with_suffix(".in").write_text("args 123456789\n")
            for machine in ("default", "few_registers", "no_fused", "slow_memory", "wide_fast"):
                cfg = Path(B.KIT) / "machines" / f"machine_{machine}.cfg"
                results = []
                for binary in binaries:
                    B.KOPT = binary
                    row = B.check_one((str(i), str(src), str(cfg), args.random, False,
                                       False, 5.0, args.seed + 100, 40))
                    if not row["ok"]:
                        raise AssertionError((i, machine, binary, row["err"]))
                    results.append(row)
                before, after = results
                row = {"case": i, "machine": machine, "before": before["c1"],
                       "after": after["c1"], "random_before": before["r1"],
                       "random_after": after["r1"]}
                rows.append(row)
                print(json.dumps(row), flush=True)
    Path(args.save).write_text(json.dumps({"seed": args.seed, "rows": rows}, indent=2) + "\n")
    print("PASS %d paired generated recurrence/machine checks" % len(rows))


if __name__ == "__main__":
    main()
