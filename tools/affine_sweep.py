#!/usr/bin/env python3
"""Paired complete-optimizer checks on generated CRC/XOR linear functions."""
import argparse
import json
from pathlib import Path
import random
import tempfile

import bench as B


def crc(rounds, seed, branch):
    rng = random.Random(seed)
    polynomial = rng.getrandbits(32) | 0x80000001
    lines = ["func generated(v0,v1)", "entry:", "and v2,v0,255", "and v3,v1,255",
             "shl v3,v3,8", "xor v2,v2,v3", f"xor v2,v2,{rng.getrandbits(32)}"]
    for i in range(rounds):
        lines += ["and v4,v2,1", "shr v5,v2,1"]
        if branch:
            lines += [f"br v4,yes{i},no{i}", f"yes{i}:", f"xor v2,v5,{polynomial}",
                      f"jmp join{i}", f"no{i}:", "mov v2,v5", f"jmp join{i}", f"join{i}:"]
        else:
            lines += [f"select v4,v4,{polynomial},0", "xor v2,v5,v4"]
    return "\n".join(lines + ["ret v2"]) + "\n"


def xorshift(rounds):
    lines = ["func generated(v0)", "entry:", "mov v2,v0"]
    for _ in range(rounds):
        lines += ["shl v3,v2,13", "xor v2,v2,v3", "shr v3,v2,17", "xor v2,v2,v3",
                  "shl v3,v2,5", "xor v2,v2,v3"]
    return "\n".join(lines + ["ret v2"]) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--baseline", required=True)
    ap.add_argument("--candidate", default=str(Path(B.ROOT) / "kopt"))
    ap.add_argument("--save", required=True)
    ap.add_argument("--seed", type=int, default=2020)
    ap.add_argument("--random", type=int, default=100)
    args = ap.parse_args()
    binaries = [str(Path(args.baseline).resolve()), str(Path(args.candidate).resolve())]
    cases = [(f"crc-branch-{n}", crc(n, args.seed + n, True), 2) for n in (8, 12, 20, 32)]
    cases += [(f"crc-select-{n}", crc(n, args.seed + n, False), 2) for n in (32, 64, 96)]
    cases += [(f"xorshift-{n}", xorshift(n), 1) for n in (4, 12, 24)]
    rows = []
    with tempfile.TemporaryDirectory(prefix="kopt-affine-sweep-") as tmp:
        for name, text, params in cases:
            src = Path(tmp) / (name + ".kir"); src.write_text(text)
            src.with_suffix(".in").write_text("args " + " ".join(["123456789", "987654321"][:params]) + "\n")
            for machine in ("default", "few_registers", "no_fused", "slow_memory", "wide_fast"):
                cfg = Path(B.KIT) / "machines" / f"machine_{machine}.cfg"
                results = []
                for binary in binaries:
                    B.KOPT = binary
                    result = B.check_one((name, str(src), str(cfg), args.random, False,
                                          False, 5.0, args.seed, 40))
                    if not result["ok"]:
                        raise AssertionError((name, machine, binary, result["err"]))
                    results.append(result)
                before, after = results
                row = {"case": name, "machine": machine, "before": before["c1"],
                       "after": after["c1"], "random_before": before["r1"],
                       "random_after": after["r1"], "seconds_before": before["kopt_s"],
                       "seconds_after": after["kopt_s"]}
                rows.append(row); print(json.dumps(row), flush=True)
    Path(args.save).write_text(json.dumps({"seed": args.seed, "rows": rows}, indent=2) + "\n")
    print("PASS %d generated paired program/machine checks" % len(rows))


if __name__ == "__main__":
    main()
