#!/usr/bin/env python3
"""Paired official-interpreter evaluation on independently generated machines.

Uses bench.py's validity, complete behavior, cycle and determinism checks.
Generated hardware descriptions and held-out inputs never enter the optimizer
except through its normal command-line machine file. KIT remains external.
"""
import argparse
import json
import math
import multiprocessing as mp
from pathlib import Path
import random
import tempfile

import bench as B
from fuzz import rand_machine


def one(job):
    name, source, machine, baseline, candidate, seed, nrandom = job
    args = (name, source, machine, nrandom, False, True, 5.0, seed, 40)
    B.KOPT = baseline
    before = B.check_one(args)
    B.KOPT = candidate
    after = B.check_one(args)
    return {"program": name, "machine": Path(machine).stem,
            "before": before, "after": after}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--baseline", required=True)
    ap.add_argument("--candidate", default=str(Path(B.ROOT) / "kopt"))
    ap.add_argument("--machines", type=int, default=4)
    ap.add_argument("--seed", type=int, default=1513)
    ap.add_argument("--random", type=int, default=50)
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--save", required=True)
    ap.add_argument("names", nargs="*")
    a = ap.parse_args()
    if min(a.machines, a.random, a.jobs) < 1:
        ap.error("machines, random and jobs must be positive")
    baseline, candidate = str(Path(a.baseline).resolve()), str(Path(a.candidate).resolve())
    files = sorted((Path(B.KIT) / "bench").glob("*.kir"))
    if a.names:
        wanted = set(a.names)
        files = [p for p in files if p.stem in wanted]
        if wanted != {p.stem for p in files}:
            ap.error("unknown program name")
    if not files:
        ap.error("no kit programs found")
    rng = random.Random(a.seed)
    machines = []
    rows = []
    with tempfile.TemporaryDirectory(prefix="kopt-machines-") as tmp:
        jobs = []
        for i in range(a.machines):
            machine = rand_machine(rng)
            # Include intermediate and wider register files, not just the kit's
            # five configurations. All ranges respect KIR's machine format.
            machine["registers"] = rng.choice([4, 7, 9, 10, 20, 24, 32])
            machine["issue_width"] = rng.choice([1, 2, 3, 4, 6])
            machine["lat_alu"] = rng.choice([1, 2, 3])
            machines.append(machine)
            path = Path(tmp) / ("generated_%d.cfg" % i)
            path.write_text("".join("%s = %d\n" % kv for kv in machine.items()))
            for source in files:
                jobs.append((source.stem, str(source), str(path), baseline, candidate,
                             a.seed + 1009 * i, a.random))
        with mp.Pool(a.jobs) as pool:
            for row in pool.imap_unordered(one, jobs):
                rows.append(row)
                for version in ("before", "after"):
                    if not row[version]["ok"]:
                        print("FAIL", row["program"], row["machine"], version,
                              row[version]["err"], flush=True)
    rows.sort(key=lambda row: (row["machine"], row["program"]))
    valid = [r for r in rows if r["before"]["ok"] and r["after"]["ok"]]
    summary = []
    for i in range(a.machines):
        group = [r for r in valid if r["machine"] == "generated_%d" % i]
        def total(version, key):
            return sum(r[version][key] or 0 for r in group)
        ratios = [r["before"]["r1"] / r["after"]["r1"] for r in group
                  if r["before"]["r1"] and r["after"]["r1"]]
        report = {"machine": i, "pairs": len(group),
                  "sample_before": total("before", "c1"), "sample_after": total("after", "c1"),
                  "random_before": total("before", "r1"), "random_after": total("after", "r1"),
                  "random_geomean_candidate_speedup": math.exp(sum(map(math.log, ratios)) / len(ratios))
                  if ratios else None}
        summary.append(report)
        print(json.dumps(report), flush=True)
    Path(a.save).write_text(json.dumps({"seed": a.seed, "machines": machines,
                                      "summary": summary, "rows": rows}, indent=2) + "\n")
    print("%d/%d paired program/machine checks passed" % (len(valid), len(rows)))
    raise SystemExit(len(valid) != len(rows))


if __name__ == "__main__":
    main()
