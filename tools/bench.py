#!/usr/bin/env python3
"""bench.py - score kopt on the starter kit, the same way the judges do.

For every (program, machine) pair it:
  1. runs kopt (or the identity transform, with --identity) under a time limit,
  2. checks the output is valid KIR for that machine,
  3. compares original and optimized behaviour on the sample input plus N
     generated inputs (the kit's own kirlib: result, volatile log, data memory),
  4. counts cycles on the sample input with the kit's exact timing model,
  5. runs kopt a second time and checks the output is byte-for-byte identical.

The kit is not part of this repository. Point KIT at its COMP10 folder:
  KIT=/path/to/COMP10 tools/bench.py [--machines all] [--random 30] [names...]
"""
import argparse
import glob
import math
import multiprocessing as mp
import os
import subprocess
import sys
import tempfile
import time

KIT = os.environ.get("KIT", os.path.join(os.path.dirname(__file__), "..", "..",
                                         "official-LLH-26", "Compilers", "COMP10"))
KIT = os.path.abspath(KIT)
sys.path.insert(0, KIT)
import kirlib as K  # noqa: E402  (the kit's reference implementation)

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
KOPT = os.path.join(ROOT, "kopt")


def run_kopt(src, machine, prof, out, identity, timeout):
    if identity:
        with open(src) as f, open(out, "w") as g:
            g.write(f.read())
        return 0.0, None
    cmd = [KOPT, src, "--machine", machine, "-o", out]
    if prof:
        cmd += ["--profile", prof]
    t0 = time.time()
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return time.time() - t0, "TIMEOUT"
    dt = time.time() - t0
    if p.returncode != 0:
        return dt, "exit %d: %s" % (p.returncode, p.stderr.strip()[-300:])
    if not os.path.exists(out):
        return dt, "no output file"
    return dt, None


def cycles_of(cp, inp, mc, max_steps):
    res = K.execute(cp, inp.args, inp.segments, inp.vin, max_steps, want_trace=True)
    if res.status == "TIMEOUT":
        return None, res
    return K.time_trace(cp, res.trace, mc), res


def check_one(job):
    name, src, machine, nrandom, identity, use_prof, timeout, seed = job
    mname = os.path.basename(machine).replace("machine_", "").replace(".cfg", "")
    prof = src[:-4] + ".prof"
    prof = prof if (use_prof and os.path.exists(prof)) else None
    row = {"name": name, "machine": mname, "ok": False, "err": None}
    mc = K.load_machine(machine)
    orig = K.load_program(src)
    cp0 = K.compile_program(orig)
    inpath = src[:-4] + ".in"
    sample = K.load_input(inpath, len(orig.params))
    with tempfile.TemporaryDirectory() as td:
        out = os.path.join(td, "out.kir")
        dt, err = run_kopt(src, machine, prof, out, identity, timeout)
        row["kopt_s"] = dt
        if err:
            row["err"] = err
            return row
        try:
            opt = K.load_program(out)
            K.check_machine_features(opt, mc)
        except K.KirError as e:
            row["err"] = "invalid output: %s" % e
            return row
        cp1 = K.compile_program(opt)
        inputs = [sample] + K.generate_inputs(len(orig.params), nrandom, seed)
        for i, inp in enumerate(inputs):
            a = K.execute(cp0, inp.args, inp.segments, inp.vin, 200000)
            if a.status == "TIMEOUT":
                continue
            b = K.execute(cp1, inp.args, inp.segments, inp.vin, 20 * a.steps + 1000)
            diff = K.first_difference(a, b)
            if diff:
                row["err"] = "MISMATCH input #%d: %s\n%s" % (i, diff, K.format_input(inp))
                return row
        c0, _ = cycles_of(cp0, sample, mc, 5000000)
        c1, _ = cycles_of(cp1, sample, mc, 5000000)
        row["c0"], row["c1"] = c0, c1
        # Held-out generated inputs (a seed kopt never sees): a less noisy
        # estimate than the single sample input.
        r0 = r1 = 0
        for inp in K.generate_inputs(len(orig.params), 8, seed + 7919):
            x0, _ = cycles_of(cp0, inp, mc, 2000000)
            x1, _ = cycles_of(cp1, inp, mc, 2000000)
            if x0 is None or x1 is None:
                continue
            r0 += x0
            r1 += x1
        row["r0"], row["r1"] = r0, r1
        row["n0"], row["n1"] = len(orig.instrs), len(opt.instrs)
        if not identity:
            out2 = os.path.join(td, "out2.kir")
            run_kopt(src, machine, prof, out2, identity, timeout)
            with open(out) as f, open(out2) as g:
                if f.read() != g.read():
                    row["err"] = "NONDETERMINISTIC output"
                    return row
    row["ok"] = True
    return row


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("names", nargs="*", help="program names (default: all of bench/)")
    ap.add_argument("--machines", default="default",
                    help="'all' or comma list: default,few_registers,no_fused,slow_memory,wide_fast")
    ap.add_argument("--random", type=int, default=30, help="generated inputs per check")
    ap.add_argument("--seed", type=int, default=12345)
    ap.add_argument("--identity", action="store_true", help="baseline: output = input")
    ap.add_argument("--no-profile", action="store_true")
    ap.add_argument("--timeout", type=float, default=10.0)
    ap.add_argument("--jobs", type=int, default=os.cpu_count())
    ap.add_argument("--dir", default=None, help="folder of .kir/.in files (default: kit bench/)")
    ap.add_argument("-v", "--verbose", action="store_true", help="print every row")
    ap.add_argument("--save", default=None, help="write per-program cycles to this JSON file")
    ap.add_argument("--compare", default=None, help="show differences against a saved JSON file")
    a = ap.parse_args()

    bench = a.dir or os.path.join(KIT, "bench")
    srcs = sorted(glob.glob(os.path.join(bench, "*.kir")))
    if a.names:
        srcs = [s for s in srcs if os.path.basename(s)[:-4] in a.names]
    mnames = ["default", "few_registers", "no_fused", "slow_memory", "wide_fast"] \
        if a.machines == "all" else a.machines.split(",")
    machines = [os.path.join(KIT, "machines", "machine_%s.cfg" % m) for m in mnames]
    jobs = [(os.path.basename(s)[:-4], s, m, a.random, a.identity, not a.no_profile,
             a.timeout, a.seed) for m in machines for s in srcs]
    t0 = time.time()
    with mp.Pool(a.jobs) as pool:
        rows = pool.map(check_one, jobs, chunksize=1)
    fails = [r for r in rows if not r["ok"]]
    good = [r for r in rows if r["ok"]]
    for r in rows:
        if a.verbose and r["ok"]:
            print("%-24s %-14s %8d -> %8d  x%5.2f  (%d -> %d instrs, %.2fs)" % (
                r["name"], r["machine"], r["c0"], r["c1"], r["c0"] / max(1, r["c1"]),
                r["n0"], r["n1"], r["kopt_s"]))
    for r in fails:
        print("FAIL %-24s %-14s %s" % (r["name"], r["machine"], r["err"]))
    by_m = {}
    for r in good:
        by_m.setdefault(r["machine"], []).append(r)
    print("\n%-14s %5s %12s %12s %8s %8s %12s %8s" % ("machine", "ok", "cycles_in", "cycles_out", "total_x", "geo_x",
                                                   "rand_out", "rgeo_x"))
    for m in mnames:
        rs = by_m.get(m, [])
        if not rs:
            continue
        s0 = sum(r["c0"] for r in rs)
        s1 = sum(r["c1"] for r in rs)
        geo = math.exp(sum(math.log(r["c0"] / max(1, r["c1"])) for r in rs) / len(rs))
        rsum = sum(r["r1"] for r in rs)
        rgeo = math.exp(sum(math.log(max(1, r["r0"]) / max(1, r["r1"])) for r in rs) / len(rs))
        print("%-14s %5d %12d %12d %8.3f %8.3f %12d %8.3f" % (m, len(rs), s0, s1, s0 / max(1, s1), geo, rsum, rgeo))
    if a.save:
        import json
        with open(a.save, "w") as f:
            json.dump({"%s|%s" % (r["name"], r["machine"]): r["c1"] for r in good}, f, indent=0, sort_keys=True)
    if a.compare:
        import json
        with open(a.compare) as f:
            old = json.load(f)
        diffs = []
        for r in good:
            k = "%s|%s" % (r["name"], r["machine"])
            if k in old and old[k] != r["c1"]:
                diffs.append((r["c1"] - old[k], k, old[k], r["c1"]))
        diffs.sort()
        print("\nbest improvements:")
        for d in diffs[:8]:
            print("  %-36s %7d -> %7d (%+d)" % (d[1], d[2], d[3], d[0]))
        print("worst regressions:")
        for d in diffs[::-1][:8]:
            if d[0] > 0:
                print("  %-36s %7d -> %7d (%+d)" % (d[1], d[2], d[3], d[0]))
    slow = max((r.get("kopt_s", 0) for r in rows), default=0)
    print("\n%d/%d passed, %d failed, slowest kopt %.2fs, wall %.1fs" % (
        len(good), len(rows), len(fails), slow, time.time() - t0))
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
