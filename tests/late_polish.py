#!/usr/bin/env python3
"""Paired strict sample/held-out scoring; direct binaries, no fallback wrapper."""
from pathlib import Path
import argparse
import json
import math
import multiprocessing as mp
import os
import statistics
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
KIT = Path(os.environ.get("KIT", ROOT.parent / "official-LLH-26/Compilers/COMP10"))
sys.dont_write_bytecode = True
sys.path.insert(0, str(KIT))
import kirlib as K


def pair(job):
    name, machine, before, after, random_count, timeout = job
    row = dict(name=name, machine=machine)
    try:
        cfg = KIT / "machines" / f"machine_{machine}.cfg"
        src = KIT / "bench" / (name + ".kir")
        mc = K.load_machine(str(cfg)); p = K.load_program(str(src)); cp = K.compile_program(p)
        sample = K.load_input(str(src.with_suffix(".in")), len(p.params))
        inputs = [sample] + K.generate_inputs(len(p.params), random_count, 12345)
        held_start = len(inputs)
        inputs += K.generate_inputs(len(p.params), 48, 12345 + 7919)[40:]
        references = [K.execute(cp, inp.args, inp.segments, inp.vin,
                                5000000 if i == 0 else 200000)
                      for i, inp in enumerate(inputs)]
        env = {k: v for k, v in os.environ.items() if not k.startswith("KOPT_")}
        env["KOPT_STRICT"] = "1"
        with tempfile.TemporaryDirectory() as tmp:
            td = Path(tmp)
            for label, binary in (("before", before), ("after", after)):
                out = td / (label + ".kir")
                cmd = [binary, str(src), "--machine", str(cfg), "-o", str(out)]
                profile = src.with_suffix(".prof")
                if profile.exists(): cmd += ["--profile", str(profile)]
                start = time.monotonic()
                process = subprocess.run(cmd, env=env, text=True, capture_output=True, timeout=timeout)
                elapsed = time.monotonic() - start
                if process.returncode: raise AssertionError((label, process.returncode, process.stderr[-1500:]))
                text = out.read_text(); program = K.load_program(str(out)); K.check_machine_features(program, mc)
                optimized = K.compile_program(program)
                cycles, held, checks = None, 0, 0
                for i, (inp, expected) in enumerate(zip(inputs, references)):
                    if expected.status == "TIMEOUT": continue
                    score = i == 0 or i >= held_start
                    actual = K.execute(optimized, inp.args, inp.segments, inp.vin,
                                       20 * expected.steps + 1000, want_trace=score)
                    diff = K.first_difference(expected, actual)
                    if diff: raise AssertionError((label, i, diff, K.format_input(inp)))
                    checks += 1
                    if score:
                        cost = K.time_trace(optimized, actual.trace, mc)
                        if i == 0: cycles = cost
                        else: held += cost
                again = subprocess.run(cmd, env=env, text=True, capture_output=True, timeout=timeout)
                if again.returncode or out.read_text() != text:
                    raise AssertionError((label, "nondeterministic/repeat failure", again.stderr[-1000:]))
                row[label] = dict(sample=cycles, heldout=held, seconds=elapsed,
                                  instructions=len(program.instrs), checks=checks)
            row["ok"] = True
    except Exception as error:
        row["ok"] = False; row["error"] = repr(error)
    return row


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--before", required=True)
    parser.add_argument("--after", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--random", type=int, default=100)
    parser.add_argument("--timeout", type=float, default=10)
    a = parser.parse_args()
    machines = ("default", "few_registers", "no_fused", "slow_memory", "wide_fast")
    names = sorted(p.stem for p in (KIT / "bench").glob("*.kir"))
    jobs = [(name, machine, str(Path(a.before).resolve()), str(Path(a.after).resolve()), a.random, a.timeout)
            for machine in machines for name in names]
    start = time.monotonic(); rows = []
    with mp.Pool(a.jobs) as pool:
        for row in pool.imap_unordered(pair, jobs):
            rows.append(row)
            if not row["ok"]: print("FAIL", row, flush=True)
            elif row["after"]["sample"] != row["before"]["sample"] or row["after"]["heldout"] != row["before"]["heldout"]:
                print("CHANGE", row, flush=True)
            if len(rows) % 50 == 0: print("PROGRESS", len(rows), "/", len(jobs), flush=True)
    summary = {}
    for machine in machines:
        subset = [r for r in rows if r["ok"] and r["machine"] == machine]
        if not subset: continue
        data = {}
        for metric in ("sample", "heldout"):
            changes = [r["after"][metric] - r["before"][metric] for r in subset]
            data[metric] = dict(before=sum(r["before"][metric] for r in subset),
                                after=sum(r["after"][metric] for r in subset),
                                faster=sum(d < 0 for d in changes), ties=sum(d == 0 for d in changes),
                                slower=sum(d > 0 for d in changes),
                                geometric_speedup=math.exp(sum(math.log(max(1, r["before"][metric]) /
                                    max(1, r["after"][metric])) for r in subset) / len(subset)))
        for label in ("before", "after"):
            secs = [r[label]["seconds"] for r in subset]
            data[label + "_seconds"] = dict(max=max(secs), median=statistics.median(secs), total=sum(secs))
        summary[machine] = data
    result = dict(rows=sorted(rows, key=lambda r: (r["machine"], r["name"])), summary=summary,
                  elapsed_seconds=time.monotonic() - start, random_inputs=a.random, heldout_offset=40,
                  jobs=a.jobs, failures=sum(not r["ok"] for r in rows))
    Path(a.output).write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "rows"}, indent=2), flush=True)
    assert len(rows) == 500 and result["failures"] == 0


if __name__ == "__main__":
    main()
