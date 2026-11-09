#!/usr/bin/env python3
"""Check renamed, reordered and literal-mutated programs against the kit.

KIT must point to the external COMP10 kit. Nothing from its corpus is copied
into the repository unless a failure is saved as a regression reproducer.
"""
import argparse
import multiprocessing as mp
import os
from pathlib import Path
import random
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
KIT = Path(os.environ.get("KIT", ROOT.parent / "official-LLH-26/Compilers/COMP10"))
sys.path.insert(0, str(KIT))
import kirlib as K
from fuzz import rand_machine, write_machine


def transform(source, rng, mutate):
    lines = [line.split(";", 1)[0].strip() for line in source.splitlines()]
    lines = [line for line in lines if line]
    regs = sorted(set(re.findall(r"\bv\d+\b", "\n".join(lines))))
    numbers = rng.sample(range(100, 999999), len(regs))
    mapping = dict(zip(regs, ("v%d" % n for n in numbers)))
    labels = [line[:-1] for line in lines if line.endswith(":" )]
    labelmap = {label: "block_%d" % i for i, label in enumerate(rng.sample(labels, len(labels)))}
    blocks = []
    header = None
    for line in lines:
        if line.startswith("func "):
            header = re.sub(r"func\s+\w+", "func renamed", line)
            header = re.sub(r"\bv\d+\b", lambda m: mapping[m[0]], header)
            continue
        line = re.sub(r"\b[A-Za-z_]\w*\b", lambda m: labelmap.get(m[0], mapping.get(m[0], m[0])), line)
        if line.endswith(":" ):
            blocks.append([line])
        else:
            if mutate and rng.random() < 0.3:
                op, *args = re.split(r"[\s,]+", line)
                for i, arg in enumerate(args):
                    if re.fullmatch(r"-?(?:0x[\da-fA-F]+|\d+)", arg) and rng.random() < 0.3:
                        args[i] = str(rng.randrange(32) if op == "addsh" and i == 3 else
                                      rng.choice([0, 1, 2, 3, 7, 15, 31, 63, 255, 3071, 3072,
                                                  4095, 4096, -1, -2147483648, 2147483647]))
                line = op + " " + ", ".join(args)
            blocks[-1].append("  " + line)
    rest = blocks[1:]
    rng.shuffle(rest)
    return header + "\n" + "\n".join(line for b in [blocks[0]] + rest for line in b) + "\n"


def one(job):
    index, seed, inputs, files = job
    rng = random.Random(seed * 1000003 + index)
    source = Path(files[index % len(files)])
    text = transform(source.read_text(), rng, index % 2 == 1)
    mc = rand_machine(rng)
    with tempfile.TemporaryDirectory() as temp:
        td = Path(temp)
        src, cfg, out, again = (td / name for name in ("in.kir", "m.cfg", "out.kir", "again.kir"))
        src.write_text(text)
        write_machine(cfg, mc)
        reason = None
        try:
            orig = K.parse_program(text)
            env = dict(os.environ, KOPT_STRICT="1")
            cmd = [str(ROOT / "build/kopt-bin"), str(src), "--machine", str(cfg), "-o"]
            for dest in (out, again):
                p = subprocess.run(cmd + [str(dest)], env=env, capture_output=True, text=True, timeout=10)
                if p.returncode:
                    raise AssertionError("exit %d: %s" % (p.returncode, p.stderr[-500:]))
            if out.read_bytes() != again.read_bytes():
                raise AssertionError("nondeterministic output")
            opt = K.load_program(out)
            K.check_machine_features(opt, mc)
            before, after = K.compile_program(orig), K.compile_program(opt)
            cases = K.generate_inputs(len(orig.params), inputs, seed * 7919 + index)
            sample = source.with_suffix(".in")
            if sample.exists():
                cases.insert(0, K.load_input(str(sample), len(orig.params)))
            for inp in cases:
                a = K.execute(before, inp.args, inp.segments, inp.vin, 20000)
                if a.status == "TIMEOUT":
                    continue
                b = K.execute(after, inp.args, inp.segments, inp.vin, 20 * a.steps + 1000)
                diff = K.first_difference(a, b)
                if diff:
                    raise AssertionError(diff + "\n" + K.format_input(inp))
        except (AssertionError, K.KirError, subprocess.TimeoutExpired) as e:
            reason = str(e)
        if reason:
            base = ROOT / "tests/fuzz_failures" / ("m%d_%d" % (seed, index))
            base.parent.mkdir(parents=True, exist_ok=True)
            base.with_suffix(".kir").write_text(text)
            write_machine(base.with_suffix(".cfg"), mc)
            base.with_suffix(".txt").write_text(str(source) + "\n" + reason + "\n")
            return "%s: %s" % (base.name, reason.splitlines()[0])
    return None


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--count", type=int, default=300)
    ap.add_argument("--seed", type=int, default=1109)
    ap.add_argument("--inputs", type=int, default=40)
    ap.add_argument("--jobs", type=int, default=4)
    args = ap.parse_args()
    files = sorted(str(p) for p in (KIT / "bench").glob("*.kir"))
    if not files or args.count < 1:
        ap.error("requires kit programs and a positive count")
    jobs = [(i, args.seed, args.inputs, files) for i in range(args.count)]
    with mp.Pool(args.jobs) as pool:
        failures = [r for r in pool.imap_unordered(one, jobs) if r]
    for failure in failures:
        print(failure)
    print("%d/%d metamorphic programs failed" % (len(failures), args.count))
    sys.exit(bool(failures))
