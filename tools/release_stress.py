#!/usr/bin/env python3
"""Time deterministic 100k-instruction cases and check them with the official oracle."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import random
import resource
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bin', type=Path, default=ROOT / 'build/kopt-bin')
    parser.add_argument('--before', type=Path)
    parser.add_argument('--output', type=Path, default=ROOT / 'build/release-stress.json')
    parser.add_argument('--timeout', type=float, default=30)
    args = parser.parse_args()
    kit = Path(os.environ.get('KIT', ROOT.parent / 'official-LLH-26/Compilers/COMP10'))
    sys.path.insert(0, str(kit)); import kirlib as K
    import genbig
    binary = args.bin.resolve()
    work = args.output.resolve().parent / 'release-stress-inputs'; work.mkdir(parents=True, exist_ok=True)
    machine = kit / 'machines/machine_default.cfg'
    env = {k: v for k, v in os.environ.items() if not k.startswith('KOPT_')}
    env['KOPT_STRICT'] = '1'
    rows = []
    for name, generate in (('straight', genbig.straight), ('loops', genbig.loops)):
        src, out = work / (name + '.kir'), work / (name + '-out.kir')
        # The loop generator's size argument is an approximate work count;
        # request a margin so both measured programs contain at least 100k.
        requested = 100000 if name == 'straight' else 115000
        src.write_text(generate(requested, random.Random(42)))
        cmd = [str(binary), str(src), '--machine', str(machine), '-o', str(out)]
        before = resource.getrusage(resource.RUSAGE_CHILDREN)
        start = time.monotonic()
        process = subprocess.run(cmd, capture_output=True, text=True, env=env, timeout=args.timeout)
        elapsed = time.monotonic() - start
        after = resource.getrusage(resource.RUSAGE_CHILDREN)
        assert process.returncode == 0, (name, process.returncode, process.stderr[-2000:])
        expected_bytes = out.read_bytes()
        start = time.monotonic()
        repeat = subprocess.run(cmd, capture_output=True, text=True, env=env, timeout=args.timeout)
        repeated = time.monotonic() - start
        assert repeat.returncode == 0 and out.read_bytes() == expected_bytes, (name, 'repeat differs')
        a = K.load_program(str(src)); b = K.load_program(str(out))
        assert len(a.instrs) >= 100000, (name, 'stress case is too small')
        K.check_machine_features(b, K.load_machine(str(machine)))
        original, optimized = K.compile_program(a), K.compile_program(b)
        trials = ((0, 0, 0, 0), (1, 0xffffffff, 0x80000000, 0x7fffffff),
                  (0xffffffff, 0x80000000, 17, 0))
        words = [(i * 2654435761) & 0xffffffff for i in range(1024)]
        for argv in trials:
            x = K.execute(original, list(argv), [(0, words)], {}, 6000000)
            y = K.execute(optimized, list(argv), [(0, words)], {}, 6000000)
            assert x.status != 'TIMEOUT' and y.status != 'TIMEOUT', (name, 'oracle timeout')
            assert K.first_difference(x, y) is None, (name, argv, K.first_difference(x, y))
        row = dict(name=name, input_instructions=len(a.instrs), output_instructions=len(b.instrs),
                   input_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),
                   wall_seconds=elapsed, repeat_wall_seconds=repeated,
                   cpu_seconds=after.ru_utime + after.ru_stime - before.ru_utime - before.ru_stime,
                   official_comparisons=len(trials), deterministic=True,
                   output_sha256=hashlib.sha256(expected_bytes).hexdigest())
        if args.before:
            prior = work / (name + '-before.kir')
            old = subprocess.run([str(args.before.resolve()), str(src), '--machine', str(machine), '-o', str(prior)],
                                 env=env, capture_output=True, text=True, timeout=args.timeout)
            assert old.returncode == 0, old.stderr
            row['identical_to_baseline'] = prior.read_bytes() == expected_bytes
        rows.append(row)
        print(json.dumps(row), flush=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    result = dict(binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(), rows=rows)
    args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
