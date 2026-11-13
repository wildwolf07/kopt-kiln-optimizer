#!/usr/bin/env python3
"""Inject optimizer failure and verify machine-legal, deterministic fallback."""
import argparse
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--kit-free', action='store_true')
    args = parser.parse_args()
    binary = (ROOT / 'build/kopt-bin').resolve()
    sys.path.insert(0, str(ROOT / 'tools'))
    from smoke import BASE_MACHINE
    oracle = None
    if not args.kit_free:
        kit = Path(os.environ.get('KIT', ROOT.parent / 'official-LLH-26/Compilers/COMP10'))
        sys.path.insert(0, str(kit)); import kirlib as oracle
    env = {k: v for k, v in os.environ.items() if not k.startswith('KOPT_')}
    fixtures = [(p.stem, p.read_text()) for p in sorted((ROOT / 'tests/smoke').glob('*.kir'))]
    fixtures += [('high-register-aliases', 'func high(v999999, v765432)\nentry:\n'
                  ' mac v999999, v999999, v765432, v999999\n'
                  ' addsh v765432, v999999, v765432, 31\n store 17, v765432\n ret v999999\n')]
    checked = comparisons = 0
    with tempfile.TemporaryDirectory(prefix='kopt forced fallback ') as tmp:
        td = Path(tmp); bundle = td / 'bundle space'; (bundle / 'build').mkdir(parents=True)
        shutil.copy2(ROOT / 'kopt', bundle / 'kopt')
        fake = bundle / 'build/kopt-bin'
        fake.write_text('#!/bin/sh\nif [ "$1" = "--fallback" ]; then\n'
                        f' exec {shlex.quote(str(binary))} "$@"\nfi\nexit 77\n')
        fake.chmod(0o755)
        cfg = td / 'machine.cfg'; src = td / 'input file.kir'; out = td / 'only output.kir'
        for mac, addsh in ((0, 0), (0, 1), (1, 0), (1, 1)):
            cfg.write_text(''.join(f'{k} = {v}\n' for k, v in dict(
                BASE_MACHINE, fused_mac=mac, fused_addsh=addsh).items()))
            for name, text in fixtures:
                src.write_text(text)
                cmd = [str(bundle / 'kopt'), str(src), '--machine', str(cfg), '-o', str(out)]
                first = None
                for _ in range(2):
                    out.unlink(missing_ok=True)
                    before = set(td.rglob('*'))
                    run = subprocess.run(cmd, cwd=td, env=env, text=True, capture_output=True, timeout=30)
                    assert run.returncode == 0, (name, run.stderr)
                    assert 'machine-legal fallback' in run.stderr, run.stderr
                    assert set(td.rglob('*')) - before == {out}, 'unexpected written file'
                    data = out.read_bytes()
                    if first is not None: assert first == data, 'nondeterministic fallback'
                    first = data
                if not mac: assert not re.search(r'^\s*mac\s', out.read_text(), re.M)
                if not addsh: assert not re.search(r'^\s*addsh\s', out.read_text(), re.M)
                unsupported = (not mac and re.search(r'^\s*mac\s', text, re.M)) or (
                    not addsh and re.search(r'^\s*addsh\s', text, re.M))
                if not unsupported: assert first == src.read_bytes(), 'legal fallback changed the input'
                check = subprocess.run([str(binary), '--check', str(src), str(out), '--machine', str(cfg),
                                        '--random', '96'], env=env, text=True, capture_output=True, timeout=30)
                assert check.returncode == 0, (name, check.stdout, check.stderr)
                if oracle is not None:
                    original = oracle.compile_program(oracle.parse_program(text))
                    candidate = oracle.load_program(str(out))
                    oracle.check_machine_features(candidate, oracle.load_machine(str(cfg)))
                    optimized = oracle.compile_program(candidate)
                    for inp in oracle.generate_inputs(len(candidate.params), 96, 131126):
                        a = oracle.execute(original, inp.args, inp.segments, inp.vin, 100000)
                        b = oracle.execute(optimized, inp.args, inp.segments, inp.vin, 100000)
                        assert oracle.first_difference(a, b) is None, (name, inp.args)
                        comparisons += 1
                checked += 1
    print(f'PASS {checked} injected failures; fused gates, high names, effects, traps, determinism; '
          f'{comparisons} official comparisons')


if __name__ == '__main__':
    main()
