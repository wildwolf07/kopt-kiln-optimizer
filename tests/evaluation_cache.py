#!/usr/bin/env python3
"""The bounded exact-score cache must leave optimizer output unchanged."""
import argparse
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--kit-free', action='store_true')
    parser.add_argument('--bin', type=Path, default=ROOT / 'build/kopt-bin')
    args = parser.parse_args()
    import sys
    sys.path.insert(0, str(ROOT / 'tools'))
    from smoke import BASE_MACHINE
    fixtures = [(p.stem, p.read_text()) for p in sorted((ROOT / 'tests/smoke').glob('*.kir'))]
    fixtures += [('high-registers', 'func high(v999999, v765432)\nentry:\n'
                  ' mac v999999, v999999, v765432, v999999\n'
                  ' addsh v765432, v999999, v765432, 31\n ret v765432\n'),
                 ('no-parameters', 'func none()\nentry:\n store 17, 91\n ret 19\n')]
    large = ['func large(v0)', 'entry:']
    large += [f'add v{i}, v{i-1}, v0' for i in range(1, 4003)]
    large += ['ret v4002']
    fixtures.append(('large-cache-disabled', '\n'.join(large) + '\n'))
    clean = {k: v for k, v in os.environ.items() if not k.startswith('KOPT_')}
    hits = checked = 0
    with tempfile.TemporaryDirectory(prefix='kopt exact score ') as tmp:
        td = Path(tmp)
        cfg = td / 'machine.cfg'
        profile = td / 'wrong profile.prof'
        profile.write_text('edge entry impossible 999999999\nedge missing entry 1\n')
        for fused in (0, 1):
            machine = dict(BASE_MACHINE, fused_mac=fused, fused_addsh=fused)
            cfg.write_text(''.join(f'{k} = {v}\n' for k, v in machine.items()))
            for name, text in fixtures:
                src = td / (name + '.kir'); src.write_text(text)
                label = next(line.strip()[:-1] for line in text.splitlines() if line.strip().endswith(':'))
                # Existing labels make this an active but deliberately wrong
                # profile, rather than merely exercising the ignored case.
                profile.write_text(f'edge {label} {label} 1000000000\nedge missing nowhere 1\n')
                outputs = []
                for disabled in (False, True):
                    out = td / 'output.kir'
                    env = dict(clean, KOPT_STRICT='1', KOPT_VERBOSE='1')
                    if disabled: env['KOPT_DISABLE'] = 'evalcache'
                    cmd = [str(args.bin.resolve()), str(src), '--machine', str(cfg),
                           '--profile', str(profile), '-o', str(out)]
                    run = subprocess.run(cmd, env=env, cwd=td, capture_output=True, text=True, timeout=30)
                    assert run.returncode == 0, (name, fused, disabled, run.stderr[-2000:])
                    assert 'optimizer failed' not in run.stderr
                    outputs.append(out.read_bytes())
                    count = run.stderr.count('reused exact score')
                    if disabled or name == 'large-cache-disabled': assert count == 0
                    hits += count
                assert outputs[0] == outputs[1], (name, fused, 'cached selection changed')
                checked += 1
    assert hits > 0, 'cache was never exercised'
    print(f'PASS {checked} cached/uncached output pairs; {hits} exact-score hits; large-program bypass')


if __name__ == '__main__':
    main()
