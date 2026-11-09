#!/usr/bin/env python3
"""Require and validate real unswitch+unroll4 candidates, including traps/I/O."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
KIT = Path(os.environ.get("KIT", ROOT.parent / "official-LLH-26/Compilers/COMP10"))
sys.path.insert(0, str(KIT))
import kirlib as K


def main():
    stem = ROOT / "tests/regress/unswitch_guarded_effects"
    orig = K.compile_program(K.load_program(str(stem.with_suffix(".kir"))))
    checks = 0
    with tempfile.TemporaryDirectory() as td:
        env = {k: v for k, v in os.environ.items() if not k.startswith("KOPT_")}
        env.update(KOPT_STRICT="1", KOPT_DUMP=td)
        subprocess.run([str(ROOT / "build/kopt-bin"), str(stem.with_suffix(".kir")),
                        "--machine", str(stem.with_suffix(".cfg")), "-o", td + "/out.kir"],
                       check=True, env=env, capture_output=True, text=True, timeout=30)
        candidates = [f for f in Path(td).glob("cand*.kir")
                      if any(tag in f.read_text().splitlines()[0] for tag in ("/unswitch4", "/unswitch+unroll4"))]
        if not candidates:
            raise AssertionError("no unswitch+unroll4 candidate exercised")
        for path in candidates:
            opt = K.compile_program(K.load_program(str(path)))
            for n in (0, 1, 3, 7, 17, 31):
                for flag in (0, 1, 37):
                    for divisor in (0, 7, 0xFFFFFFFF):
                        args = [n, flag, divisor]
                        a = K.execute(orig, args, [], {}, 20000)
                        b = K.execute(opt, args, [], {}, 20000)
                        diff = K.first_difference(a, b)
                        if diff:
                            raise AssertionError((path.name, args, diff))
                        checks += 1
    print("unswitch+unroll4: %d candidates, %d official comparisons passed" %
          (len(candidates), checks))


if __name__ == "__main__":
    main()
