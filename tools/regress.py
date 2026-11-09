#!/usr/bin/env python3
"""regress.py - run kopt (strict self-check) on every tests/regress/NAME.kir with
NAME.cfg, and compare the output with the input on many inputs using the kit's
reference interpreter. Each file is a past bug: it must never come back.

  KIT=/path/to/COMP10 tools/regress.py
"""
import glob
import os
import subprocess
import sys
import tempfile

KIT = os.environ.get("KIT", os.path.join(os.path.dirname(__file__), "..", "..",
                                         "official-LLH-26", "Compilers", "COMP10"))
sys.path.insert(0, os.path.abspath(KIT))
import kirlib as K  # noqa: E402

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
bad = 0
files = sorted(glob.glob(os.path.join(ROOT, "tests", "regress", "*.kir")))
for f in files:
    cfg = f[:-4] + ".cfg"
    mc = K.load_machine(cfg)
    with tempfile.TemporaryDirectory() as td:
        out = os.path.join(td, "out.kir")
        p = subprocess.run([os.path.join(ROOT, "build", "kopt-bin"), f, "--machine", cfg, "-o", out],
                           capture_output=True, text=True, env=dict(os.environ, KOPT_STRICT="1"))
        if p.returncode != 0:
            print("FAIL %s: %s" % (os.path.basename(f), p.stderr.strip()[-200:]))
            bad += 1
            continue
        orig, opt = K.load_program(f), K.load_program(out)
        K.check_machine_features(opt, mc)
        c0, c1 = K.compile_program(orig), K.compile_program(opt)
        for inp in K.generate_inputs(len(orig.params), 400, 99):
            a = K.execute(c0, inp.args, inp.segments, inp.vin, 50000)
            if a.status == "TIMEOUT":
                continue
            b = K.execute(c1, inp.args, inp.segments, inp.vin, 20 * a.steps + 1000)
            d = K.first_difference(a, b)
            if d:
                print("MISMATCH %s: %s" % (os.path.basename(f), d))
                bad += 1
                break
print("%d/%d regression tests failed" % (bad, len(files)))
sys.exit(1 if bad else 0)
