#!/usr/bin/env python3
"""Kit-free dense-live-set stress tests with a separate arithmetic oracle."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from smoke import BASE_MACHINE


def main():
    binary = str(ROOT / "build/kopt-bin")
    env = {k: v for k, v in os.environ.items() if not k.startswith("KOPT_")}
    env["KOPT_STRICT"] = "1"
    mask = (1 << 32) - 1
    with tempfile.TemporaryDirectory() as temp:
        td = Path(temp)
        cfg = td / "m.cfg"
        cfg.write_text("".join("%s = %s\n" % kv for kv in BASE_MACHINE.items()))
        for count in (900, 2000, 15000):
            lines = ["func pressure(v0)", "entry:"]
            for i in range(1, count + 1):
                lines.extend(["xor v%d, v0, %d" % (i, i), "mul v%d, v%d, v%d" % (i, i, i)])
            lines.append("const v990000, 0")
            for i in range(1, count + 1):
                lines.append("add v990000, v990000, v%d" % i)
            lines.append("ret v990000")
            src, out = td / "in.kir", td / "out.kir"
            src.write_text("\n".join(lines) + "\n")
            subprocess.run([binary, str(src), "--machine", str(cfg), "-o", str(out)],
                           env=env, check=True, capture_output=True, timeout=5 if count == 900 else 25)
            for x in (0, 37, 0x80000000, mask):
                inp = td / "input.in"
                inp.write_text("args %d\n" % x)
                expected = sum((x ^ i) * (x ^ i) for i in range(1, count + 1)) & mask
                p = subprocess.run([binary, "--sim", str(out), "--machine", str(cfg),
                                    "--input", str(inp)], env=env, check=True,
                                   capture_output=True, text=True, timeout=5)
                actual = p.stdout.split(" cycles=", 1)[0]
                if actual != "RET %d" % expected:
                    raise AssertionError((count, x, expected, actual))
            print("PASS dense pressure: %d values, %d instructions" % (count, len(lines) - 2))


if __name__ == "__main__":
    main()
