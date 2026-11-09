#!/usr/bin/env python3
"""Direct signedPowerTwo tests using an independent oracle and the official kit.

Run: python3 tests/signed_pow2.py
     KIT=/path/to/COMP10 python3 tests/signed_pow2.py --count 6000
     python3 tests/signed_pow2.py --source-root ../kopt-next

The default checks 1,000 random dividends plus signed power-of-two boundaries
(about 316,000 DIV/MOD results). --count changes the random sample size; edge
cases always run. ROOT comes from this file's parent directory. --source-root
selects another compiler checkout without changing it. CXX selects the compiler.
The embedded driver calls the pass directly, so optimizer fallback cannot hide
an incorrect or missing rewrite. Builds and generated KIR live only in a temporary
directory. --sanitize enables AddressSanitizer and UndefinedBehaviorSanitizer.
"""

import argparse
import importlib
import os
from pathlib import Path
import random
import re
import shlex
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
MASK = (1 << 32) - 1
INT_MIN, INT_MAX = -(1 << 31), (1 << 31) - 1

DRIVER = r'''
#include "backend.h"
#include "passes.h"
#include <cstdlib>
#include <iostream>
#include <iterator>

// The pass needs no shared-header or optimizer call-site changes for this test.
namespace kopt { bool signedPowerTwo(Func &, const Machine &); }

int main(int argc, char **argv) {
    using namespace kopt;
    if (argc != 5) return 1;
    Machine m;
    m.lat_div = std::atoi(argv[1]);
    m.lat_alu = std::atoi(argv[2]);
    std::string text((std::istreambuf_iterator<char>(std::cin)), {}), err;
    Program p;
    Func f;
    if (!parseProgram(text, p, err) || !buildSSA(p, f, err)) {
        std::cerr << err; return 2;
    }
    err = verifyFunc(f);
    if (!err.empty()) { std::cerr << err; return 3; }
    const bool changed = signedPowerTwo(f, m);
    err = verifyFunc(f);
    if (!err.empty()) { std::cerr << err; return 4; }
    if (signedPowerTwo(f, m)) {
        std::cerr << "pass is not idempotent"; return 5;
    }
    std::cerr << "changed=" << changed << '\n';
    // Extreme cost arithmetic is tested without invoking unrelated backend
    // scheduling, whose critical-path heights use signed int arithmetic.
    if (std::string(argv[4]) == "pass-only") return 0;
    BackendOptions options;
    options.preSchedule = std::atoi(argv[3]) != 0;
    std::cout << printProgram(lowerToProgram(f, m, options));
}
'''


def signed(bits):
    bits &= MASK
    return bits - (1 << 32) if bits & (1 << 31) else bits


def oracle(x, divisor, op):
    """Correct Python's floor quotient toward zero, then derive the remainder.

    This deliberately does not use the absolute-magnitude shift/mask algorithm
    implemented by the compiler (or the kit's absolute-magnitude division).
    """
    quotient = x // divisor
    if (x < 0) != (divisor < 0) and x % divisor != 0:
        quotient += 1
    return (quotient if op == "div" else x - quotient * divisor) & MASK


def sample_values(divisors, count):
    edges = {0, 1, -1, INT_MIN, INT_MAX}
    for divisor in divisors:
        for center in (divisor, -divisor, 2 * divisor, -2 * divisor):
            for offset in (-2, -1, 0, 1, 2):
                value = center + offset
                if INT_MIN <= value <= INT_MAX:
                    edges.add(value)
    rng = random.Random(0x2752)
    return sorted(edges) + [signed(rng.getrandbits(32)) for _ in range(count)]


def all_operations(cases):
    lines = ["func all_signed(v0)", "entry:"]
    for index, (op, divisor) in enumerate(cases):
        lines += [f"  {op} v{index + 1}, v0, {divisor}",
                  f"  vstore {index}, v{index + 1}"]
    return "\n".join(lines + ["  ret 0"]) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--count", type=int, default=1000,
                        help="random dividends in addition to all edge cases (default: 1000)")
    parser.add_argument("--source-root", type=Path, default=ROOT,
                        help="compiler checkout to compile (default: this script's repository)")
    parser.add_argument("--sanitize", action="store_true", help="build driver with ASan/UBSan")
    args = parser.parse_args()
    if args.count < 0:
        parser.error("--count must be nonnegative")
    source_root = args.source_root.expanduser().resolve()
    if not (source_root / "src/pow2.cpp").is_file():
        parser.error(f"missing {source_root / 'src/pow2.cpp'}")
    kit = Path(os.environ.get("KIT", ROOT.parent / "official-LLH-26/Compilers/COMP10"))
    kit = kit.expanduser().resolve()
    if not (kit / "kirlib.py").is_file():
        parser.error(f"missing {kit / 'kirlib.py'}; set KIT to the COMP10 directory")
    sys.path.insert(0, str(kit))
    K = importlib.import_module("kirlib")

    divisors = [d for shift in range(1, 31) for d in (1 << shift, -(1 << shift))]
    divisors.append(INT_MIN)
    cases = [(op, divisor) for divisor in divisors for op in ("div", "mod")]
    values = sample_values(divisors, args.count)
    with tempfile.TemporaryDirectory(prefix="kopt-signed-pow2-") as temp:
        directory = Path(temp)
        driver = directory / "driver.cpp"
        binary = directory / "driver"
        driver.write_text(DRIVER)
        sources = sorted(str(path) for path in (source_root / "src").glob("*.cpp")
                         if path.name != "main.cpp")
        flags = ["-std=c++17", "-O1", "-Wall", "-Wextra", "-pedantic"]
        if args.sanitize:
            flags += ["-g", "-fsanitize=address,undefined", "-fno-omit-frame-pointer"]
        print(f"Compiling signedPowerTwo driver against {source_root}", flush=True)
        subprocess.run([*shlex.split(os.environ.get("CXX", "c++")), *flags,
                        "-I", str(source_root / "src"), str(driver), *sources,
                        "-o", str(binary)], check=True)
        environment = dict(os.environ)
        if args.sanitize:
            # A sanitizer diagnostic must fail the test, including during lower.
            environment["UBSAN_OPTIONS"] = "halt_on_error=1"
            environment["ASAN_OPTIONS"] = "halt_on_error=1"

        def lower(text, div=12, alu=1, pre=False, changed=True, pass_only=False):
            result = subprocess.run(
                [str(binary), str(div), str(alu), str(int(pre)),
                 "pass-only" if pass_only else "lower"],
                input=text, capture_output=True, text=True, check=True, env=environment)
            assert result.stderr == f"changed={int(changed)}\n", result.stderr
            return result.stdout

        def compile_text(text):
            return K.compile_program(K.parse_program(text))

        def execute(program, x, extra=()):
            return K.execute(program, [x & MASK, *extra], [], {}, 10000)

        def equivalent(expected, actual, context):
            difference = K.first_difference(expected, actual)
            assert not difference, (context, difference)

        source = all_operations(cases)
        original = compile_text(source)
        variants = []
        for pre in (False, True):
            lowered = lower(source, pre=pre)
            assert not re.search(r"^\s+(div|mod) ", lowered, re.MULTILINE), lowered
            variants.append(compile_text(lowered))
        comparisons = 0
        for x in values:
            reference = execute(original, x)
            expected_log = [("S", index, oracle(x, divisor, op))
                            for index, (op, divisor) in enumerate(cases)]
            assert reference.status == "RET" and reference.vlog == expected_log, x
            for pre, program in enumerate(variants):
                actual = execute(program, x)
                equivalent(reference, actual, (x, pre))
                assert actual.status == "RET" and actual.vlog == expected_log, (x, pre)
                comparisons += len(cases)
        print(f"PASS: {comparisons:,} signed DIV/MOD results against independent oracle "
              f"and official runtime ({len(values):,} dividends, 61 divisors, "
              "pre-scheduling off/on)", flush=True)

        for div, alu, expected in ((1, 1, False), (6, 1, False), (7, 1, True),
                                   (12, 2, False), (13, 2, True),
                                   (INT_MAX, INT_MAX, False)):
            lower(source, div, alu, changed=expected, pass_only=True)
        print("PASS: strict cost-gate boundaries and overflow-safe cost arithmetic", flush=True)

        # These must retain the original operations, including dynamic zero
        # traps and INT_MIN/-1 (the trivial simplifier owns +/-1).
        lines = ["func rejected(v0, v1)", "entry:"]
        index = 2
        for divisor in (1, -1, 3, -3, 6, -6, INT_MAX, -INT_MAX):
            for op in ("div", "mod"):
                lines += [f"  {op} v{index}, v0, {divisor}", f"  vstore {index}, v{index}"]
                index += 1
        lines += [f"  div v{index}, v0, v1", f"  vstore {index}, v{index}",
                  f"  mod v{index + 1}, -2147483648, -8", f"  ret v{index + 1}"]
        source = "\n".join(lines) + "\n"
        original, lowered = compile_text(source), compile_text(lower(source, changed=False))
        # Keep auxiliary tests bounded when --count requests a large sample.
        probes = sorted(set([INT_MIN, INT_MAX, -1, 0, 1, *values[:100], *values[-100:]]))
        skipped = 0
        for x in probes:
            for y in (0, 1, -1, 2, -2, INT_MIN, 3):
                equivalent(execute(original, x, [y & MASK]),
                           execute(lowered, x, [y & MASK]), ("rejected", x, y))
                skipped += 1
        print(f"PASS: {skipped:,} rejected-case executions including dynamic zero traps", flush=True)

        for op in ("div", "mod"):
            source = ("func trap(v0)\nentry:\n  vstore 0, 11\n"
                      f"  {op} v1, v0, 0\n  vstore 0, 22\n  ret v1\n")
            original, lowered = compile_text(source), compile_text(lower(source, changed=False))
            for x in (INT_MIN, -1, 0, 1, INT_MAX):
                actual = execute(lowered, x)
                equivalent(execute(original, x), actual, ("zero", op, x))
                assert actual.status == "TRAP" and actual.value == "div_by_zero", (op, x)
                assert actual.vlog == [("S", 0, 11)], (op, x)

        source = """func chained(v0)
entry:
  div v1, v0, -8
  mod v2, v1, -2147483648
  br v2, yes, no
yes:
  mod v3, v2, 16
  ret v3
no:
  div v4, v1, 2
  ret v4
"""
        original, lowered = compile_text(source), compile_text(lower(source, pre=True))
        for x in values:
            equivalent(execute(original, x), execute(lowered, x), ("CFG", x))
        print("PASS: zero-trap effect order, dependent CFG replacements, "
              "SSA verification and idempotence", flush=True)


if __name__ == "__main__":
    main()
