#!/usr/bin/env python3
"""Check bit-demand masks directly against an independent interpreter."""
import os
from pathlib import Path
import random
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True
KIT_FREE = sys.argv[1:] == ["--kit-free"]
if not KIT_FREE:
    sys.path.insert(0, str(Path(os.environ.get("KIT", ROOT.parent / "official-LLH-26/Compilers/COMP10"))))
    import kirlib as K

DRIVER = r'''
#include <iostream>
#include <iterator>
#include "passes.h"
namespace kopt { bool finiteInputMasks(const Program &, std::vector<uint32_t> &); }
int main() {
    using namespace kopt;
    const std::string t((std::istreambuf_iterator<char>(std::cin)), {});
    Program p; std::string e;
    if (!parseProgram(t, p, e)) { std::cerr << e; return 2; }
    std::vector<uint32_t> masks{123456789};
    if (!finiteInputMasks(p, masks)) {
        if (masks != std::vector<uint32_t>{123456789}) return 3;
        std::cout << "reject\n"; return 0;
    }
    std::cout << "accept";
    for (uint32_t m : masks) std::cout << ' ' << m;
    std::cout << '\n';
}
'''


def program(body, params="v0, v1"):
    return f"func bits({params})\nentry:\n{body}\n"


def main():
    cases = [
        ("constant-mask-alias", program("const v5,63\nmov v6,v5\nand v2,v0,v6\nret v2"), [63, 0]),
        ("sparse-mask", program("and v2,v0,17\nret v2"), [17, 0]),
        ("high-bits", program("shr v2,v0,29\nand v3,v2,7\nret v3"), [0xe0000000, 0]),
        ("literal-or", program("or v2,v0,4294967232\nand v3,v2,63\nret v3"), [63, 0]),
        ("add-carry", program("add v2,v0,29\nand v3,v2,31\nret v3"), [31, 0]),
        ("sub-borrow", program("sub v2,3,v0\nand v3,v2,63\nret v3"), [63, 0]),
        ("multiply", program("mul v2,v0,v1\nand v3,v2,7\nret v3"), [7, 7]),
        ("mac", program("mac v2,v0,v1,v0\nand v3,v2,7\nret v3"), [7, 7]),
        ("addsh", program("addsh v2,v0,v1,2\nand v3,v2,15\nret v3"), [15, 3]),
        ("zero-shift-wrap", program("shl v2,v0,32\nand v3,v2,15\nret v3"), [15, 0]),
        ("amount-low-five", program("shr v2,4294967295,v0\nret v2"), [31, 0]),
        ("comparison-result-high-bits", program("lt v2,v0,v1\nand v3,v2,2\nret v3"), [0, 0]),
        ("comparison-needs-all", program("lt v2,v0,2\nret v2"), None),
        ("raw-branch", program("br v0,a,b\na:\nret 1\nb:\nret 1"), None),
        ("divisor-trap", program("div v2,v1,v0\nret 7"), None),
        ("dead-dividend", program("div v2,v0,1\nret 7"), [0, 0]),
        ("bounded-divisor", program("and v2,v1,3\ndiv v3,0,v2\nret 7"), [0, 3]),
        ("select-guard", program("and v2,v0,1\nand v3,v1,31\nselect v4,v2,v3,7\nret v4"), [1, 31]),
        ("load-rejected", program("load v2,0\nret v2"), None),
        ("volatile-rejected", program("vstore 0,0\nret 0"), None),
        ("explicit-trap-rejected", program("trap 7"), None),
        ("loop-demand-fixpoint", program("mov v2,v0\nconst v3,0\njmp loop\nloop:\nadd v2,v2,3\nadd v3,v3,1\nlt v4,v3,9\nbr v4,loop,done\ndone:\nand v5,v2,7\nret v5"), [7, 0]),
        ("branch-phi", program("and v2,v0,1\nbr v2,a,b\na:\nadd v3,v1,7\njmp done\nb:\nsub v3,v1,4\njmp done\ndone:\nand v4,v3,15\nret v4"), [1, 15]),
        ("uninitialized-zero", program("xor v2,v99,v0\nand v3,v2,63\nret v3"), [63, 0]),
        ("reject-seven-bits", program("and v2,v0,127\nret v2"), None),
    ]
    # Systematic transfer combinations compare masks against the full 32-bit
    # semantics. No optimizer selection or fallback can mask a wrong proof.
    for op in ("add", "sub", "mul", "xor", "or", "and"):
        for width in (1, 2, 3):
            mask = (1 << width) - 1
            body = f"{op} v2,v0,v1\nand v3,v2,{mask}\nret v3"
            cases.append((f"{op}-low-{width}", program(body), [mask, mask]))
    rng = random.Random(1817)
    edges = [0, 1, 31, 32, 63, 127, 4095, 0x7fffffff, 0x80000000, 0xffffffff]
    args = [(a, b) for a in edges for b in edges]
    args += [(rng.getrandbits(32), rng.getrandbits(32)) for _ in range(200)]
    checks = 0
    with tempfile.TemporaryDirectory() as tmp:
        source, binary = Path(tmp) / "driver.cpp", Path(tmp) / "driver"
        source.write_text(DRIVER)
        sources = [str(p) for p in sorted((ROOT / "src").glob("*.cpp"))
                   if p.name not in ("main.cpp", "optimizer.cpp")]
        subprocess.run([os.environ.get("CXX", "c++"), "-std=c++17", "-O1", "-Wall", "-Wextra",
                        "-Werror", "-pedantic", "-I" + str(ROOT / "src"), str(source),
                        *sources, "-o", str(binary)], check=True)
        for name, text, expected in cases:
            out = subprocess.run([str(binary)], input=text, text=True, capture_output=True, check=True)
            words = out.stdout.split()
            if expected is None:
                assert words == ["reject"], (name, words)
            else:
                assert words == ["accept"] + list(map(str, expected)), (name, words, expected)
                if not KIT_FREE:
                    compiled = K.compile_program(K.parse_program(text))
                    for pair in args:
                        masked = [a & m for a, m in zip(pair, expected)]
                        a = K.execute(compiled, list(pair), [], {}, 1000)
                        b = K.execute(compiled, masked, [], {}, 1000)
                        diff = K.first_difference(a, b)
                        assert not diff, (name, pair, masked, diff)
                        checks += 1
            print("PASS", name, flush=True)
    if KIT_FREE:
        print(f"PASS {len(cases)} direct bit-demand proof gates (kit-free)")
    else:
        print(f"PASS {checks} official mask-equivalence comparisons across {len(cases)} transfer/CFG cases")


if __name__ == "__main__":
    main()
