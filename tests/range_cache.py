#!/usr/bin/env python3
"""Poison range caches, build a fresh SSA function, check trap ordering."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
ROOT = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True
KIT_FREE = sys.argv[1:] == ["--kit-free"]
if not KIT_FREE:
    sys.path.insert(0, str(Path(os.environ.get("KIT", ROOT.parent / "official-LLH-26/Compilers/COMP10"))))
    import kirlib as K
DRIVER = r'''#include <iostream>
#include "backend.h"
#include "passes.h"
using namespace kopt;
int main(int argc, char **argv) {
    if (argc != 2) return 2;
    const std::string safe = "func safe(v0)\nentry:\nand v1, v0, 7\nload v2, v1\nvload v3, 0\nret v2\n";
    const std::string raw = "func raw(v0)\nentry:\nmul v1, v0, 4096\nload v2, v1\nvload v3, 0\nret v2\n";
    Program p; Func f; std::string error;
    if (!parseProgram(safe, p, error) || !buildSSA(p, f, error)) return 3;
    computeIVRanges(f); computeVRP(f);
    const auto good = memoryFacts(f);
    if (good.size() != 1 || good[0].safe.size() != 1 || !good[0].safe[0]) return 4;
    if (!parseProgram(raw, p, error) || !buildSSA(p, f, error)) return 5;
    const auto unknown = memoryFacts(f);
    if (unknown.size() != 1 || unknown[0].safe.size() != 1 || unknown[0].safe[0]) {
        std::cerr << "fresh function inherited a safe-address proof"; return 6;
    }
    Machine m; BackendOptions o; o.preSchedule = true;
    o.pressureSchedule = std::string(argv[1]) == "pressure";
    o.bottomUpSchedule = std::string(argv[1]) == "bottomup";
    std::cout << printProgram(lowerToProgram(f, m, o));
}
'''
def main():
    raw = "func raw(v0)\nentry:\nmul v1, v0, 4096\nload v2, v1\nvload v3, 0\nret v2\n"
    before = None if KIT_FREE else K.compile_program(K.parse_program(raw))
    checks = 0
    with tempfile.TemporaryDirectory() as tmp:
        source, binary = Path(tmp) / "driver.cpp", Path(tmp) / "driver"
        source.write_text(DRIVER)
        sources = [str(p) for p in sorted((ROOT / "src").glob("*.cpp"))
                   if p.name not in ("main.cpp", "optimizer.cpp")]
        subprocess.run([os.environ.get("CXX", "c++"), "-std=c++17", "-O1", "-Wall", "-Wextra",
                        "-Werror", "-pedantic", "-I" + str(ROOT / "src"), str(source), *sources,
                        "-o", str(binary)], check=True)
        for mode in ("forward", "pressure", "bottomup"):
            out = subprocess.run([str(binary), mode], capture_output=True, text=True, check=True)
            if KIT_FREE:
                continue
            after = K.compile_program(K.parse_program(out.stdout))
            for x in (0, 1, 2, 7, 31, 32, 4095, 0x7fffffff, 0x80000000, 0xffffffff):
                for vin in ({}, {0: [17]}):
                    a = K.execute(before, [x], [(0, [73])], vin, 100)
                    b = K.execute(after, [x], [(0, [73])], vin, 100)
                    assert not K.first_difference(a, b), (mode, x, vin, K.first_difference(a, b))
                    checks += 1
    if KIT_FREE:
        print("PASS fresh-SSA signed/unsigned cache isolation (kit-free proof checks)")
    else:
        print(f"PASS fresh-SSA signed/unsigned cache isolation and {checks} official trap-order comparisons")
if __name__ == "__main__":
    main()
