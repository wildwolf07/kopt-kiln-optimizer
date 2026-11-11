#!/usr/bin/env python3
"""Direct packed-counter proof checks using the official interpreter."""
import os
from pathlib import Path
import random
import shlex
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
KIT = Path(os.environ.get("KIT", ROOT.parent / "official-LLH-26/Compilers/COMP10"))
sys.path.insert(0, str(KIT))
import kirlib as K

DRIVER = r'''
#include <fstream>
#include <iostream>
#include <iterator>
#include "backend.h"
#include "passes.h"
using namespace kopt;

int main(int argc, char **argv) {
    if (argc != 3) return 2;
    std::ifstream machineFile(argv[1]);
    const std::string cfg((std::istreambuf_iterator<char>(machineFile)), {});
    const std::string text((std::istreambuf_iterator<char>(std::cin)), {});
    std::string err;
    Machine m;
    Program p;
    Func f;
    if (!parseMachine(cfg, m, err) || !parseProgram(text, p, err) || !buildSSA(p, f, err)) {
        std::cerr << err << '\n';
        return 3;
    }
    instSimplify(f); gvn(f); dce(f); simplifyCFG(f);
    const bool changed = packIndexedCounts(f);
    if (changed != (std::string(argv[2]) == "accept")) {
        std::cerr << "unexpected match: " << changed << '\n';
        return 4;
    }
    err = verifyFunc(f);
    if (!err.empty()) {
        std::cerr << err << '\n';
        return 5;
    }
    BackendOptions options;
    options.preSchedule = true;
    std::cout << printProgram(lowerToProgram(f, m, options));
}
'''


def kernel(mask=7, cap=63, input_base=10, bin_base=400, step=1,
           increment=1, extra="", count_use=False, alternate=False,
           finish="load v13,400\n  ret v13"):
    entry = "br v1,alternate,start\nalternate:\n  mov v15,42\n  jmp done\nstart:" if alternate else ""
    if alternate:
        finish = "ret v15"
    returned_count = "mov v15,v11" if count_use else "mov v15,v3"
    if count_use:
        finish = "ret v15"
    return f"""func counters(v0,v1)
entry:
  {entry}
  and v2,v0,{cap}
  const v3,0
  const v15,0
  jmp head
head:
  lt v4,v3,v2
  br v4,body,done
body:
  add v5,v3,{input_base}
  load v6,v5
  and v7,v6,{mask}
  add v8,v7,{bin_base}
  load v10,v8
  add v11,v10,{increment}
  store v8,v11
  {extra}
  add v3,v3,{step}
  {returned_count}
  jmp head
done:
  {finish}
"""


def main():
    cases = [
        ("two", kernel(mask=1, cap=255), True),
        ("four", kernel(mask=3, cap=255), True),
        ("nibbles", kernel(cap=15), True),
        ("bytes", kernel(cap=255), True),
        ("constant-bound", kernel(cap=255).replace("and v2,v0,255", "const v2,255"), True),
        ("offset-boundary", kernel(input_base=3841, cap=255, bin_base=3072,
                                   finish="load v13,3079\n  ret v13"), True),
        ("exit-phi", kernel(alternate=True), True),
        ("exit-trap", kernel(finish="trap 123"), True),
        ("overlap", kernel(input_base=380), False),
        ("input-trap", kernel(input_base=4090), False),
        ("bin-trap", kernel(bin_base=4093), False),
        ("wrap-address", kernel(input_base=4294967295), False),
        ("large-trip-bound", kernel(cap=511), False),
        ("signed-trip-bound", kernel(cap=2147483711), False),
        ("unsupported-mask", kernel(mask=5), False),
        ("different-step", kernel(step=2), False),
        ("different-increment", kernel(increment=2), False),
        ("observed-count", kernel(count_use=True), False),
        ("volatile", kernel(extra="vstore 1,v6"), False),
        ("extra-store", kernel(extra="store 2000,v11"), False),
        ("body-trap", kernel(extra="div v20,v6,v1"), False),
        ("extra-load", kernel(extra="load v15,v1"), False),
    ]
    rng = random.Random(2315)
    memories = [[value] * 4096 for value in (0, 1, 7, 0xffffffff)]
    memories += [[rng.getrandbits(32) for _ in range(4096)] for _ in range(4)]
    arguments = (0, 1, 15, 16, 63, 64, 127, 255, 0x80000000, 0xffffffff)
    cfg = KIT / "machines/machine_slow_memory.cfg"
    machine = K.load_machine(str(cfg))
    checks = 0
    with tempfile.TemporaryDirectory(prefix="packed-counts-") as temp:
        driver = Path(temp) / "driver.cpp"
        binary = Path(temp) / "driver"
        driver.write_text(DRIVER)
        modules = ("kir", "cfg", "ssa", "passes", "sim", "backend", "packed_counts")
        command = shlex.split(os.environ.get("CXX", "c++"))
        subprocess.run(command + ["-std=c++17", "-O1", "-Wall", "-Wextra", "-Werror",
                                  "-pedantic", "-I", str(ROOT / "src"), str(driver),
                                  *(str(ROOT / "src" / (name + ".cpp")) for name in modules),
                                  "-o", str(binary)], check=True)
        for name, source, accepted in cases:
            args = [str(binary), str(cfg), "accept" if accepted else "reject"]
            result = subprocess.run(args, input=source, capture_output=True, text=True)
            assert result.returncode == 0, (name, result.stderr)
            p = K.parse_program(result.stdout)
            K.check_machine_features(p, machine)
            original, optimized = K.compile_program(K.parse_program(source)), K.compile_program(p)
            for bound in arguments:
                for branch in (0, 1):
                    for memory in memories:
                        inp = K.Inputs([bound, branch], [(0, memory)], {})
                        a = K.execute(original, inp.args, inp.segments, inp.vin, 25000)
                        b = K.execute(optimized, inp.args, inp.segments, inp.vin, 25000)
                        assert a.status != "TIMEOUT", (name, bound)
                        difference = K.first_difference(a, b)
                        assert not difference, (name, bound, branch, difference)
                        checks += 1
            print("PASS", name, flush=True)
    print(f"{len(cases)} proof gates and {checks} independent comparisons passed")


if __name__ == "__main__":
    main()
