# kopt: an optimizer for the Kiln

`kopt` rewrites a KIR program into one that does exactly the same thing in fewer Kiln cycles. It is an SSA-based optimizing compiler middle and back end written in C++17, with no dependencies.

## Build and run

```
./build.sh
./kopt IN.kir --machine MACHINE.cfg [--profile PROFILE.prof] -o OUT.kir
```

`build.sh` needs `g++` 11 or newer (or set `CXX=clang++`) and takes a few seconds. `kopt` works from any folder. It writes only `OUT.kir` and exits 0.

## Results on the starter kit

Cycles on the sample input of all 100 practice programs. Every output passes `kvalidate --against` on every machine, and running `kopt` twice gives the identical file.

| Machine | Cycles before | Cycles after | Speed-up |
|---|---:|---:|---:|
| default | 103,671 | 16,743 | 6.19x |
| few_registers | 202,164 | 26,916 | 7.51x |
| no_fused | 107,966 | 20,228 | 5.34x |
| slow_memory | 111,254 | 24,319 | 4.58x |
| wide_fast | 55,744 | 12,923 | 4.31x |

The 15 solved examples of the kit: kopt matches or beats 13 of them (for example `branchy_select` 1323 -> 211 cycles, `strength_ladder` 327 -> 223).

## How it stays correct

1. Every transformation is exact by construction (see `DESIGN.md`, section 5).
2. Before writing its output, kopt runs the input and every candidate program on about 120 inputs with its own copy of the reference interpreter (kit-style edge values, special pairs, random and typical inputs). Any difference in the result, trap kind, volatile log or data memory rejects the candidate. If no candidate survives, the input is written unchanged.
3. Development testing: the official kit validator on all 100 programs x 5 machines, a differential fuzzer (`tools/fuzz.py`) that has compiled more than 12,000 random programs with traps, aliasing, volatile I/O and irreducible control flow, a regression corpus (`tests/regress`), and AddressSanitizer/UBSan builds.

## Developer tools

These need the starter kit; set `KIT` to its `Compilers/COMP10` folder.

| Command | What it does |
|---|---|
| `tools/bench.py --machines all` | Optimizes every practice program on every machine, validates with the kit's interpreter, counts cycles, checks determinism |
| `tools/fuzz.py --count 2000` | Differential fuzzing on random programs and random machines |
| `tools/regress.py` | Re-runs every past bug in `tests/regress` |
| `tools/genbig.py loops 100000` | Generates very large programs for timing |
| `KOPT_VERBOSE=1 ./kopt ...` | Shows every candidate and the one chosen |
| `./build/kopt-bin --sim P.kir --machine M.cfg --input I.in` | Runs a program and shows where the cycles go |

`DESIGN.md` explains every pass.
