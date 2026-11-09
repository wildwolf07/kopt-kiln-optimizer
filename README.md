# kopt: an optimizer for the Kiln

`kopt` rewrites a KIR program into one that does exactly the same thing in fewer Kiln cycles. It is an SSA-based optimizing compiler middle and back end written in C++17, with no dependencies.

## Build and run

```
./build.sh
./kopt IN.kir --machine MACHINE.cfg [--profile PROFILE.prof] -o OUT.kir
```

`build.sh` needs `g++` 11 or newer (or set `CXX=clang++`) and takes a few seconds. `kopt` works from any folder. It writes only `OUT.kir` and exits 0.

## Results on the starter kit

Cycles on the sample input of all 100 practice programs. The development harness compares observable behaviour against the kit interpreter and checks byte-for-byte determinism for every program/machine pair. The table below records commit `acb68c8`; timings are sample-input cycle totals, not a prediction of hidden-test performance.

| Machine | Cycles before | Cycles after | Speed-up |
|---|---:|---:|---:|
| default | 103,671 | 16,527 | 6.27x |
| few_registers | 202,164 | 25,592 | 7.90x |
| no_fused | 107,966 | 20,218 | 5.34x |
| slow_memory | 111,254 | 24,319 | 4.58x |
| wide_fast | 55,744 | 12,923 | 4.31x |

The 15 solved examples of the kit: kopt matches or beats 13 of them (for example `branchy_select` 1323 -> 211 cycles, `strength_ladder` 327 -> 223).

## How it stays correct

1. Transformations are designed around the exact arithmetic, trap and effect rules (see `DESIGN.md`, section 5). Finite tests support these arguments but do not prove correctness for every input.
2. Before writing its output, kopt checks every candidate on 16 typical inputs and checks improving candidates on additional fixed-seed inputs with its C++ port of the reference interpreter (kit-style edge values, special pairs, random and typical inputs). Any difference in the result, trap kind, volatile log or data memory rejects the candidate. If no candidate survives, the input is written unchanged.
3. Development checks for the recorded snapshot: the kit interpreter on all 100 programs x 5 machines with 50 generated inputs plus the sample input per pair; 2,000 differential fuzz programs (seed 1109) with traps, aliasing, volatile I/O and irreducible control flow; and both saved regressions in `tests/regress`. The separate CI smoke suite is described below.

## Developer tools

The benchmark, fuzzer and regression tools need the starter kit; set `KIT` to its `Compilers/COMP10` folder. The smoke suite uses only our own fixtures.

| Command | What it does |
|---|---|
| `python3 tools/smoke.py` | Kit-free semantic cases, negative controls, determinism, unsupported-instruction checks, and wrapper execution from another folder |
| `tools/bench.py --machines all` | Optimizes every practice program on every machine, validates with the kit's interpreter, counts cycles, checks determinism |
| `tools/fuzz.py --count 2000` | Differential fuzzing on random programs and random machines |
| `tools/regress.py` | Re-runs every past bug in `tests/regress` |
| `tools/genbig.py loops 100000` | Generates very large programs for timing |
| `KOPT_VERBOSE=1 ./kopt ...` | Shows every candidate and the one chosen |
| `./build/kopt-bin --sim P.kir --machine M.cfg --input I.in` | Runs a program and shows where the cycles go |

`DESIGN.md` explains every pass.

## Compatibility checks

GitHub Actions builds on `ubuntu-22.04` using `g++-11`, then compiles with
`-std=c++17 -O2 -Wall -Wextra -Werror -pedantic` and runs `python3 tools/smoke.py`.
The smoke suite covers nine programs across five independently written machine
configurations. It checks hand-calculated results, traps, memory and volatile
behaviour through differential checks, and rejects four deliberately corrupted
programs. It fails on strict-mode errors or wrapper fallback. No kit download or
third-party Python package is needed for that job.

The smoke suite uses our interpreter for differential checks and is not a
replacement for the independent kit gates. Before merging, run:

```sh
export KIT=/path/to/LLH-26/Compilers/COMP10
python3 tools/bench.py --machines all --random 50
python3 tools/fuzz.py --count 2000 --seed 1109
python3 tools/regress.py
```

For a short demo and questions about the implementation, see [VIVA.md](VIVA.md).
