# kopt: the Kiln optimizer

A standalone C++17 optimizer for COMP10 “Oxygen Debt”. It combines SSA analysis,
source-derived algebraic rewrites, machine-aware scheduling and register
allocation, and deterministic search with an exact copy of the Kiln cycle model.

## Build and run

From the repository root:

```sh
./build.sh
./kopt INPUT.kir --machine MACHINE.cfg -o OUTPUT.kir
./kopt INPUT.kir --machine MACHINE.cfg --profile PROFILE.prof -o OUTPUT.kir
```

Requires only g++ 11 or newer (or `CXX=clang++ ./build.sh`) and the C++ standard
library. No package installation or network access is needed. The executable
wrapper works from any current directory, including paths containing spaces.
Normal execution writes only the requested output file. Profiles are optional
hints; incorrect hints do not establish any semantic facts.

## What is implemented

The optimizer includes constant/range propagation, value numbering, memory
forwarding, loop-invariant motion, counted-loop formulas, population-count and
bit-reverse idioms, finite-domain and bit-affine synthesis, constant division,
loop rotation/unrolling/flattening/unswitching, branch/store predication,
rolling load reuse, packed indexed counters, and proved matrix/vector and
matrix-product recipes. Backend alternatives cover pressure-aware forward and
backward scheduling, shared spill slots, rematerialization and register-touch
search. Every transformation works from the supplied program, without program
name matching or stored kernel answers. [DESIGN.md](DESIGN.md) gives pass order,
complexities, safety arguments, machine dependence and limitations.

The final release adds bounded instruction-window scheduling, reuses exact
scores for duplicate candidates, stops candidate construction at the search
budget, and fixes matrix-recognition arithmetic, unreachable-block SSA handling
and store-edge memory safety. Population-count and bit-reverse emission is
explicitly sequenced to preserve the same scheduling choices across compiler
targets.
Recovery after a process failure preserves an already legal input verbatim or
expands unsupported fused instructions in a separate mode. Validation rejects
recovery diagnostics so a fallback cannot mask a failed optimizer run.

## Measured public results

Official interpreter and cycle model, 100 public programs on each machine.
Sample totals are sums; held-out speedups are geometric means over programs,
using eight generated inputs starting at offset 40 with seed 12345 + 7919.
These measurements are evidence about the public tests, not hidden-score
predictions.

| Machine | Original sample cycles | Release sample cycles | Held-out geometric speedup |
|---|---:|---:|---:|
| default | 103,671 | 8,525 | 7.790x |
| few_registers | 202,164 | 13,589 | 11.560x |
| no_fused | 107,966 | 10,379 | 7.093x |
| slow_memory | 111,254 | 11,987 | 6.842x |
| wide_fast | 55,744 | 6,625 | 5.472x |

Against main `2400069`, held-out cycles improve on 19 pairs, tie on 480 and
increase by one cycle on one pair. All five aggregate held-out totals improve.
[BENCHMARKS.md](BENCHMARKS.md) records individual changes and tradeoffs;
`results/release-validation.json` identifies the tested source and binaries.

## Validation

The official kit is external and is not bundled. To run independent checks:

```sh
export KIT=/path/to/LLH-26/Compilers/COMP10
KOPT_STRICT=1 python3 tools/bench.py --machines all --random 100 --score-offset 40 --timeout 5 --jobs 1
python3 tools/fuzz.py --count 3000 --seed 131311
python3 tools/regress.py
python3 tools/metamorph.py --count 500 --seed 131313
python3 tools/release_stress.py
```

Kit-free checks include:

```sh
python3 tools/smoke.py
python3 tests/evaluation_cache.py --kit-free
python3 tests/fallback.py --kit-free
python3 tests/window_polish.py --kit-free
python3 tests/final_safety.py --kit-free
python3 tests/bit_idiom_order.py --kit-free
```

CI builds on Ubuntu 22.04/g++11, runs the proof suites, and checks all 500 public
pairs, generated programs and large-program time limits against a pinned copy
of the official oracle. The test kit is downloaded only by CI; the optimizer
and its build script do not use the network.

## Diagnostics and limits

`KOPT_VERBOSE=1` reports choices; `KOPT_STRICT=1` fails on a self-check mismatch;
`KOPT_DUMP=DIR` writes development candidates; `KOPT_TIMING=1` reports timing
without affecting decisions; `KOPT_DISABLE=PASS` supports controlled comparisons.
Use `./build/kopt-bin --sim P.kir --machine M.cfg --input I.in` for cycle details.

Search budgets depend on program structure and fixed inputs, never the clock.
Candidates receive finite self-checks before output. Tests and sampled checks
cannot prove arbitrary equivalence or guarantee a hidden-test score. Conservative
proof gates reject unsupported shapes, and an aggregate training win can still
cost more for a different input distribution. See section 7 of DESIGN.md.
