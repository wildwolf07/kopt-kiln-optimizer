# kopt: the Kiln optimizer

A C++17 optimizer for COMP10 “Oxygen Debt”, using SSA analysis, machine-aware
lowering and deterministic candidate search. No runtime dependencies beyond the
standard library.

```sh
./build.sh
./kopt IN.kir --machine MACHINE.cfg [--profile PROFILE.prof] -o OUT.kir
```

Build with g++ 11 or newer, or `CXX=clang++ ./build.sh`. The executable wrapper
works from any current directory. Normal execution writes only the named output.

## Public benchmark evidence

Cycles summed over the 100 kit sample inputs per machine, using the official
interpreter/timing model. These are aggregate ratios, not geometric means or
hidden-test predictions. The `optimizer-integrated` candidate combines the
core at `64574bd`, memory-fact scheduling from `e818222`, and additional tested
allocation, counted-loop, layout and correctness changes. The `opt-claude3`
branch adds loop-nest flattening, irreducible-cycle splitting, min/max and
Horner regrouping, counting selects, load phis, store selects and
return-block copying.

| Machine | Original KIR | Starting optimizer da2928e | This candidate | Speedup vs original |
|---|---:|---:|---:|---:|
| default | 103,671 | 16,527 | 11,194 | 9.26x |
| few_registers | 202,164 | 25,592 | 17,482 | 11.56x |
| no_fused | 107,966 | 20,218 | 14,021 | 7.70x |
| slow_memory | 111,254 | 24,319 | 15,905 | 7.00x |
| wide_fast | 55,744 | 12,923 | 8,847 | 6.30x |

Every program/machine pair is checked against the kit on its sample plus 50
additional inputs, and optimized twice for determinism. Individual programs can
get slower; inspect per-program comparisons as well as totals.

## Validation

Kit-free checks, also available on Ubuntu 22.04/g++ 11 CI:

```sh
python3 tools/smoke.py
python3 tests/pressure.py
```

The smoke suite covers arithmetic, loops, guarded division, memory, scratch,
volatile operations and traps, plus four deliberately corrupted negative
controls. Dense-pressure tests compare against a separate arithmetic oracle
and exercise bounded search/graph construction.

Independent kit checks (the kit is not bundled):

```sh
export KIT=/path/to/LLH-26/Compilers/COMP10
python3 tools/bench.py --machines all --random 50
python3 tools/fuzz.py --count 2000 --seed 1123
python3 tools/metamorph.py --count 1000 --seed 1124
python3 tools/regress.py
CXX=clang++ python3 tests/counted_loops.py --integrated-bin build/kopt-bin
python3 tests/unswitch_pipeline.py
```

The fuzzer includes conditional pointer cursors, counted recurrences and
literal-driven rare inputs. Metamorphic testing renames registers, shuffles
blocks, changes constants and varies machines. Counted/unswitch tests inspect
all dumped candidates as well as winners, so fallback cannot mask a bad
transformation. Regression `.in` files preserve rare arguments that ordinary
fixed-seed testing can miss.

## Design and diagnostics

[DESIGN.md](DESIGN.md) explains every pass, safety argument and limitation.
[VIVA.md](VIVA.md) provides a short demonstration and judge questions.

- `KOPT_VERBOSE=1`: candidate cycles and chosen candidate.
- `KOPT_STRICT=1`: fail on a candidate self-check mismatch.
- `KOPT_DUMP=DIR`: dump candidates for development.
- `KOPT_TIMING=1`: diagnostic timings only; never changes selection.
- `KOPT_DISABLE=PASS`: disable passes for debugging.
- `./build/kopt-bin --sim P.kir --machine M.cfg --input I.in`: exact cycle breakdown.

Training runs and self-checks are finite safeguards. Transformations still need
semantic justification, and passing tests cannot guarantee a hidden-test score.
There is no wall-clock-based choice of output or timed fallback.
