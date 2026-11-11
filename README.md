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
allocation, counted-loop, layout and correctness changes. The `optimizer-best`
branch adds loop-nest flattening, irreducible-cycle splitting, closed forms
for summation loops, population-count and bit-reverse idioms, state-machine
dispatch tables, division by constants, min/max and Horner regrouping,
counting selects, load phis, store selects, return-block copying and
profile-guided timing inputs. The `optimizer-frontier` branch combines
`optimizer-next` at `8a818d6` with spill-slot sharing and larger-program
allocation from `58b5077`, pressure-aware scheduling, pure-region tree ordering,
and bounded rematerialization. The `optimizer-forge` branch builds on `f6088bb` with backward scheduling,
pure instruction sinking, source-derived finite-domain specialization, and a
range-cache lifetime fix. The `optimizer-apex` branch builds on `dac7d75`: large-function lazy
coalescing and local analysis refresh reduce compile work; backward bit-demand
proofs and packed lookup alternatives cover additional finite computations.
The vector stage adds exact bit-affine synthesis and final layout polishing.
This `optimizer-stream` branch starts from integrated main `a3e67fe`, preserving
its later speculation and store rewrites. It adds the previously validated wide
finite-domain and constant-load splitting candidates, followed by exact rolling
load reuse with bounded unrolling and scheduling alternatives. Other active
worktrees are not modified.

| Machine | Original KIR | Starting optimizer da2928e | This candidate | Speedup vs original |
|---|---:|---:|---:|---:|
| default | 103,671 | 16,527 | 8,973 | 11.55x |
| few_registers | 202,164 | 25,592 | 13,978 | 14.46x |
| no_fused | 107,966 | 20,218 | 10,847 | 9.95x |
| slow_memory | 111,254 | 24,319 | 13,351 | 8.33x |
| wide_fast | 55,744 | 12,923 | 6,860 | 8.13x |

Every program/machine pair is checked against the kit on its sample plus 100
additional inputs, and optimized twice for determinism. Individual programs can
get slower; inspect per-program comparisons as well as totals.

## Validation

Kit-free checks, also available on Ubuntu 22.04/g++ 11 CI:

```sh
python3 tools/smoke.py
python3 tests/pressure.py
python3 tests/wide_finite.py --kit-free
python3 tests/load_rematerialize.py --kit-free
python3 tests/rolling_load.py --kit-free
```

The smoke suite covers arithmetic, loops, guarded division, memory, scratch,
volatile operations and traps, plus four deliberately corrupted negative
controls. Dense-pressure tests compare against a separate arithmetic oracle
and exercise bounded search/graph construction.

Independent kit checks (the kit is not bundled):

```sh
export KIT=/path/to/LLH-26/Compilers/COMP10
python3 tools/bench.py --machines all --random 50
python3 tools/fuzz.py --count 2000 --seed 1205
python3 tools/metamorph.py --count 1000 --seed 1206
python3 tools/regress.py
CXX=clang++ python3 tests/arithmetic_compact.py
CXX=clang++ python3 tests/signed_pow2.py
CXX=clang++ python3 tests/counted_loops.py --integrated-bin build/kopt-bin
python3 tests/unswitch_pipeline.py
python3 tests/monotone_unswitch.py --count 300
python3 tests/pipeline_across.py --count 300
```

The fuzzer includes conditional pointer cursors, counted recurrences and
literal-driven rare inputs. Metamorphic testing renames registers, shuffles
blocks, changes constants and varies machines. Counted/unswitch tests inspect
all dumped candidates as well as winners, so fallback cannot mask a bad
transformation. Regression `.in` files preserve rare arguments that ordinary
fixed-seed testing can miss.

## Design and diagnostics

[DESIGN.md](DESIGN.md) explains every pass, safety argument and limitation.

- `KOPT_VERBOSE=1`: candidate cycles and chosen candidate.
- `KOPT_STRICT=1`: fail on a candidate self-check mismatch.
- `KOPT_DUMP=DIR`: dump candidates for development.
- `KOPT_TIMING=1`: diagnostic timings only; never changes selection.
- `KOPT_DISABLE=PASS`: disable passes for debugging.
- `./build/kopt-bin --sim P.kir --machine M.cfg --input I.in`: exact cycle breakdown.

Training runs and self-checks are finite safeguards. Transformations still need
semantic justification, and passing tests cannot guarantee a hidden-test score.
There is no wall-clock-based choice of output or timed fallback.

For actual randomized scoring beyond the generator's fixed edge prefix, run
`python3 tools/bench.py --machines all --score-offset 40`. The historical
default offset is zero and covers eight edge inputs, regardless of seed.
`KOPT_EXEC=/absolute/path/to/another/kopt` selects a separate baseline executable
without rebuilding or changing either checkout.

New arithmetic candidates share a quotient/remainder pair using the exact
wrapping identity, and lower signed power-of-two operations using unsigned
magnitudes (including INT_MIN). Original candidates remain available. Exact
duplicate-block sharing and bounded common-suffix sharing can reduce cache
pressure; the cycle model includes any extra jumps.

Pressure scheduling tracks values needed by successor blocks and later scheduling
windows. Pure-region tree ordering reduces long live ranges without crossing
memory or trapping operations. Rematerialization duplicates only a bounded
number of cheap parameter-based expressions, with guards against extending
parameter lifetimes. These are measured alternatives, not unconditional choices.
See [BENCHMARKS.md](BENCHMARKS.md) for paired results and individual regressions.

Backward scheduling offers a second direction through the existing dependence
graph. Pure sinking delays single-user expressions without crossing unsafe
loop boundaries. Finite-domain specialization proves that a pure function
depends on at most six input bits in the earlier stage or ten in a separate
final stage, exhaustively evaluates that complete domain,
and emits a reduced decision graph. It derives every table from the supplied
program at runtime; it has no stored program answers. [RESEARCH.md](RESEARCH.md)
records the references, independent adaptations and rejected experiments.

The apex baseline preserved forge's practice-suite cycle totals. That stage
improved compiler throughput and generated recurrences whose relevant input
bits become visible only through final masks. `tools/finite_sweep.py`
reproduces the complete-optimizer comparison. The lookup values always come
from exhaustive evaluation of the program supplied on the command line.

The bit-affine alternative proves XOR/shift/selection expressions for every
input using GF(2) coefficient forms, then emits a branch-free matrix. It does
not guess linearity from sample executions. Unsupported or nonlinear expressions
retain earlier candidates. `tools/affine_sweep.py` checks complete optimizers on
independently generated CRC-style and XOR/shift kernels; `tests/bit_affine.py`
validates the pass directly against the official interpreter.

Rolling memory reuse proves that the next iteration's first read is already
available from a successful load or store in the preceding iteration. It keeps
all stores, uses a valid constant-address initial read, and carries the proved
value through a phi. Unknown aliases, effects, unsupported recurrences and
complex loop shapes reject. Bounded unrolling and loads-only scheduling follow
as separate candidates. `tools/rolling_sweep.py` checks generated sorting
kernels with varied bases, strides and orderings against a baseline executable.

`tools/bench.py --report /tmp/report.json` records full per-case cycle and
held-out data, compiler CPU time and wall time. CPU diagnostics help distinguish
contention from compiler work; the contest still enforces wall-clock limits.
