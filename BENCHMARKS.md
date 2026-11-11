# Packed indexed counts

Comparison against main `64ce095` on the same public programs, machines and
inputs. The candidate pass keeps 2, 4 or 8 counters in at most two registers,
then applies their deltas at the loop exit. It uses a source-derived proof
of the trip bound, address validity, disjointness and effects.

| Scope | Main cycles | Packed candidate cycles |
|---|---:|---:|
| Histogram, slow-memory sample | 587 | 434 |
| Histogram, slow-memory held-out | 2,657 | 2,136 |
| Slow-memory suite, sample total | 13,351 | 13,198 |
| Slow-memory suite, held-out total | 80,350 | 79,829 |

The full suite passed all 500 program and machine pairs with 100 generated
inputs per pair, strict candidate checks and repeat-output checks. Held-out
scoring starts at offset 40. The histogram improvement was the sole cycle
change in both the sample and held-out comparisons.

Eight generated kernels varied bin counts, memory addresses, masked trip
bounds, initial bin values and exit behavior. In the paired runs on all five
machines, 25 pairs improved and 15 tied. Aggregate generated-case cycle
reductions were 25.7% on default, 13.4% on few_registers, 23.4% on no_fused,
44.8% on slow_memory and 18.0% on wide_fast. All 1,359 emitted packed
candidates passed 54,360 independent interpreter comparisons, covering
initial values that wrap, concentrated counts and a trap after writeback.

A slow-memory sweep across lengths 0 through 63 found 58 faster lengths
and six slower short lengths, with 38,816 → 29,185 total cycles. The fixed
writeback makes an empty histogram cost 60 cycles instead of 8 in this
candidate. The compiler selects the packed form based on aggregate simulated
cycles.

On the loaded Mac, the slowest compiler CPU time across the public suite
was 0.993 seconds and the maximum observed wall time was 5.27 seconds.
Selected normal cases on a pinned Linux VM CPU completed in under two seconds.
Both 100k-instruction stress inputs produced byte-identical outputs to main,
with wall times of 2.93 and 11.63 seconds. The judge limit uses wall time.

The frozen build passed 3,000 strict fuzz programs, 500 metamorphic
programs, 44 regressions, 100 mutation cases, and all 18 root test suites.
The direct packed-counter tests passed 3,520 comparisons and the sanitizer
run passed 3,360 comparisons. The unseen-machine sweep covered 1,200 pairs
with zero slowdowns against the input programs and zero wrapper fallbacks.
Source hashes and measured results are recorded in
`results/bins-validation.json`.

Reproduce the public comparison and direct proof checks with:

```sh
./build.sh
KOPT_STRICT=1 KOPT_EXEC="$PWD/build/kopt-bin" python3 tools/bench.py \
  --machines all --random 100 --score-offset 40 --timeout 180 \
  --compare results/stream-sample-cycles.json --report /tmp/packed-report.json
python3 tests/packed_counts.py
```

---

# optimizer-stream validation

Based on main `a3e67fe`, in its own branch and worktree. Adds exact rolling
load reuse and bounded follow-up alternatives, and ports the independently
validated wide finite-domain and constant-load splitting candidates from
`optimizer-resolve` (`f4b615f`). Main and other active worktrees were not edited.

| Machine | Main sample | Stream sample | Main held-out | Stream held-out | Main held-out geo | Stream held-out geo |
|---|---:|---:|---:|---:|---:|---:|
| default | 9,318 | 8,973 | 54,471 | 52,610 | 7.293 | 7.453 |
| few_registers | 14,679 | 13,978 | 87,708 | 84,004 | 10.932 | 11.236 |
| no_fused | 11,696 | 10,847 | 67,537 | 63,098 | 6.594 | 6.798 |
| slow_memory | 13,760 | 13,351 | 82,440 | 80,350 | 6.364 | 6.505 |
| wide_fast | 7,186 | 6,860 | 41,241 | 39,442 | 5.191 | 5.295 |

500 program/machine pairs passed sample plus 30 generated-input checks,
feature validation and repeat-output determinism. A second paired campaign
against separately built main passed sample plus 100 generated inputs, strict
candidate checks and repeat determinism. Held-out scoring uses eight generated
inputs starting after offset 40, skipping the fixed edge prefix. Both sample
and held-out comparisons have 12 faster pairs, 488 ties and zero regressions.
These public measurements do not establish a hidden-test score.

The new rolling stage's sample wins over the ported baseline include:

| Kernel | Machine | Before | After |
|---|---|---:|---:|
| bubble sort | wide_fast | 407 | 289 |
| bubble sort | no_fused | 692 | 647 |
| stencil3 | default | 174 | 165 |
| stencil3 | no_fused | 193 | 168 |
| stencil3 | slow_memory | 301 | 253 |
| alias stores | default | 184 | 171 |

The ported wide specialization removes most of the divisor-count loop cost,
and constant-load splitting improves slow-memory matrix multiplication.
Earlier candidates and all earlier seed trajectories stay available.

Eight independently generated sorting kernels vary base address, stride and
comparison direction. Forty pairs across five machines passed sample plus 100
inputs and repeat determinism. Fourteen improve and 26 tie on both sample and
held-out totals; none regress. Aggregate results:

| Machine | Sample before → after | Held-out before → after |
|---|---:|---:|
| default | 7,825 → 7,825 | 61,050 → 61,050 |
| few_registers | 11,225 → 11,225 | 87,091 → 87,091 |
| no_fused | 9,149 → 8,311 | 71,386 → 64,721 |
| slow_memory | 12,817 → 12,817 | 99,706 → 99,706 |
| wide_fast | 6,653 → 4,280 | 52,171 → 33,479 |

Reproduce with:

```sh
python3 tools/bench.py --machines all --random 30 --score-offset 40 \
  --timeout 180 --jobs 3 --report /tmp/report.json
python3 tools/rolling_sweep.py --baseline /path/to/main/kopt --candidate ./kopt \
  --cases 8 --seed 2215 --save /tmp/generated.json
```

Frozen validation passed: 3,000 strict-mode fuzz programs (seed 2211), 500
metamorphic programs (seed 2212), 300 ASan/UBSan fuzz programs (seed 2214),
44 saved regressions, 100 mutation cases with identical cycle totals, and
50 smoke pairs plus four negative controls. The 1,200 unseen-machine cases
report zero outputs slower than the input and zero wrapper fallbacks.

All 16 other root test suites passed against unchanged source hashes,
including 87,620 integrated counted-loop comparisons over 6,326 dumped
candidates. The added rolling suite passed 60 proof/CFG/effect fixtures,
23 promotions and 37 rejections under four backend modes, with 7,680 independent
official comparisons. It checks exact store preservation, phi structure, valid
SSA, repeat determinism and scratch restrictions. Kit-free mode also passed
7,680 local-interpreter comparisons under ASan/UBSan. An additional full-pipeline
check ran 20 strict compilations and compared all 852 emitted rolling candidates
against the original on 100 inputs each: 85,200 independent official comparisons,
including partial stores followed by invalid-address traps, all passed. Local-interpreter checks
complement the independent official oracle; they are not independent evidence.

The full 500-pair parallel report measured maximum compiler CPU time 0.982 s
on the Mac. Some wall times exceeded five seconds during concurrent work
(maximum 5.72 s), so CPU diagnostics are recorded separately. The strict C++17
Linux build was also tested with one pinned VM CPU: the eight slowest Mac
program/machine cases completed in 1.11–1.99 s wall time, with 1.07–1.95 s CPU.
Generated ~100k-instruction straight/loop inputs completed in 2.99/11.38 s wall
(2.95/11.32 s CPU), with approximately 119/186 MiB peak child RSS. Eight independent official comparisons of both Linux-built large-program
outputs also passed. The contest
uses wall-clock limits; these local measurements do not predict its CPU speed.

Pure guard-chain fusion was evaluated separately and deferred: the initial
500-pair experiment saved only two sample cycles; twenty raw-seed trials
established no further gain. That module is absent from production.

Full per-case results, source hashes, test logs' summaries and generated timing
results are in `results/stream-*.json`. Kit folders and binaries are not bundled.

---

# optimizer-vector validation

Isolated branch based on `optimizer-apex` (`0683c43`). Adds an exact symbolic
bit-affine candidate and bounded final trace-layout polishing. Main and other
candidate worktrees were not edited.

Same practice inputs, 100 programs on five machines:

| Machine | Apex sample cycles | Vector | Original / vector |
|---|---:|---:|---:|
| default | 9,844 | 9,813 | 10.56x |
| few_registers | 14,991 | 14,941 | 13.53x |
| no_fused | 12,307 | 12,264 | 8.80x |
| slow_memory | 14,138 | 14,104 | 7.89x |
| wide_fast | 7,464 | 7,431 | 7.50x |

31 pairs improve, 457 tie, 12 regress. All regressions are one to three sample
cycles: histogram/default 272 to 275; gray_code_sum and strength_ladder/no_fused
11 to 13; fib and sum_cubes_mod on four machines gain one cycle of cost; and
fnv_hash/few_registers 115 to 116. These are explicitly retained tradeoffs,
not a claim of monotonic improvement on every unseen input.

The straight-line CRC practice case improves on all machines: default 41 to 21,
few_registers 41 to 26, no_fused 68 to 32, slow_memory 41 to 21, wide_fast 41 to 16.
Final layout also improves merge_sorted/few_registers 526 to 504, and several
finite-table cases. Per-pair data: `results/vector-sample-cycles.json`.

Actual held-out random scoring uses eight inputs beyond the fixed edge prefix:

| Machine | Apex random cycles | Vector | Geometric speedup apex | Vector |
|---|---:|---:|---:|---:|
| default | 56,949 | 56,709 | 7.042 | 7.158 |
| few_registers | 88,196 | 88,038 | 10.768 | 10.925 |
| no_fused | 71,161 | 70,859 | 6.360 | 6.418 |
| slow_memory | 84,407 | 84,091 | 6.189 | 6.299 |
| wide_fast | 42,867 | 42,525 | 5.038 | 5.121 |

The affine-only ablation passed all 500 pairs, improving exactly the five CRC
pairs and tying 495. Its held-out totals were 56,789 / 88,076 / 70,873 / 84,247 /
42,667. Final layout accounts for the remaining gains and small regressions.
Both stages append alternatives without changing earlier seed trajectories.

Four independently generated machines, seed 2013, passed 400 paired checks:

| Machine | Random apex | Vector | Paired geometric speedup |
|---|---:|---:|---:|
| generated_0 | 83,557 | 82,847 | 1.01316x |
| generated_1 | 69,700 | 69,220 | 1.01436x |
| generated_2 | 85,928 | 85,784 | 1.00548x |
| generated_3 | 105,004 | 104,737 | 1.00115x |

These vary issue width 1–4, registers 7/9/20/32, ALU latency 1–3, cache size
8/16/64, load latency 1–12, and fused availability. Every row validates both
versions on sample +100 generated inputs, then repeat output. Details are in
`results/vector-machine-sweep.json`.

Generated CRC/XOR kernels (`tools/affine_sweep.py`, seed 2020): 41 pairs improve,
nine tie and none regress across 50 complete-optimizer comparisons. The source
uses different polynomials and branch/selection forms, plus full-width XOR/shift
chains. Examples on default: a 96-round CRC-style function 700 to 26 cycles;
a 24-round XOR/shift function 226 to 96. These are independent generated tests,
not hidden-score claims.

| Machine | Generated sample apex | Vector | Random apex | Vector |
|---|---:|---:|---:|---:|
| default | 2,015 | 369 | 16,120 | 2,952 |
| few_registers | 2,015 | 407 | 16,120 | 3,256 |
| no_fused | 2,313 | 580 | 18,504 | 4,640 |
| slow_memory | 2,015 | 369 | 16,120 | 2,952 |
| wide_fast | 2,015 | 308 | 16,120 | 2,464 |

Direct pass tests bypass optimizer selection and fallback: 18,168 official
comparisons across 74 sources (47 accepted, 27 rejected), using zero, basis,
edge, independent random and superposition inputs. They check the source matrix
independently from basis executions, output preservation on rejection, SSA,
repeat determinism, high parameter IDs, bit 31, complement algebra, exact affine
carry/borrow, masked shift counts and grouped-wire emission. A 771-instruction
CRC-style source becomes 98 raw instructions; raw output is not always the best
candidate. On 33 basis/zero inputs, default cycles drop 48,246 to 3,663; no_fused
49,566 to 5,049. The same proof/structural acceptance gates have a kit-free CI
mode. Source proof, not sampled affine behavior, justifies the transformation.

Frozen source gates: 2,500 stronger fuzz programs seed 2011, 1,000 metamorphic
programs seed 2012, 300 ASan/UBSan fuzz programs seed 2014, 35 regressions, 50 smoke
pairs plus four negative controls, dense pressure sizes 900/2,000/15,000, and a
strict Linux C++17 build all passed. The initial 500-pair combined run passed
sample +100 generated inputs, determinism and a five-second timeout; slowest
invocation 1.51 seconds under concurrent validation (64.4 seconds suite wall).

The lower-load release run repeated all 500 checks with identical cycle
results: slowest invocation 1.38 seconds, suite wall 63.5 seconds. To assess
compiler overhead without comparing unrelated loads, a separate run alternated
apex/vector directly on the 100 default-machine inputs, one at a time with
strict self-checks. Median wall time was 98.43 / 98.32 ms; maximum 1.041 / 0.918
seconds, sums 16.239 / 15.952 seconds. These noisy observations do not establish
a controlled compiler-throughput speedup. They show no material added overhead
in this paired run. Data: `results/vector-compile-times.json`.

Generated 100k straight/loop inputs finish in 2.27 / 9.07 seconds in the Linux
ARM VM under concurrent work, peak roughly 120 / 177 MiB RSS. Outputs are
byte-identical to the previously validated apex Linux outputs. These are not
judge-x86 runtime measurements. Large programs skip the new bounded stages.

Neither test totals nor research references establish a winning contest rank.
Known limitations and universal proof obligations are documented in DESIGN.md;
RESEARCH.md lists the primary references and independent implementation choices.

Historical apex/forge/frontier/next evidence follows.

---

# optimizer-apex validation

Isolated branch based on `optimizer-forge` (`dac7d75`). Integrates large-function
allocation/analysis improvements from this repository's `optimizer-final`
(`65e03e0`), while keeping the existing small-function allocation order. Adds
backward bit-demand projection and packed finite lookup alternatives. Main and
the other worktrees were not edited.

Practice sample and held-out cycle totals remain **identical** to forge on all
500 program/machine pairs. The four generated-machine sweep (seed 1813) also
passes all 400 paired checks with identical sample/random cycle counts. This
round's new code-quality evidence is on independently generated recurrences;
it does not claim another gain on the practice suite or a known hidden score.

The final lower-load practice run passed all 500 pairs with 100 generated
validation inputs each and byte-for-byte determinism. Its slowest optimizer
invocation was 0.61 seconds using four workers (24.3 seconds for the suite).
An earlier run under simultaneous compilation/fuzz/mutation/sweep load reached
4.53 seconds; both runs respected the five-second test timeout. Decisions use
structural budgets, never elapsed time.

Compiler throughput on generated 100k inputs:

| Platform / load | Straight seconds | Loop seconds | Peak RSS straight / loop |
|---|---:|---:|---:|
| Mac, lighter load | 1.04 | 2.61 | 140 / 320 MiB |
| Linux ARM VM, concurrent validation | 3.08 | 10.39 | 119 / 176 MiB |

The older forge run recorded 3.66 / 13.11 seconds on the Linux VM under its
concurrent validation. Loads differ; these are observations, not controlled
speedup ratios or judge-x86 time guarantees. Both large Mac outputs passed 16
complete official observable-state checks. Default cycles: straight 170,026,
loop 376,625, versus original 686,591 / 558,161. Lazy coalescing is used only
above 4,096 SSA values; the small allocator's tie order is preserved.

New finite proof and representations:

- Fresh SSA dependence analysis roots every returned bit, complete branch
  operand and division/remainder divisor. Phi demands are unioned to a fixed
  point. Logical shifts, literal masks, bitwise operations and low-bit arithmetic
  propagate only necessary bits; conservative transfers retain more bits when
  uncertain. Exact constant evaluation exposes const/mov aliases without cached
  intervals. At most six retained input bits are allowed.
- Projected equivalence alone does not prove termination. The original program
  still must return for every retained-bit assignment, under the existing 20k
  per-case / one-million-total step limits. Any trap/timeout rejects.
- Original decision graphs remain available. A second candidate packs unsigned
  offsets into power-of-two fields and selects/extracts a constant word. At most
  16 words; high/sign/sparse bits and parameter identity are preserved. Width 32
  bypasses field shifts/masks. Both encodings share one proof/evaluation in the
  optimizer; standalone APIs remain independently testable.

Generated recurrence experiment (`tools/finite_sweep.py`): input values are
unmasked through wrapping arithmetic and masked only at the return. The earlier
literal-AND-use proof rejected these programs. All 60 paired generated checks
improve, with no ties or regressions; each version passes sample +100 generated
validation inputs and repeat-output checks. Additional random scoring skips the
fixed edge prefix.

| Machine | Sample cycles forge | Apex | Random forge | Apex |
|---|---:|---:|---:|---:|
| default | 774 | 124 | 6,192 | 1,006 |
| few_registers | 774 | 124 | 6,192 | 1,006 |
| no_fused | 1,006 | 142 | 8,048 | 1,074 |
| slow_memory | 1,074 | 124 | 8,592 | 1,006 |
| wide_fast | 624 | 146 | 4,992 | 1,182 |

Examples on the default machine: generated case 9 falls 82 to 7 cycles; case 11
falls 92 to 27. These synthetic cases establish coverage and performance on a
new program family, not performance on hidden contest inputs. Reproduce:
`python3 tools/finite_sweep.py --baseline /absolute/path/to/kopt-forge/kopt
--save /tmp/generated.json` (join the command on one line).

Direct frozen-source checks:

- 10,800 official input/projection comparisons across 43 bit-transfer, alias,
  branch, phi, loop, trapping-divisor and zero-initialized-register cases.
- 5,566 existing finite-pass comparisons, including stale-range poisoning,
  projected traps/timeouts and instruction/evaluation-budget caps.
- 19,422 BDD/packed comparisons, covering 1/2/4/8/16/32-bit fields, unsigned bases,
  wrap-boundary outputs, sparse/sign bits, multiple parameters, SSA, aliasing,
  deterministic output and rejection gates. Some packed alternatives are slower;
  exact candidate measurement is required.
- 2,500 stronger fuzz programs seed 1811, 1,000 metamorphic programs seed 1812,
  300 ASan/UBSan fuzz programs seed 1814, 35 regressions, 50 smoke pairs plus
  four negative controls, and dense-pressure sizes 900/2,000/15,000 passed.
- Strict Linux C++17 compilation passed with `-Wall -Wextra -Werror -pedantic`.
  Bit-demand proof gates also have a kit-free Ubuntu/g++11 CI mode.

Source hashes, per-pair metrics and generated-machine descriptions are retained
under `results/`. No external optimizer code, runtime framework, solver,
benchmark fingerprint, cached corpus answer or network use was introduced.

Historical forge/frontier/next evidence follows.

---

# optimizer-forge validation

Isolated branch `optimizer-forge`, based on `optimizer-frontier` at `f6088bb`.
Adds backward preallocation scheduling, conservative single-user pure sinking,
source-derived finite-domain specialization, and a signed-range cache lifetime
fix. The other worktrees and main were not edited.

Same 100 sample programs on each of the five practice machines:

| Machine | frontier | forge | Original / forge |
|---|---:|---:|---:|
| default | 10,102 | 9,844 | 10.53x |
| few_registers | 15,706 | 14,991 | 13.49x |
| no_fused | 13,050 | 12,307 | 8.77x |
| slow_memory | 14,822 | 14,138 | 7.87x |
| wide_fast | 7,766 | 7,464 | 7.47x |

101 pairs improve, 398 tie, one regresses: jump_chain on slow_memory, 12 to 13
cycles. Per-pair evidence: `results/forge-sample-cycles.json`. Examples include
transpose8/slow_memory 379 to 198, matmul4/no_fused 594 to 426, fib/few_registers
190 to 23, and spill_storm/slow_memory 91 to 14. These are measured samples,
not known hidden scores or guaranteed contest rankings.

Held-out scoring uses eight generated inputs at offset 40, beyond the fixed
edge prefix. None is used by the optimizer's candidate selection.

| Machine | Random cycles frontier | Random cycles forge | Geometric speedup frontier | Forge |
|---|---:|---:|---:|---:|
| default | 58,930 | 56,949 | 6.788 | 7.042 |
| few_registers | 92,189 | 88,196 | 10.037 | 10.768 |
| no_fused | 74,187 | 71,161 | 6.018 | 6.360 |
| slow_memory | 90,451 | 84,407 | 5.756 | 6.189 |
| wide_fast | 44,054 | 42,867 | 4.865 | 5.038 |

The frozen source passed 500/500 checks with sample +100 generated validation
inputs per pair, output determinism, and a five-second optimizer timeout. The
slowest measured invocation was 0.61 seconds on the M4 with four test workers.
Reproduce: `python3 tools/bench.py --machines all --random 100 --score-offset 40
--timeout 5 --jobs 4` (join this command on one line).

Ablations before the cache fix (which left all 500 sample cycle counts equal):

| Stage | default | few | no_fused | slow | wide |
|---|---:|---:|---:|---:|---:|
| Backward scheduling | 9,991 | 15,432 | 12,818 | 14,384 | 7,754 |
| + pure sinking | 9,968 | 15,394 | 12,810 | 14,332 | 7,727 |
| + finite-domain specialization | 9,844 | 14,991 | 12,307 | 14,138 | 7,464 |

Backward scheduling improved 54 sample pairs and tied 446. Sinking added 15
improvements and tied 485 versus that build. The stages retain earlier
candidates, but a new candidate can generalize differently from its training
score, as the single sample regression demonstrates.

Generalization on four independent generated machines, 100 programs each:

| Machine | Random cycles frontier | Forge | Paired geometric speedup |
|---|---:|---:|---:|
| generated_0 | 49,196 | 48,151 | 1.0672x |
| generated_1 | 74,802 | 73,136 | 1.0536x |
| generated_2 | 127,421 | 120,167 | 1.0878x |
| generated_3 | 45,573 | 44,483 | 1.0340x |

All 400 paired checks passed complete observable-state validation and
repeat-output checks for both versions. Machines include 7/20/32 registers,
one/two-cycle ALU operations, 8/32/128-instruction caches, different load/multiply
latencies and unavailable fused operations. Seed 1513 and all generated keys
are saved in `results/forge-machine-sweep.json`. Reproduce using
`tools/machine_sweep.py --baseline /absolute/path/to/kopt-frontier/kopt
--machines 4 --seed 1513 --random 100 --save /tmp/sweep.json`.

Direct evidence bypassing winner selection and optimizer fallback:

- Scheduling: 4,665 official-interpreter comparisons across forward, pressure,
  tree, combined, backward and backward+K modes; block/window exports, phis,
  traps, volatile effects and 100,000-deep chains with a 512 KiB stack.
- Sinking: 120,960 official comparisons, SSA checks, deterministic output,
  idempotence, deep chains and caps. Synthetic cold-path arithmetic avoids
  unnecessary calculations; some lowering variants regress, hence candidates.
- Finite specialization: 5,566 official comparisons, high/sign-bit masks,
  multiple parameters, rejected phi/unmasked uses, aliases, zero-initialized
  registers, deliberate old-range poisoning, traps and evaluation budgets.
  Every accepted function has a static domain proof followed by complete
  projected-domain evaluation; this is stronger than a sampled self-check.
- Cache isolation: 60 direct official trap-order comparisons after populating
  range caches with a different function; the inherited implementation fails.
  Full regression `analysis_cache_cross_function` retains the fuzz reproducer.

The fresh fuzz campaign caught stale signed VRP facts leaking across SSA
functions that reuse value IDs. On args 2, the unfixed candidate performs three
volatile reads before bad_address; the original performs two. buildSSA now
clears both induction and signed VRP caches. This fix is necessary for prior
revisions too; finite self-checking alone did not establish their correctness.

Frozen-build campaign: 4,500 stronger fuzz programs (2,500 seed 1611 after
fixing its saved failure, plus 2,000 fresh seed 1711), 1,000 metamorphic programs
(seed 1712), 300 ASan/UBSan fuzz programs (seed 1714), 35 regressions, 50 smoke
pairs plus four negative controls, and dense-pressure sizes 900/2,000/15,000 all
passed. The poisoned-cache test also has a kit-free CI mode.

Linux strict C++17 build passed (`-Wall -Wextra -Werror -pedantic`). Generated
100k straight/loop inputs completed in 3.66/13.11 seconds in the Linux ARM VM
under concurrent tests, at roughly 117/177 MiB peak RSS. These are not timings
on the judges' x86 CPU. Large-input search remains structurally bounded and
skips the new small-program candidate stages.

An early alternate coloring/search-lineage experiment was rejected because it
recovered some older wins while losing more elsewhere. No such switch or code
is present in this production branch.

Historical frontier and next evidence follows.

---

# optimizer-frontier validation

This isolated branch combines `8a818d6` with the committed allocator changes
from `58b5077`, then adds pressure-aware preallocation scheduling, iterative
pure-region tree ordering, bounded parameter-based rematerialization, and
allocator bookkeeping savings. No main or other active worktree was edited.

Sample totals, same 100 programs and five machines:

| Machine | optimizer-next (8a818d6) | frontier | Original / frontier |
|---|---:|---:|---:|
| default | 10,178 | 10,102 | 10.26x |
| few_registers | 15,931 | 15,706 | 12.87x |
| no_fused | 13,051 | 13,050 | 8.27x |
| slow_memory | 15,155 | 14,822 | 7.51x |
| wide_fast | 7,785 | 7,766 | 7.18x |

Per-pair cycles: `results/frontier-sample-cycles.json`. Relative to `8a818d6`,
57 pairs improve, 423 tie, and 20 regress. Examples: wide_expression on
few_registers falls 185 to 71; transpose8 on slow_memory falls 480 to 379.
Regressions include spill_storm on slow_memory (26 to 91), binary_search on
few_registers (85 to 122), and word_count on no_fused (125 to 146).
Changing allocation also changes the candidate search's later seeds; retaining
old candidates does not imply the complete search is monotonic across versions.

Held-out random scoring, eight inputs beyond the fixed edge prefix:

| Machine | Random cycles next | Random cycles frontier | Geometric speedup next | Frontier |
|---|---:|---:|---:|---:|
| default | 59,041 | 58,930 | 6.745 | 6.788 |
| few_registers | 94,834 | 92,189 | 9.818 | 10.037 |
| no_fused | 74,268 | 74,187 | 6.006 | 6.018 |
| slow_memory | 91,577 | 90,451 | 5.783 | 5.756 |
| wide_fast | 44,196 | 44,054 | 4.851 | 4.865 |

All five random cycle sums improve; slow_memory's geometric speedup decreases.
Neither aggregate statistic predicts hidden performance. Reproduce with
`python3 tools/bench.py --machines all --random 50 --score-offset 40 --jobs 4`.
Use `KOPT_EXEC=/absolute/path/to/baseline/kopt` to measure a separate checkout.
This run passed 500/500 validity, behavior and determinism checks; the slowest
optimizer invocation was 0.84 seconds on the M4 with four parallel test workers.

Focused tests bypass candidate selection and fallback:

- `tests/tree_schedule.py`: 3,110 official-interpreter comparisons, covering
  exact region permutation, barriers, three-source/shared DAGs, phi/liveOut,
  terminators, 96-instruction boundaries, and 100,000-deep chains with a 512 KiB
  stack. A producer-first 900-value case uses 115,160 aggregate cycles with
  plain lowering, 49,920 with tree ordering, and 42,464 with tree plus pressure.
- The complete optimizer on that generated pressure program, input 37:
  `optimizer-next` 8,042 cycles / 900 names, frontier 3,570 cycles / 4 names.
- `tests/rematerialize.py`: 25,372 official-interpreter comparisons, including
  underflow traps and ten backend alternatives with/without recomputation.
  Eight runtime stream values on slow_memory improve from the best 69 to 40
  cycles. Some other cases regress, which is why this remains an alternative.
  The public 500-pair ablation measured no additional gain from rematerialization.
- Frozen production sources passed 2,500 stronger fuzz programs (seed 1411),
  1,000 metamorphic programs (seed 1412), 34 saved regressions, 50 smoke pairs
  plus four negative controls, and dense-pressure sizes 900/2,000/15,000.
  A separate AddressSanitizer/UndefinedBehaviorSanitizer build passed 300 fresh
  fuzz programs (seed 1414).
- Linux strict C++17 compilation passed with `-Wall -Wextra -Werror -pedantic`.
  The lower-load release run repeated all 500 checks with identical cycle
results: slowest invocation 1.38 seconds, suite wall 63.5 seconds. To assess
compiler overhead without comparing unrelated loads, a separate run alternated
apex/vector directly on the 100 default-machine inputs, one at a time with
strict self-checks. Median wall time was 98.43 / 98.32 ms; maximum 1.041 / 0.918
seconds, sums 16.239 / 15.952 seconds. These noisy observations do not establish
a controlled compiler-throughput speedup. They show no material added overhead
in this paired run. Data: `results/vector-compile-times.json`.

Generated 100k straight/loop inputs finish in 3.11/11.20 seconds in the Linux
  ARM VM, using about 119/177 MiB peak RSS. This is not the judge's x86 CPU.
  Mac times under concurrent work were 4.01/11.76 seconds. Result cycles are
  170,026 / 376,633 versus original 686,591 / 558,161 on default inputs.
  Both generated programs passed 16 complete official observable-state checks.
  Repeated Linux output is identical on the loop case; Mac and Linux may choose
  different legal allocations (Linux loop score 376,630).

The historical `optimizer-next` evidence follows for comparison.

---

# optimizer-next validation

Compared with the separately built `optimizer-best` snapshot `02773ad`.
Both versions used the same kit, programs, inputs and machine descriptions.
No changes were made to the active `optimizer-best` or `main` worktrees.

Sample-input cycles over 100 programs per machine:

| Machine | 02773ad | optimizer-next |
|---|---:|---:|
| default | 10,185 | 10,178 |
| few_registers | 15,937 | 15,931 |
| no_fused | 13,103 | 13,051 |
| slow_memory | 15,161 | 15,155 |
| wide_fast | 7,901 | 7,785 |

Across 500 pairs: 11 faster, 489 unchanged, zero slower. Per-pair cycles are in
`results/next-sample-cycles.json`. Total-cycle ratios and per-program geometric
means measure different things and should not be interchanged.

Additional randomized-input scoring uses eight inputs per program starting at
offset 40 in the kit generator. This skips its fixed edge-value prefix; changing
the seed alone does not randomize that prefix. These inputs are not used by the
optimizer to select candidates.

| Machine | Random cycles before | Random cycles after | Geometric speedup before | After |
|---|---:|---:|---:|---:|
| default | 59,097 | 59,041 | 6.716 | 6.745 |
| few_registers | 94,882 | 94,834 | 9.783 | 9.818 |
| no_fused | 74,544 | 74,268 | 5.936 | 6.006 |
| slow_memory | 91,625 | 91,577 | 5.767 | 5.783 |
| wide_fast | 44,680 | 44,196 | 4.788 | 4.851 |

Reproduce with `python3 tools/bench.py --machines all --random 50 --score-offset 40`.
Set `KOPT_EXEC` to an absolute baseline wrapper path to measure another checkout.
Sample and randomized runs each passed all 500 validity/equivalence/determinism
checks. Hidden-test performance remains unknown.

Focused evidence:

- Signed power-of-two pass: 316,224 results compared with a separate integer
  oracle and the official interpreter, including INT_MIN and negative divisors.
- Quotient/remainder and block/suffix sharing: 4,949 direct comparisons with
  the official interpreter; the pass driver bypasses optimizer fallback.
- Static semantic review and 25,856 sanitizer-enabled suffix-sharing comparisons
  covered loops, duplicate branch targets and generated-label collisions.
- 34 saved regressions; 50 smoke program/machine pairs and four negative controls.
- Dense-live-set tests: 900, 2,000 and 15,000 simultaneous values, checked against
  a separate arithmetic oracle.
- Linux strict C++17 build (`-Wall -Wextra -Werror -pedantic`) passed, with a
  1,000-input signed-arithmetic equivalence check.
- Generated ~100,000-instruction straight-line and loop programs finished in
  0.739 s and 3.174 s on the M4 during concurrent tests. This is not a prediction
  of the judge CPU's runtime.

Every optimization remains subject to exact behavior, deterministic output and
the contest time limits. No code-size or latency heuristic alone proves a speedup.

Frozen-build campaign: 2,000 stronger fuzz programs (seed 1205), 1,000 metamorphic
programs (seed 1206), and 300 ASan/UBSan fuzz programs (seed 1204) all passed.
