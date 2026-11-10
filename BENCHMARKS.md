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
