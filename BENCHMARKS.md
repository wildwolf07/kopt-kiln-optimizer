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
