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
