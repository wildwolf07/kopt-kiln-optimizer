# Submission release validation — 13 November

The release starts from main `2400069` and retains all previous algorithms.
It adds a final bounded instruction-window search and reduces redundant
compiler work. It also fixes three memory-safety classes: unchecked matrix
coefficients, a stale block reference during store sinking, and unreachable
raw registers entering the SSA forwarding table. Both matrix preparers now
skip unreachable blocks. The launcher produces machine-legal recovery output,
and validation rejects recovery diagnostics.

| Machine | Main sample | Release sample | Main held-out | Release held-out | Release held-out geo |
|---|---:|---:|---:|---:|---:|
| default | 8,529 | 8,525 | 48,985 | 48,950 | 7.790 |
| few_registers | 13,589 | 13,589 | 81,157 | 81,153 | 11.560 |
| no_fused | 10,386 | 10,379 | 60,211 | 60,077 | 7.093 |
| slow_memory | 11,993 | 11,987 | 71,961 | 71,894 | 6.842 |
| wide_fast | 6,625 | 6,625 | 37,608 | 37,606 | 5.472 |

Each frozen compiler passed all 500 public pairs with the official interpreter,
100 generated inputs, offset-40 held-out scoring and repeat determinism.
The Mac/Clang and Linux/ARM GCC11 builds produced byte-identical public outputs.
A separate paired comparison against the baseline also passed all 500 pairs.

Held-out changes: 19 faster, 480 equal, one slower by one cycle. Sample changes:
seven faster, 492 equal, one slower by one cycle. The regression is
`dead_mod_in_loop` on no_fused: sample31→32, held-out351→352. All five
aggregate held-out totals improve. The search uses fixed training inputs;
these results do not imply dominance on every input distribution.

| Kernel and machine | Held-out before → after |
|---|---:|
| rle_encode, no_fused | 835 → 777 |
| histogram, slow_memory | 2,062 → 2,022 |
| matvec8, no_fused | 2,140 → 2,106 |
| alias_stores, default | 1,416 → 1,388 |
| merge_sorted, no_fused | 1,797 → 1,778 |

Final frozen gates passed:

- 6,000 strict fuzz programs on Mac, seed131311, and 6,000 on Linux, seed131312.
- 1,000 further fuzz programs under ASan/UBSan, seed131315.
- 48 saved regressions on each compiler, 500 metamorphic programs seed131313,
  100 mutations seed131314 (8,545 cycles both versions), smoke50+4negative controls.
- 1,200 unseen-machine pairs: zero slower-than-input outputs, zero wrapper
  fallbacks; maximum observed wall time0.93s.
- All 30 root suites with unchanged production, test and binary hashes.
- Direct window search:320fixtures,4,040callback candidates,52,320 independent
  official comparisons. Direct final safety:11fixtures,480 official plus480
  local comparisons; the same480 local comparisons passed under sanitizers.
- Bit-idiom emission: four loop forms and four lowering modes, 4,096
  independent scalar plus 4,096 official comparisons. Explicit instruction
  creation order removes a target-dependent argument-evaluation choice that
  previously cost nine sample cycles on hamming_dist/few_registers.
- Cache enabled/disabled:26 byte-identical output pairs and1,281 exact-score
  hits, including active incorrect profiles and large-program bypass.
- Recovery:44 injected process failures and4,224 official comparisons,
  including disabled fused operations, highest valid register names, effects,
  traps, exact preservation of legal input, and repeat determinism.

The first fresh fuzz run found two exits at seed131301 cases520/2557.
ASan identified unreachable raw-register indices used as SSA values. Both
saved cases and direct empty-SSA fixtures pass after the fix. Separate old-source
regressions reproduced ASan use-after-free and UBSan coefficient overflow;
the patched fixtures pass. Earlier failed runs are not claimed as successful
validation of the final build.

Maximum public compiler CPU time was 0.942s on Mac and 1.113s on the Linux VM; maximum observed wall times were 1.130s and 1.121s.

The final stress programs contain100,000 straight-line and102,567 loop
instructions. Linux first/repeat wall times were 2.06/2.14s and 9.70/9.53s.
Mac first/repeat times were 1.83/1.92s and 6.97/6.61s. Every large output passed
three independent official comparisons and repeat determinism. Both compilers'
large outputs remain byte-identical to their respective parent-release baseline. The
large loop's instruction/register layouts differ between compilers; cross-
compiler byte identity is claimed only for the500 public pairs.

`results/release-validation.json` records the frozen hashes and checks;
`release-benchmark-report.json` contains every public row and compiler timing;
`release-output-manifest.json` contains all500 output hashes. CI additionally
runs the pinned official oracle and large tests on Ubuntu22.04/g++11 x86-64.
Its final status must be checked before submission.

---

# optimizer-boost4 validation

This candidate starts from main `495f87b`. Matrix-product recipes now accept
up to 16 columns and also run at reduced search effort, which long-running
products receive because of their training cost. Public bench results are
unchanged on all 500 pairs (the public matmul4 already used the recipe).

Generated products C[i][j] = sum_k A[i][k] * B[k][j] (zero inputs; the timing
does not depend on data), cycles before → after:

| N M P | default | few_registers | no_fused | slow_memory | wide_fast |
|---|---:|---:|---:|---:|---:|
| 4 4 4 | 175 → 175 | 453 → 453 | 426 → 426 | 363 → 363 | 73 → 73 |
| 8 8 8 | 2,313 → 2,313 | 4,044 → 4,044 | 4,889 → 4,889 | 3,742 → 3,742 | 1,647 → 1,647 |
| 6 12 6 | 2,927 → 2,401 | 8,542 → 5,685 | 3,220 → 3,220 | 4,837 → 3,515 | 1,461 → 1,461 |
| 3 5 7 | 514 → 514 | 1,206 → 1,206 | 841 → 841 | 823 → 823 | 278 → 278 |
| 16 16 16 | 47,848 → 20,433 | 79,306 → 41,121 | 53,305 → 40,945 | 70,738 → 41,545 | 23,407 → 19,855 |
| 8 16 4 | 2,650 → 2,650 | 4,071 → 4,071 | 4,203 → 4,203 | 5,934 → 4,552 | 1,826 → 1,826 |
| 2 16 16 | 3,381 → 2,555 | 6,884 → 5,141 | 5,309 → 5,119 | 5,429 → 5,127 | 2,029 → 2,029 |

No size got slower. Compile CPU for the 16x16x16 case stayed at 0.14-0.30 s.

# optimizer-boost2 validation

This candidate starts from main `58c5a3a` and adds structurally proven
matrix-product recipes (see DESIGN.md). They are extra candidates; earlier
search paths and seeds are unchanged.

| Machine | Main sample | Boost2 sample | Main held-out | Boost2 held-out | Main held-out geo | Boost2 held-out geo |
|---|---:|---:|---:|---:|---:|---:|
| default | 8,670 | 8,529 | 50,113 | 48,985 | 7.742 | 7.787 |
| few_registers | 13,731 | 13,589 | 82,293 | 81,157 | 11.528 | 11.559 |
| no_fused | 10,386 | 10,386 | 60,211 | 60,211 | 7.083 | 7.083 |
| slow_memory | 12,210 | 11,993 | 73,697 | 71,961 | 6.805 | 6.837 |
| wide_fast | 6,763 | 6,625 | 38,712 | 37,608 | 5.414 | 5.472 |

Paired on the same 500 public pairs (random 30, score offset 40): 4 pairs
improve in held-out cycles, 0 get worse and 496 tie.

| Kernel and machine | Sample main → boost2 | Held-out main → boost2 |
|---|---:|---:|
| matmul4, slow_memory | 580 → 363 | 4,640 → 2,904 |
| matmul4, few_registers | 595 → 453 | 4,760 → 3,624 |
| matmul4, default | 316 → 175 | 2,528 → 1,400 |
| matmul4, wide_fast | 211 → 73 | 1,688 → 584 |

On no_fused (32-instruction cache) the earlier rolled candidates still win.
The Linux g++ 15 build produces byte-identical outputs on all 500 pairs and
the same cycle totals.

# optimizer-boost validation

This candidate starts from main `1689c93` and adds final-only candidate
stages: boolean-tree formulas, select identity arms and canonical sign forms;
partially dead store sinking; join hoisting above effectful branches (0.5%
selection margin); and register-touch polishing for programs that name more
registers than the machine keeps. Earlier search paths and seeds are unchanged.

| Machine | Main sample | Boost sample | Main held-out | Boost held-out | Main held-out geo | Boost held-out geo |
|---|---:|---:|---:|---:|---:|---:|
| default | 8,700 | 8,670 | 50,229 | 50,113 | 7.652 | 7.742 |
| few_registers | 13,846 | 13,731 | 82,938 | 82,293 | 11.327 | 11.528 |
| no_fused | 10,403 | 10,386 | 60,317 | 60,211 | 7.012 | 7.083 |
| slow_memory | 12,372 | 12,210 | 74,790 | 73,697 | 6.701 | 6.805 |
| wide_fast | 6,809 | 6,763 | 38,936 | 38,712 | 5.342 | 5.414 |

Paired against main on the same 500 public pairs (random 30, score offset 40):
52 pairs improve in held-out cycles, 0 get worse and 448 tie.
Largest held-out improvements:

| Kernel and machine | Sample main → boost | Held-out main → boost |
|---|---:|---:|
| matmul4, slow_memory | 630 → 580 | 5,040 → 4,640 |
| paren_depth, few_registers | 504 → 458 | 3,224 → 2,968 |
| hamming_dist, slow_memory | 167 → 146 | 1,542 → 1,324 |
| crc_bitwise, few_registers | 327 → 300 | 1,824 → 1,674 |
| poly_mac, few_registers | 36 → 23 | 288 → 184 |
| sensor_threshold, wide_fast | 79 → 68 | 727 → 640 |
| histogram, slow_memory | 434 → 419 | 2,136 → 2,062 |
| redundant_loads, slow_memory | 101 → 92 | 1,221 → 1,147 |
| branchy_select, slow_memory | 264 → 248 | 1,536 → 1,477 |
| count_above, few_registers | 182 → 174 | 1,190 → 1,142 |
| run_count, slow_memory | 133 → 128 | 1,222 → 1,175 |
| array_max, slow_memory | 123 → 108 | 1,086 → 1,040 |
| sensor_threshold, no_fused | 93 → 90 | 703 → 657 |
| conv_mac, wide_fast | 120 → 105 | 522 → 484 |

A GCC 15 build exposed a compiler difference in aggregate initialization of
the formula table (entries left zeroed); the table is now initialized
explicitly. Gates for this branch therefore also run on a Linux g++ binary:
bench, fuzzing and regressions, plus byte-identical outputs to the macOS
clang build on all 500 public pairs.

# optimizer-matrix validation

This candidate starts from main `9316fa7`, includes the validated packed
counter pass `64abe81`, and adds select factoring and paired-row matrix/vector
reuse. Both new stages append alternatives after the earlier searches.

| Machine | Packed sample | Matrix sample | Packed held-out | Matrix held-out | Matrix held-out geo |
|---|---:|---:|---:|---:|---:|
| default | 8,712 | 8,700 | 50,290 | 50,229 | 7.652 |
| few_registers | 13,894 | 13,846 | 83,198 | 82,938 | 11.327 |
| no_fused | 10,427 | 10,403 | 60,447 | 60,317 | 7.012 |
| slow_memory | 12,376 | 12,372 | 75,567 | 74,790 | 6.701 |
| wide_fast | 6,814 | 6,809 | 38,965 | 38,936 | 5.342 |

All 500 public pairs passed strict candidate checks, sample plus 100 generated
inputs, feature checks and repeat determinism. Six pairs improve and 494 tie
in both sample and held-out cycles. The changes comprise select factoring on
`branchy_select` for all five machines, and paired-row reuse on `matvec8`
for slow_memory.

| Kernel and machine | Sample before → after | Held-out before → after |
|---|---:|---:|
| branchy_select, default | 159 → 147 | 890 → 829 |
| branchy_select, few_registers | 399 → 351 | 2,200 → 1,940 |
| branchy_select, no_fused | 171 → 147 | 952 → 822 |
| branchy_select, slow_memory | 266 → 264 | 1,551 → 1,536 |
| branchy_select, wide_fast | 95 → 90 | 597 → 568 |
| matvec8, slow_memory | 99 → 97 | 3,132 → 2,370 |

The matrix-vector kernel improved for all eight reachable row counts on
slow_memory. For 1 through 8 rows, the before/after cycles were
99/97, 189/141, 279/230, 369/274, 459/363, 549/407, 639/496 and 729/540.

Eight generated matrix/vector kernels varied widths from 2 through 16,
row strides, memory bases and return values. Forty pairs across the five
machines passed behavior checks. Every emitted row-pair candidate was checked,
for 39,543 independent official comparisons. Fourteen timing pairs improve,
23 tie and three regress. Aggregate totals improve on default, no_fused,
slow_memory and wide_fast, and tie on few_registers.

| Generated machine | Before cycles | After cycles |
|---|---:|---:|
| default | 38,955 | 36,282 |
| few_registers | 55,140 | 55,140 |
| no_fused | 55,101 | 53,142 |
| slow_memory | 66,765 | 58,497 |
| wide_fast | 20,220 | 19,770 |

Generated timing regressions were 1,458 → 1,464 for width 2 on no_fused,
4,104 → 4,116 for width 4 on slow_memory, and 2,730 → 2,904 for width 8
on wide_fast. The candidate ranking uses fixed training inputs, so different
trip-count distributions can favor a different version.

Maximum compiler CPU time across the public suite was 1.058 s on the Mac,
with a maximum observed parallel wall time of 4.17 s. The selected cases on
one pinned Linux VM CPU completed within 1.43 s wall time. The 100k-instruction
straight and loop stress cases took 3.05 and 9.14 s and produced byte-identical
output to the validated packed baseline.

The frozen combined build passed 3,000 strict fuzz programs, 500 metamorphic
programs, 46 regressions, 100 mutation cases with equal cycle totals, and
300 further fuzz programs under ASan and UBSan. Smoke checks passed 50 pairs
and four negative controls. All 1,200 unseen-machine checks passed with zero
outputs slower than the input and zero wrapper fallbacks.

The paired-row module separately passed 84,960 independent official
comparisons over 376 proof fixtures and 122,560 more over 500 generated
sources. Its sanitizer checks covered another 37,440 local comparisons.
Both new proof suites have kit-free modes for Ubuntu 22.04/g++11 CI.
All 22 root test suites passed against unchanged production source and binary
hashes. Select factoring passed 56,576 official comparisons over 64 fixtures
and four lowerings, plus 71,936 local comparisons. The complete manifest is
`results/matrix-validation.json`.

---

# optimizer-packed validation

The packed-counter pass from `2541b59` is applied on main `9316fa7`, which
already includes cross-iteration load pipelining and monotone loop unswitching.
Both binaries were built independently. The candidate passed 500 strict
program and machine checks with 100 generated inputs per pair and repeat
determinism. Held-out scoring starts at offset 40.

| Machine | Main sample | Packed sample | Main held-out | Packed held-out | Packed held-out geo |
|---|---:|---:|---:|---:|---:|
| default | 8,712 | 8,712 | 50,290 | 50,290 | 7.646 |
| few_registers | 13,894 | 13,894 | 83,198 | 83,198 | 11.313 |
| no_fused | 10,427 | 10,427 | 60,447 | 60,447 | 7.002 |
| slow_memory | 12,529 | 12,376 | 76,088 | 75,567 | 6.681 |
| wide_fast | 6,814 | 6,814 | 38,965 | 38,965 | 5.339 |

Histogram on slow_memory was the sole cycle change against this baseline.
It ran in 434 instead of 587 sample cycles and 2,136 instead of 2,657 held-out
cycles. The packed pass accumulates deltas for 2, 4, or 8 bins in at most two
registers. It proves a bounded trip count, disjoint valid memory ranges and
absence of observable effects inside the loop before deferring the writes.

Eight generated kernels varied bin counts, addresses, trip bounds, starting
bin values and exit behavior. Across all five machines, 25 of 40 pairs
improved and 15 tied. All 1,359 emitted packed candidates passed 54,360
independent interpreter comparisons. The direct pass test separately passed
3,520 comparisons across 22 proof fixtures.

The standalone pass's sweep over all 64 histogram lengths found 58 faster
lengths and six slower short lengths. The empty case rose from 8 to 60
cycles due to fixed writeback. The compiler selects candidates on aggregate
simulated cycles.

Maximum compiler CPU time in the combined public run was 0.932 seconds on
the Mac. On one pinned Linux VM CPU, selected normal cases finished in
under two seconds and the two 100k-instruction stress inputs completed in
2.07 and 6.73 seconds. The large outputs were byte-identical to the earlier
baseline, matching main's large-input equivalence check.

The combined build passed 3,000 strict fuzz programs, 500 metamorphic
programs, 46 saved regressions, 100 mutation cases with equal cycle totals,
and all 20 root test suites. The 1,200 unseen-machine cases reported zero
outputs slower than the input and zero wrapper fallbacks. The packed pass
also passed 3,520 local interpreter comparisons under ASan and UBSan.
CI runs these proof and writeback checks without requiring the official kit.
Full measurements and source hashes are in `results/packed-validation.json`.

---

# optimizer-sieve validation

Based on main `64ce095`. Adds cross-iteration load pipelining (the next
iteration's first load is read before the rest of the iteration, including
inner loops whose stores provably miss it) as a side candidate trajectory, and
monotone loop unswitching as three extra loop plans.

| Machine | Main sample | Sieve sample | Main held-out | Sieve held-out | Main held-out geo | Sieve held-out geo |
|---|---:|---:|---:|---:|---:|---:|
| default | 8,973 | 8,712 | 52,610 | 50,290 | 7.453 | 7.646 |
| few_registers | 13,978 | 13,894 | 84,004 | 83,198 | 11.236 | 11.313 |
| no_fused | 10,847 | 10,427 | 63,098 | 60,447 | 6.798 | 7.002 |
| slow_memory | 13,351 | 12,529 | 80,350 | 76,088 | 6.505 | 6.667 |
| wide_fast | 6,860 | 6,814 | 39,442 | 38,965 | 5.295 | 5.339 |

Held-out (offset 40, eight inputs per pair): 58 pairs faster, 440 equal, two
slower (array_min and array_max on slow_memory, 1,064 to 1,086 each: their
training cycles improve, held-out does not). Six sample inputs are slower, the
largest dfa_dispatch on default (214 to 278). Largest gains: sieve on
slow_memory 3,923 to 2,669, paren_depth on slow_memory, adler32, fnv_hash,
array_min/max on no_fused, word_count, prefix_sum, merge_sorted.

Checks on the final binary: 500/500 bench pairs (sample plus 30 generated
inputs, repeat determinism); 3,000 strict fuzz programs (seed 31301); 500
metamorphic programs; 46 regressions; 50 smoke pairs plus four negative
controls; mutation invariance; 1,200 unseen-machine cases with no output
slower than its input and no fallback; all test suites, including
`tests/pipeline_across.py` (300 generated loop nests, 746,370 official
comparisons of every dumped candidate) and `tests/monotone_unswitch.py` (300
programs, 529,320 comparisons). Deliberately broken builds of either pass fail
these tests. Worst compiler CPU time 1.13 s (main 0.96 s); 100k-instruction
programs give the same output in the same time. Linux g++ strict build has no
warnings and produces byte-identical output on all 500 pairs.

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
