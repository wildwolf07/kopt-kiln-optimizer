# kopt design

The implementation is C++17 and uses only the standard library. `kir.*` parses
and prints KIR; `sim.*` interprets KIR and counts cycles; `ssa.cpp` and `cfg.*`
construct and analyze SSA; `passes.*` optimizes values; `loops.*` transforms
register-form control flow; `backend.*` allocates registers and schedules;
`optimizer.cpp` constructs, measures and checks candidates.

Sources: the official `KIR_SPEC.md` and `kirlib.py` supplied with COMP10; Cytron
et al. for SSA, Cooper–Harvey–Kennedy for dominators, Wegman–Zadeck for SCCP,
Chaitin and Briggs–Cooper–Torczon for allocation/coalescing, and standard LICM,
value-range and list-scheduling techniques. For the scheduling/allocation
tradeoff, see Shobaki, Shaw and Riddle,
[Preallocation instruction scheduling with register pressure minimization](https://scholars.csus.edu/esploro/outputs/journalArticle/Preallocation-instruction-scheduling-with-register-pressure/99257888392901671).
The interpreter, timing model and fixed-seed generators are ports of the kit,
as permitted. No optimizer framework, solver, or external optimizer code is
used. Candidate decisions do not depend on filenames, hashes, the network or
the wall clock.

## 1. What is implemented

Analyses: dominators/frontiers, natural loops and irreducible regions,
path-based liveness, recurrence SCCs, induction ranges, signed value-range
propagation with branch refinement, and bounded trip-count reasoning.

SSA transformations: SCCP, copy/algebraic simplification, linear combinations,
GVN, load forwarding, DCE, dead stores, CFG cleanup, LICM, induction strength
reduction, reassociation (sums and min/max chains), Horner-chain splitting,
counting-select rewriting, safe speculation, fusion and if-conversion. A
late candidate stage adds load phis (loads below merges become phis of values
every predecessor already knows) and store selects (a conditional store whose
old value is known becomes an unconditional store of a select).

Register-form transformations: rotation, ordinary unrolling (innermost loops,
or whole top-level loop nests), peeling,
splitting of multi-entry (irreducible) cycles, repeated peeling of short
constant-trip loop nests ("flatten"), threading, invariant-condition
unswitching and two complementary counted-loop
recognizers. One handles rotated latch tests, invariant constant/register steps
and optional remainder chains; the other handles exact two-block pre-test loops
with a positive constant step and an explicit signed-underflow guard.

Back end: parallel-copy SSA destruction, unlimited-name and K-name allocation,
copy-related spill webs, bounded-distance reload reuse, pre/post-allocation
scheduling, optional legal color spreading, loop-based layout and trace-derived
layout alternatives, copying of tiny return blocks into jumping predecessors,
and removal of spill stores that are never reloaded. SSA memory facts allow the pre-allocation scheduler to
separate proven-disjoint accesses and recognize proven-safe loads.

The input is canonicalized by CFG traversal and first-appearance register
renaming. This reduces accidental dependence on shuffled blocks and register
numbers. Multiple candidates are evaluated on fixed training executions, and a
winning candidate is checked on additional inputs before being written.

Missing or partial: no software pipelining, unrestricted cross-block scheduling,
full partial-redundancy elimination or general alias analysis. Counted-loop
recognition is deliberately restricted. The profile only steers which inputs
rank candidates (section 6). Finite self-checking is not a proof of equivalence.

## 2. Pass order

1. Canonicalize reachable block order/register names; expand unsupported fused
   instructions when necessary. Interpret the input on fixed training/check inputs.
2. Build SSA, remove obvious CFG clutter, then run up to four cleanup rounds:
   induction ranges, signed VRP, SCCP, linear combining, CFG cleanup,
   simplification, GVN, simplification, DCE, dead stores, CFG cleanup and LICM.
   Above 20,000 instructions VRP runs only in the first round.
3. Run strength reduction, reassociation, Horner splitting, optional speculation,
   machine-dependent fusion, if-conversion and counting-select rewriting. Simplify again; combine newly exposed sums and run
   cleanup/fusion once more when useful.
4. Before destruction, optionally record SSA memory safety/disjointness facts.
   Destroy SSA, optionally pre-schedule on value names, allocate registers,
   remove identity copies, clean the CFG, lay out blocks and post-schedule.
5. Repeat with pass/backend alternatives. The full search uses eight pass flags;
   medium programs get two, large/dense/expensive programs get one. The first
   two phases include register-form loop transforms followed by recompilation.
   Full-effort runs also perform two rounds of threading/peeling on the best
   distinct candidates. Original compact-color and spill choices remain available.
6. For full-effort programs: a flatten chain (split irreducible cycles, peel by
   16, thread, recompile; up to four steps on the best three candidates, under a
   deterministic budget of compiled instructions); a load-phi stage recompiling
   the best three with load phis and return-block copies, with and without store selects; then chain and
   hot-block layout alternatives from up to eight good candidates. Measure them with the exact same cycle model.
7. Sort by training cycles (ties: fewer instructions), then check improving candidates on additional inputs
   until one passes. If none improves and passes, write the original input.

Search effort depends on instruction count (full through 1,000, reduced through
4,000), block/register counts (at most 256 for expanded search), and deterministic
training instruction counts (reduce above 300,000 steps; use one pipeline above
1,000,000). These are structural/execution-count budgets, not elapsed-time tests.
The wrapper has no timed output fallback. Diagnostic timing never selects output.

## 3. Each pass

Here n is instructions/values, b is blocks, E is interference edges, L is loops,
U is an unroll factor, and w=96 is the scheduling window. Bounds below describe
the main work; CFG, phi fan-in and interference density can dominate particular
inputs. Analyses with iteration/path limits abandon deductions when not established.

| Pass | Method and main cost | Correctness obligation |
|---|---|---|
| Canonicalization | Iterative CFG traversal, target remapping, dense register renaming; O(n+b). | Entry stays first; all explicit targets and each register identity are preserved. |
| SSA | Dominators/frontiers, live phi placement and renaming; depends on CFG/frontiers and inserted phis. | Preserve def-use relations and incoming edges; undefined reads are zero. |
| IV ranges | Recognize bounded positive-step recurrences; loop/phi analysis. | Continuing paths must pass the bound test without wrap. For a post-increment test, **init+step must also stay below 2^31**. |
| Signed VRP | Monotone interval growth, widening to program thresholds, capped iteration and narrowing. At most 100 solving rounds; at most 192 thresholds. | Arithmetic that may wrap returns a conservative full interval. Only settled solutions are used. Branch facts apply on guarded paths/phi edges. |
| Trip caps | Enumerate at most 48 acyclic header-to-backedge paths, each bounded in length; follow constant phi changes. | A bounded, nondecreasing measure must grow on every path. Unknown changes, cycles and excessive path counts reject the proof. |
| SCCP | Executable-edge/value lattice worklists; near-linear for sparse graphs. | Replace only constants on executable paths; never fold a trapping division. |
| Simplification | Bounded rounds of exact identities and range-based comparisons. | KIR wraps modulo 2^32. Signed division-to-shift needs nonnegative operands; shifts mask their amount. |
| Linear combinations | Collect add/sub/mul/shift trees with restricted shared uses; O(n) for bounded trees. | Distributivity and cancellation hold modulo 2^32. |
| GVN/forwarding | Dominator-scoped expression hashing and alias-aware memory tables; expected O(n), with memory/phi scans. | Reused computation dominates its use; intervening possibly aliasing stores invalidate knowledge. |
| DCE | Rooted mark/sweep; O(n+uses). | Stores, volatile effects, terminators and possibly trapping work remain observable. |
| Dead stores | Reverse block scans with bounded-address/alias reasoning. | No read, trap or effect may expose the overwritten value. |
| CFG cleanup | Reachability, branch folding, merging and jump threading. | Keep the same selected execution paths/instructions. |
| LICM | Move invariant pure/safe work to preheaders; roughly O(n·L). | Hoisted operations cannot introduce traps. Divisor nonzero facts must hold on the preheader edge; loads also need valid addresses and no aliasing loop store. |
| Strength reduction | Replace i*c by a coupled recurrence; O(n) scanning plus CFG work. | The recurrence uses wrapping arithmetic. Save destination IDs before vector insertion so shifted instructions cannot be mistaken for the replacement. |
| Reassociation | Shorten loop-carried addition chains; graph/SCC work. | Wrapping addition is associative and commutative. |
| Sum balancing | In the load-phi stage's store-select variant, a chain of single-use adds outside loop recurrences with 4+ terms becomes a balanced tree when that cuts its depth by 2 or more. | 32-bit addition wraps, so it is associative and commutative. |
| Closed-form loops | A loop that exits only at its header test i < n (n invariant, i = phi(i0, i+1)), with a pure body whose other header phis are accumulators s' = s + c0 + c1*i + c2*i^2 (invariant c), is replaced by its exit values computed before it: T = (i0 < n) ? n - i0 : 0, S1 = T(T-1)/2 (halve the even factor), S2 = S1*(2T-1)*inv(3) mod 2^32. | The sums are exact integer identities, and all of them hold modulo 2^32. i + 1 cannot wrap because i < n <= INT_MAX. Pure bodies have no effects or traps to keep. Loop values may not be used outside except the header phis. |
| Dead scratch stores | A store to a constant scratch word (3072..4095) that no load can read is removed. | The scratch region is not observable; a constant in-range address cannot trap. |
| Min/max chains | In a block, a loop-carried chain of select(lt(p,q),q,p) (max) or select(lt(p,q),p,q) (min) becomes one carried step plus a balanced tree of the other inputs. | Signed min/max are associative and commutative and return one of their inputs, so every grouping gives the same bits. Inner nodes must have no other uses. |
| Horner splitting | A chain h' = h*x + c of n >= 6 steps becomes k=2 chains in x^2 (k=4 in x^4 with 16+ registers), combined at the end. Values it creates are never split again. | Wrapping arithmetic is a commutative ring, so any regrouping of the polynomial is exact. Inner products and sums must be single-use. |
| Counting selects | select(c, a, a+1) -> a + eq(c,0); select(c, a+1, a) -> a + (c != 0) (c itself when its range is 0..1). | Exact case analysis on c; the test leaves the a chain. |
| Speculation | Bounded pure-work hoisting across eligible branches. A load whose address is proven in memory only on its own path (signed VRP plus branch facts) moves up as `and t, a, 4095; load t`, and may cross stores of the arm that provably touch other words. | Extra-path execution must have no observable effect and cannot trap. The masked address equals the original wherever the original load runs, so it reads the same word; elsewhere the value is unused. |
| Fusion | Select mac/addsh patterns using machine availability/costs; O(n). | Preserve low-32-bit arithmetic; unavailable instructions never reach output. Reduction fusion is a candidate choice. |
| If-conversion | Inline small safe arms and replace joins with select. | Both evaluated arms must be pure and non-trapping. |
| Load phis | For a load, walk up single-predecessor blocks to the nearest merge; if every predecessor's chain ends with a known value for the same address and no possibly aliasing store follows it, insert a phi there. | Each path already accessed the word, so no trap is lost. The address is constant or defined in a block strictly dominating the merge, so it names the same word on every edge, back edges included. |
| May-alias forwarding | In the load-phi stage, a load whose address was accessed earlier in the block, with at most two possibly aliasing stores since, becomes select(A == Bi, wi, ...) over those stores, newest last. | Exact case analysis on address equality; volatile accesses stop the search; the earlier access rules out a lost trap. |
| Store selects | Hoist a branch arm's leading pure work and stores (pairwise disjoint addresses defined above the branch) and store select(c, new, old). If the arm is then empty, merge its phi inputs into selects and remove it. | The old value must be known at the branch; the skipped path rewrites the same value into an already accessed word. Loads, volatile operations and possibly trapping work stop the hoisted run. |
| Return-block copies | In the load-phi stage, a return block (at most 32 instructions) gets a private copy for each predecessor whose phi inputs are all constants, within 512 new instructions; folding then shrinks the copy. | The block ends in ret, so its values have no other users; each path executes the same instructions with the same values. |
| Irreducible splitting | Tarjan SCCs; each extra entry of a multi-entry region gets its own copy of the region within a code budget. | Copying blocks and redirecting edges in register form keeps every execution's instruction sequence. |
| SSA destruction | Edge parallel copies, critical-edge splitting, temporary cycle breaking. | Read all copy sources before overwriting them. |
| Unlimited allocation | Interference/coalescing and greedy coloring; O(n+E) plus set work. | Simultaneously live values cannot share a name. On two million edge insertion attempts, use distinct names rather than build an unbounded dense graph. |
| K-name allocation | Conservative coalescing, ordered-set simplify/select, scratch spills and retry. | Scratch is used only if original accesses are proven below 3072. Copy-related spill webs share a word only when legal. |
| Reload reuse | Retain fresh load/result temporaries for nearby uses in a block. | Cached slot contents must still match; definitions/stores update or invalidate the entry. Failed retention retries without reuse. |
| Color spreading | Try additional interference-legal colors within a bounded hardware-name preference set. | Coloring legality is unchanged. Unlimited allocation may still need more names; the preference cap is not a semantic register limit. |
| Scheduling | List scheduling in fixed windows, before/after allocation; O(n·w). | Preserve RAW/WAR/WAW, alias, trap and effect constraints. SSA memory ordinals must still match; otherwise facts are disabled. |
| Rotation/unroll/peel/thread | Duplicate/register-form blocks and redirect edges; O(n·U) within code-growth budgets. | Each new path executes the same original instructions, except tests established redundant. |
| Latch counted groups | Guard the positive step, safe bound subtraction and enough remaining iterations; retain scalar fallback/remainder. | No skipped latch exit test may be false; preserve comparison writes and the body/effect order. Variable steps have runtime validity guards. |
| Header counted groups | Let D=(U-1)s. Guard bound >= INT_MIN+D, then test i < bound-D per group. | Intermediate increments cannot wrap before a skipped test. Each copy writes comparison=1. Keep the final possibly wrapping increment and original scalar exit test. |
| Unswitching | Clone a loop and dispatch on a register the loop never writes. | Reading the invariant early cannot trap; guarded body operations stay on their selected paths and in order. |
| Return copying | A jump to a return block of at most 3 instructions takes a copy of it; a branch to two identical such blocks becomes a jump; mov a,s; ret a becomes ret s; unreachable blocks are dropped. | Text copy of the executed instructions minus one jump. |
| Unread spill stores | Remove stores to scratch spill words that no load reads (K-name allocation only). | All original addresses were proven below 3072, so only spill code touches scratch. |
| Initial/trace layout | Loop-frequency chains; additional hot-block/edge layouts from fixed traces, O(T+b²). | Entry remains first; explicit targets are remapped. Prediction errors affect speed, not semantics. |

## 4. The machine

All machine keys are parsed. K and spill penalties affect allocation; latencies,
issue width and memory ports affect scheduling; fused availability/costs affect
instruction choice. Branch penalties influence if-conversion/layout, and code
size/cache penalties constrain unrolling and are included in simulation.

The unlimited allocator may intentionally use more than K names and pay LRU
penalties. The K-name allocator trades those penalties for explicit scratch
loads/stores. Compact and spread-color alternatives can differ in false
register dependencies, so they are compared rather than assumed faster.

## 5. Keeping the behaviour

The contract is returned value or trap kind/code, ordered volatile log, and words
0–3071 at termination/trap. Source operands are read before destinations change.
All value arithmetic follows KIR's wrapping and signed-operation rules.

Removal and motion require proof about traps and effects. Scheduling keeps
memory aliases ordered, keeps observable effects ordered, prevents potentially
trapping work from crossing effects, and preserves ordering between different
possible trap kinds. Pre-allocation memory facts are captured on SSA before phi
copies; memory ordinal mismatches or new blocks lose those facts conservatively.

Normal-sized self-checks use 16 typical inputs, 64 generated inputs, another 32,
and literal-derived inputs; programs above 4,000 instructions use fewer check
inputs. Literal-driven cases include source constants and neighbors in arguments,
memory and volatile queues. Original runs that time out are skipped, matching
the reference's allowance. A candidate must match all compared observables.
This is **finite testing**, not a proof; shared interpreter mistakes and rare
control paths remain possible. Independent tests use the unmodified kit.

Permanent regressions cover strength-reduction insertion invalidation, the
first-increment signed-wrap hole, negative fused-shift range analysis,
non-Boolean/sibling/loop facts, volatile effects and prior CFG bugs. Test inputs
stored in `.in` files run in addition to generated cases. Sanitizer builds use
`KOPT_BIN` in the test harness; no sanitizer dependency is required for judging.

Moved code drops its recorded ranges. A value's range may rely on the branch
facts of the block that defines it. Speculation, if-conversion, LICM and store
selects therefore clear the recorded range of every value they move, and later
queries recompute it from the operands. (A fuzz case showed a load hoisted out
of a dead block whose range facts were contradictory.)

## 6. Profiles

The profile only changes which inputs rank the candidates; it never changes
what a candidate is allowed to do.

1. Parse `edge FROM TO COUNT` lines whose labels name blocks of the input
   program. Lines that do not parse or name unknown blocks are ignored. If no
   edge remains (or the program has more than 4,000 instructions), the profile
   is ignored.
2. Run the input program on a fixed pool of 64 inputs (48 typical, 16
   generated) and count its block-to-block edges.
3. Distance of a run to the profile: the sum of |log2(1+run count) -
   log2(1+profile count)| over the profile's edges, plus log2(1+count) for each
   edge the profile does not list.
4. The 8 nearest pool inputs (ties by pool order) replace the second half of
   the 16 timing inputs. The first 8 typical inputs always stay.

When the profile is wrong, half of the ranking still comes from ordinary
inputs, so it can shift the choice but never decide it alone. Every
candidate is still checked on the full input set. Initial layout uses loop
estimates, and the layout candidates use frequencies from our own fixed
inputs. Neither profiles nor sampled runs establish semantic facts.

## 7. Known problems

- The training inputs can favor one candidate over another that would win on an
  unseen input. Some public individual cases regress despite better totals.
- Large/dense/expensive programs receive reduced search. Distinct-name fallback
  bounds graph construction but can leave significant LRU penalties.
- VRP, trip analysis and counted recognition are bounded/conservative. Failed
  recognition or unresolved ranges leave work in the program.
- Scheduling is local except for bounded speculative hoisting. No general
  software pipelining or scheduling across arbitrary joins is implemented.
- Finite self-checking and testing cannot establish universal equivalence.
- Profiles only steer the choice of timing inputs; they are not used for
  layout or spill costs directly.
