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
tradeoff, see Shobaki, Shawabkeh and Abu Rmaileh,
[Preallocation instruction scheduling with register pressure minimization](https://scholars.csus.edu/esploro/outputs/journalArticle/Preallocation-instruction-scheduling-with-register-pressure/99257888392901671).
Tree ordering also uses the register-need idea described by Appel and Supowit,
[Generalizations of the Sethi-Ullman algorithm for register allocation](https://collaborate.princeton.edu/en/publications/generalizations-of-the-sethiullman-algorithm-for-register-allocat/).
Our shared-DAG ordering is a heuristic; it does not claim the optimality of a tree algorithm.
Rolling reuse follows the general predictive-commoning idea described in
[GCC's optimization documentation](https://gcc.gnu.org/onlinedocs/gcc/Optimize-Options.html#index-fpredictive-commoning).
Our implementation is independent and restricted to KIR's explicit memory/trap
semantics. Packed counters use bounded fields in the sense of
[Dietz's packed arithmetic notes](https://aggregate.org/SWAR/over.html). Constant-load splitting uses the recomputation tradeoff in Briggs,
Cooper and Torczon, [Rematerialization](https://doi.org/10.1145/143095.143143).
The interpreter, timing model and fixed-seed generators are ports of the kit,
as permitted. No optimizer framework, solver, or external optimizer code is
used. Additional research and experiment notes are in [RESEARCH.md](RESEARCH.md).
Candidate decisions do not depend on filenames, hashes, the network or
the wall clock.

## 1. What is implemented

Analyses: dominators/frontiers, natural loops and irreducible regions,
exact bit-affine symbolic forms,
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
scheduling, pressure-aware forward and backward alternatives, iterative pure-region tree
ordering, optional legal color spreading, loop-based layout and trace-derived
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
5. Repeat with pass/backend alternatives. The full search uses nine pass flags (the ninth adds dispatch tables);
   medium programs get two, large/dense/expensive programs get one. The first
   two phases include register-form loop transforms followed by recompilation.
   Full-effort runs also perform two rounds of threading/peeling on the best
   distinct candidates. Original compact-color and spill choices remain available.
6. For full-effort programs: a flatten chain (split irreducible cycles, peel by
   16, thread, recompile; up to four steps on the best three distinct programs,
   under a deterministic budget of compiled instructions); a load-phi stage
   recompiling the best five distinct programs (at most 8,000 instructions) with load phis and return-block copies, with and without store selects; then pressure-aware scheduling, bounded
   rematerialization, pure-region tree ordering and arithmetic alternatives.
   Then, after those seed-sensitive stages, speculation recompiles of the best
   programs under their own 8,000-instruction budget: full speculation, and a
   loads-only mode with pipelined header loads.
   Finally try chain/hot-block layouts and exact block/suffix sharing from up to eight good candidates.
   A final backward-scheduling stage offers four lowering alternatives for each
   of the best four distinct programs, retaining all earlier candidates. A final
   single-user pure sinking stage offers six additional lowerings per seed.
   For input programs through 1,000 instructions and within the normal CFG/register
   bounds, offer source-derived finite-domain decision and packed-lookup alternatives when proven.
   Their projection proof and exhaustive evaluation are shared within one call.
   Offer up to six final trace layouts on the best three candidates, then an
   independently proven bit-affine rewrite with raw and two backend lowerings.
   A separate final stage offers seven-to-ten-bit finite domains, then bounded
   constant-address load rematerialization. Finally, for original inputs through
   500 instructions, prepare a branch-free store alternative and prove rolling
   load reuse before trying its own 1/2/4/8 unroll factors and loads-only
   scheduling. This stage has a separate 6,000-unit lowering budget, weighted
   three times for K allocation. Earlier searches and seeds are unchanged.
   For inputs through 160 instructions, also try packed counters for bounded
   indexed increments, followed by ordinary and counted unrolling and loads-only
   scheduling. This stage caps recompiled input at 1,600 instructions. It applies
   bottom-up scheduling and a layout alternative to at most two of its own seeds.
   Measure alternatives with the exact same cycle model.
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
| Bit-affine synthesis | For pure input through 1,000 instructions/128 blocks/four parameters, bounded if-conversion and cleanup must leave one RET block without phis (at most 4,000 SSA values). Interpret each bit symbolically as an affine GF(2) form with 128 input coefficients and a separate constant. Emit bias XOR selected matrix columns; one-bit columns with common displacement share masked shifts. At most 32 nonzero columns. | XOR is exact. AND/OR are accepted only for constant, equal or complementary forms; nonlinear products reject. Ripple carry/borrow must remain affine at each accepted step. Shifts use low-five-bit counts, SELECT guards must be provably affine, and every operand definition is available. Original memory/volatile/div/mod/trap instructions reject, even if dead. No sampled inference establishes the matrix. |
| Final layout polishing | At most three distinct winning seeds and two trace layouts each, appended after finite alternatives. O(trace steps + blocks squared) within existing structural limits. | Entry and explicit targets are remapped; all instructions/effects remain unchanged. Every earlier candidate and search trajectory remains available. |
| Packed indexed counts | Recognize one two-block loop with a zero-based unit induction variable, a constant or masked nonnegative bound through 255, and one increment of a masked bin indexed by the only input load. Analyze up to 64 blocks and 1,024 SSA values. Count contributions to two, four, or eight bins in at most two 32-bit words, then add each delta to the original bin on the exit edge. | Both address ranges must be valid, nonwrapping and disjoint. The loop contains only pure arithmetic, two ordinary loads and the bin store, with no other users of the loaded or incremented bin value. The loop has one normal exit and cannot trap, so each bin can be updated there before any subsequent observation. The trip bound prevents carry between packed fields. Final additions preserve 32-bit wrapping. |
| Rolling load reuse | On fresh SSA, require a two-block natural loop with one latch, pure header, and ordinary pure/load/store body. Recognize an exact modular IV+offset recurrence with constant initial IV and nonzero constant step. The first body effect must be the replaced load. Search backward from the latch for the next iteration's same-word load/store, rejecting any intervening potentially aliasing store. Bound to 256 blocks, 10k values, 2,000 instructions and 50k expression visits per call; at most four promotions. | A valid constant initial read gives the first carried value even for a zero-trip loop. On a later iteration the previous successful same-word access establishes both value and address validity. Other constant-offset accesses from the same IV are disjoint modulo 2^32. Header/prefix purity excludes intervening writes or traps; volatile and div/mod body operations reject. All stores and their order remain. |
| Wide finite alternatives | Reuse the fresh-SSA projection proof and original-source exhaustive evaluation with a ten-bit cap, skipping six-bit and smaller domains. Forward/reversed decision and packed representations share one exhaustive run; at most 64 packed words and 1,024 output instructions per candidate. | Key reversal permutes both source-bit descriptors and table indices. All projected classes must return within 20k steps/case and 1M total steps; memory, traps or nontermination reject. |
| Constant-load rematerialization | On fresh SSA, record valid constant-word loads, then per-word store versions and effect barriers. Split 2–8 user sites within the defining block into groups separated by over 16 instructions, up to 64 clones. O(values + instructions + uses + 4096 × blocks), capped at 256 blocks, 20k values and 4,096 instructions. Final hook: at most three seeds, four lowerings, 500 instructions/seed and 2,000 work units. | All uses must keep the same store version and barrier snapshot. Unknown/invalid memory, volatile operations, explicit traps and potentially trapping div/mod reject. No phi/cross-block users; valid repeated reads cannot trap. No GVN afterward to recreate shared long live ranges. |
| Finite-domain specialization | Backward bit-demand analysis on fresh SSA roots all returns/branches and every div/mod divisor. Propagate through phis, literal masks, logical shifts, comparisons and low-bit arithmetic until a fixed point; bounded exact constant folding exposes const/mov masks. Require at most six demanded raw input bits in the original stage; a separate final stage accepts seven through ten. Exhaustively interpret every projection, then emit a reduced decision graph. API caps 256 blocks, eight parameters, 8,000 instructions, 20k steps/case and 1M total steps; normal integration is capped at 1,000 instructions. | Projection preserves demanded result bits and full branch/divisor values. Fixed-point phi rules preserve the argument through loops. Exhaustive execution of the ORIGINAL program establishes return/totality for every equivalence class. Memory/volatile/explicit traps, projected traps and timeouts reject. |
| Packed finite lookup | Pack table offsets from an unsigned base into 1/2/4/8/16/32-bit fields. High key bits select one of at most 16 words (64 in the wide stage); low bits select a field through logical shift and mask. Restore the base with wrapping addition. | Offsets fit their fields, shifts never cross field boundaries, sparse/sign input bits retain their projected positions, fresh names exclude all input parameters. Width 32 bypasses shifts/masks. Decision/original alternatives remain available. |
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
| Reassociation | Shorten loop-carried chains of add, mul, xor, and, or: the carried value joins last, the other terms form their own tree (balanced for the non-add operators) with constants folded; graph/SCC work. | Each of these operators is associative and commutative on 32-bit words (add and mul wrap). |
| Inclusive tests | "br lt(n, i), EXIT, BODY" with i a phi of the block and n defined elsewhere becomes "br lt(i, n+1), BODY, EXIT", the form the counted-loop transformations accept. | Needs n < INT_MAX (range proof) so n+1 does not wrap; then !(n < i) == i < n+1. |
| Sum balancing | In the load-phi stage's store-select variant, a chain of single-use adds outside loop recurrences with 4+ terms becomes a balanced tree when that cuts its depth by 2 or more. | 32-bit addition wraps, so it is associative and commutative. |
| Dispatch tables | In one extra phase-1 variant: a loop's state phi s = phi(c0, s') where s' merges, at the join J of a branch region R (entered from E = idom(J), every path reconverging at J, pure instructions only), only constants or s. The region's other inputs must be one small key t (proven range [0, m], m <= 15) or values R passes on unchanged or plus a constant. R is evaluated at compile time for every (s, t) pair (symbolic base + constant values); each phi of J becomes a packed table read with shifts (one or two 32-bit words, entries stored relative to their minimum, states remapped through a nibble table when that shrinks the index). E then jumps straight to J. | s ranges over a finite set closed under the region (proven by following its phis to constants), t's range is proven, and each table entry is what the path for that pair computes. Pairs that cannot occur hold zero and are never read. Values made in R may not be used outside it except through J's phis. Tested on 150 random state machines in strict mode. |
| Closed-form loops | A loop that exits only at its header test (i < n, i <= n, i > n or i >= n; n invariant; i = phi(i0, i +- k), constant 1 <= k <= 65536, counting toward n), with a pure body whose other header phis are accumulators s' = s + c0 + c1*i + c2*i^2 + c3*i^3 (invariant c), is replaced by its exit values computed before it: T = (i0 < n') ? ceil((n' - i0)/k) : 0 (n' = n or n+1; a shift for power-of-two k, else div), S1 = T(T-1)/2 (halve the even factor), S2 = S1*(2T-1)*inv(3) mod 2^32, S3 = S1^2. | The sums are exact integer identities, and all of them hold modulo 2^32. Signed ranges must prove n' + k - 1 <= INT_MAX (so i never wraps), and for div that the rounded difference stays below 2^31. Pure bodies have no effects or traps to keep. Loop values may not be used outside except the header phis. |
| Bit-count and bit-reverse loops | Three loop shapes become the branch-free SWAR population count (12 operations): x &= x-1 with s += K; s += x & 1 with x >>= 1, both while x != 0; and s += (X >> i) & 1 for i from 0 while i < 32. In the last shape, s |= ((X >> i) & 1) << (31 - i) (or +=) becomes s0 | reverse(X) with the five-stage swap network (22 operations). | Each loop runs exactly pop(x) (or 32) rounds and adds one per set bit; shr is logical, so the count is exact for every 32-bit value. The structural conditions are the same as for closed-form loops. |
| Division by constants | x / C and x % C with constant C (not a power of two) and x proven in [0, X], X < 2^31: when X < 2C, one conditional subtraction (x / C = (x >= C), x % C = x < C ? x : x - C); otherwise q = (x*M) >> s with M = ceil(2^s/C) for the smallest s where X*M < 2^32 and X*(M*C - 2^s) < 2^s, and x % C = x - q*C. The multiply form is used only when the machine's mul+shift latency beats its div; the pass runs in the reassociating variants only, so the others keep the div. | Granlund-Montgomery: the error bound gives floor(x*M/2^s) = floor(x/C) on [0, X] and the product cannot wrap; checked exhaustively for 1,279 (C, X) pairs. Signed div equals unsigned here since x >= 0 and C > 0. A constant nonzero divisor cannot trap. |
| Dead scratch stores | A store to a constant scratch word (3072..4095) that no load can read is removed. | The scratch region is not observable; a constant in-range address cannot trap. |
| Min/max chains | In a block, a loop-carried chain of select(lt(p,q),q,p) (max) or select(lt(p,q),p,q) (min) becomes one carried step plus a balanced tree of the other inputs. | Signed min/max are associative and commutative and return one of their inputs, so every grouping gives the same bits. Inner nodes must have no other uses. |
| Horner splitting | A chain h' = h*x + c of n >= 6 steps becomes k=2 chains in x^2 (k=4 in x^4 with 16+ registers), combined at the end. Values it creates are never split again. | Wrapping arithmetic is a commutative ring, so any regrouping of the polynomial is exact. Inner products and sums must be single-use. |
| Counting selects | select(c, a, a+1) -> a + eq(c,0); select(c, a+1, a) -> a + (c != 0) (c itself when its range is 0..1). On a loop recurrence, select(c, a+k, a) with non-constant k -> a + select(c, k, 0) (and mirrored). | Exact case analysis on c; the test leaves the a chain. |
| Speculation | Bounded pure-work hoisting across eligible branches. A load whose address is proven in memory only on its own path (signed VRP plus branch facts) moves up as `and t, a, 4095; load t`, and may cross stores of the arm that provably touch other words. | Extra-path execution must have no observable effect and cannot trap. The masked address equals the original wherever the original load runs, so it reads the same word; elsewhere the value is unused. |
| Fusion | Select mac/addsh patterns using machine availability/costs; O(n). | Preserve low-32-bit arithmetic; unavailable instructions never reach output. Reduction fusion is a candidate choice. |
| If-conversion | Inline small safe arms and replace joins with select. | Both evaluated arms must be pure and non-trapping. |
| Load phis | For a load, walk up single-predecessor blocks to the nearest merge; if every predecessor's chain ends with a known value for the same address and no possibly aliasing store follows it, insert a phi there. | Each path already accessed the word, so no trap is lost. The address is constant or defined in a block strictly dominating the merge, so it names the same word on every edge, back edges included. |
| May-alias forwarding | In the load-phi stage, a load whose address was accessed earlier in the block, with at most two possibly aliasing stores since, becomes select(A == Bi, wi, ...) over those stores, newest last. | Exact case analysis on address equality; volatile accesses stop the search; the earlier access rules out a lost trap. |
| Pipelined header loads | (loads-only speculation candidates) A loop header's first load, preceded only by pure non-trapping work and with its address proven in memory at the header, is issued by every predecessor instead: each recomputes the address from its own incoming values, masks it to 12 bits and loads; the header takes the value through a phi. | When the header runs, a predecessor's address equals the header's, so the mask changes nothing and the same word is read at the same point (nothing runs between a predecessor's end and the header). On other exits the masked load cannot trap and its value is unused. |
| Arm stores | (store-select variant) A diamond whose two arms each end with a store to the same word (same SSA address or same base and offset) and otherwise hold only pure work: the arms' work moves into the branch block and one store of select(c, x, y) replaces both. | The word is written on both paths, so the single store writes what either arm would, and it cannot trap where the arms did not. Loads, volatile operations and possibly trapping work in an arm block the transform. |
| Store selects | Hoist a branch arm's leading pure work and stores (pairwise disjoint addresses defined above the branch) and store select(c, new, old). If the arm is then empty, merge its phi inputs into selects and remove it. | The old value must be known at the branch; the skipped path rewrites the same value into an already accessed word. Loads, volatile operations and possibly trapping work stop the hoisted run. |
| Return-block copies | In the load-phi stage, a return block (at most 32 instructions) gets a private copy for each predecessor whose phi inputs are all constants, within 512 new instructions; folding then shrinks the copy. | The block ends in ret, so its values have no other users; each path executes the same instructions with the same values. |
| Irreducible splitting | Tarjan SCCs; each extra entry of a multi-entry region gets its own copy of the region within a code budget. | Copying blocks and redirecting edges in register form keeps every execution's instruction sequence. |
| SSA destruction | Edge parallel copies, critical-edge splitting, temporary cycle breaking. | Read all copy sources before overwriting them. |
| Unlimited allocation | Interference/coalescing and greedy coloring; O(n+E) plus set work. | Simultaneously live values cannot share a name. On eight million edge insertion attempts, use distinct names rather than build an unbounded dense graph; neighbour lists are vectors to keep memory low. Functions with more than 4,096 SSA values coalesce through lazy representatives and canonicalize edges before coloring; small functions keep the prior eager traversal order. |
| K-name allocation | Conservative coalescing, ordered-set simplify/select, scratch spills and retry. Spill webs that are never live at the same time share a scratch word (greedy colouring over the interference graph of all members of each spilled web). Also tried for the largest programs; skipped when the graph exceeds 1.5 million edges. | Scratch is used only if original accesses are proven below 3072. Copy-related spill webs share a word only when legal. |
| Reload reuse | Retain fresh load/result temporaries for nearby uses in a block. | Cached slot contents must still match; definitions/stores update or invalidate the entry. Failed retention retries without reuse. |
| Color spreading | Try additional interference-legal colors within a bounded hardware-name preference set. | Coloring legality is unchanged. Unlimited allocation may still need more names; the preference cap is not a semantic register limit. |
| Scheduling | List scheduling in fixed windows, before/after allocation; O(n·w). | Preserve RAW/WAR/WAW, alias, trap and effect constraints. SSA memory ordinals must still match; otherwise facts are disabled. |
| Pressure scheduling | An extra pre-allocation alternative prefers last uses over new live definitions when ready issue times tie and K is nearly full; O(n·w) plus liveness. Exported values and exact backwards window-boundary sets retain future uses. | Only priorities change; the existing dependency/effect graph is unchanged. |
| Backward scheduling | Build a reverse topological order from sink instructions, estimate backwards liveness from exact liveOut/window boundaries, and balance reverse issue time against excess live values weighted by the machine's spill penalty. Try compact/spread colors with and without scratch allocation. With fixed window w=96, dependency construction is O(n·w) and ready-set scoring is O(n·w²) worst case. | Uses the identical RAW/WAR/WAW, memory, trap and effect graph as forward scheduling. Emits every instruction once and retains the terminator. Priorities never remove a dependence; reverse issue times are heuristics, not inserted delays. |
| Pure-region tree ordering | Order dependencies by estimated register need, then emit iterative postorder inside contiguous pure SSA regions; O(n), at most three operands per instruction. Used as an extra large-program or late-search candidate. | Emit every original instruction once, after its operands; never cross memory, division, volatile operations or control flow. No algebraic rewrites or recursion. Shared DAG estimates are heuristic. |
| Pure instruction sinking | Move single-user nontrapping pure instructions just before their user, possibly into a dominated block. Pin phi users; forbid loop-depth increases, movement into another loop and cross-block irreducible moves. Iterative dependency-forest rewrite; value scans O(n), CFG analyses bounded to 256 blocks, 100k instructions and 300k values. | Operands must dominate the destination. Single-user chains move together without cloning; pure operations may cross effects because they cannot affect them or trap. Moves never increase loop nesting. |
| Rematerialization | Offer at most 64 copies of cheap one-instruction parameter/constant recipes with 2–8 separated instruction users; O(n) scanning and fixed-budget cloning. No phi users; no GVN afterward. | Immutable leaves dominate every use. No effects/traps. Each parameter already has an independent use at/after the clone in its block, excluding all recipe definitions, so moving recipes does not invalidate the lifetime guard. |
| Rotation/unroll/peel/thread | Duplicate/register-form blocks and redirect edges; O(n·U) within code-growth budgets. | Each new path executes the same original instructions, except tests established redundant. |
| Latch counted groups | Guard the positive step, safe bound subtraction and enough remaining iterations; retain scalar fallback/remainder. | No skipped latch exit test may be false; preserve comparison writes and the body/effect order. Variable steps have runtime validity guards. |
| Header counted groups | Let D=(U-1)s. Guard bound >= INT_MIN+D, then test i < bound-D per group. | Intermediate increments cannot wrap before a skipped test. Each copy writes comparison=1. Keep the final possibly wrapping increment and original scalar exit test. |
| Unswitching | Clone a loop and dispatch on a register the loop never writes. | Reading the invariant early cannot trap; guarded body operations stay on their selected paths and in order. |
| Return copying | A jump to a return block of at most 3 instructions takes a copy of it; a branch to two identical such blocks becomes a jump; mov a,s; ret a becomes ret s; unreachable blocks are dropped. | Text copy of the executed instructions minus one jump. |
| Unread spill stores | Remove stores to scratch spill words that no load reads (K-name allocation only). | All original addresses were proven below 3072, so only spill code touches scratch. |
| Initial/trace layout | Loop-frequency chains; additional hot-block/edge layouts from fixed traces, O(T+b²). | Entry remains first; explicit targets are remapped. Prediction errors affect speed, not semantics. |

The final arithmetic stage takes at most five distinct candidate programs and
rebuilds SSA. In each block, identical quotient/remainder operands can share a
quotient, with `r = a - q*b` modulo 2^32. If remainder occurs first, the new
division executes at that same point, preserving the zero-divisor trap and
earlier effects. Six-ALU signed power-of-two lowering uses unsigned absolute
magnitude and sign-restoring selects; INT_MIN is representable as an unsigned
magnitude. Constant zero and +/-1 divisors retain their existing treatment.
Only cheaper-latency expansions are offered, and pre-scheduled and ordinary
lowerings are compared. These transformations are O(n log n) for local pairing
and O(n) for power-of-two expansion, before normal lowering costs.

A final compaction stage offers exact duplicate blocks, then an alternative
with shared identical suffixes (at least four instructions). Matches include
opcodes, registers, literals, shift amounts and ordered targets. The entry
stays first, explicit targets are remapped, and only unreachable copies are
removed. Suffix sharing leaves each original prefix intact and jumps to the
shared suffix; side effects/traps keep their execution order and multiplicity.
At most four suffixes are shared, with at most 128 input blocks and 32 compared
suffix instructions; this bounds pairwise matching work. Compaction itself
does not imply faster execution: each alternative is measured including jump
and instruction-cache costs.

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

SSA value numbers restart for each function. Both unsigned induction ranges and
signed VRP caches are cleared whenever buildSSA starts. Keeping the signed cache
across functions could falsely prove a fresh load safe and move it across a
volatile operation. A saved whole-pipeline regression and a direct poisoned-cache
test exercise this boundary.

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

Range tables are per function. The interval tables are indexed by one
function's value numbers, so building a new function empties both of them. A
stage that rebuilds a program and lowers it without running the range analyses
then sees no facts (and stays conservative) instead of another function's.

Compile work is bounded without the clock. A meter counts instructions lowered
(K-name allocations count three times). Phase 1 always runs in full; once
150,000 units are spent, later stages stop trying K-name allocations. The
count depends only on the input, so both judge runs give the same file.

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

- Packed count writeback has a fixed cost. Very short loops can take more
  cycles even when the candidate wins on the training inputs as a whole.

- The affine recognizer is deliberately incomplete: a nonlinear intermediate
  may cause rejection even when a later expression would cancel it. Dynamic
  shifts, general multiply, unresolved CFGs/loops and wide input support fall
  back to the existing optimizer. The emitted matrix is not claimed minimal.

- Rolling reuse deliberately rejects dynamic initial addresses/steps, multi-latch
  or larger loops, unknown aliases and volatile/trapping body operations. It
  keeps stores, so it does not remove every redundant write in sorting loops.
- Finite specialization handles only tiny statically proven input-bit domains
  with no memory effects. Failure of any gate retains existing candidates. Its
  lookup graph may lose to ordinary arithmetic, so it is always measured.

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
