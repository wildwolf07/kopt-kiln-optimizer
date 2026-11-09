# Demo and judge questions

These answers describe the implementation at `acb68c8`. Recheck them after changes
to the optimizer. Sample-input speedups and finite testing do not establish a
hidden-test score or equivalence for every input.

## Three-minute demonstration

Prepare the official COMP10 kit separately and set `KIT` to its absolute path.
Run these commands once before the demo; keep their output available offline.

```sh
./build.sh
python3 tools/smoke.py
python3 tools/bench.py --machines all --random 50
```

1. **0:00–0:30 — State the contract.** Show the command below. It accepts KIR and a
   machine file, and emits KIR with the same result, trap, volatile log and data
   memory. The core is SSA optimization followed by machine-aware lowering.
2. **0:30–1:30 — Show one transformation.** Use the kit's `sum_sq` program. Show
   the before/after instruction counts and simulator cycles. Explain one removed
   copy and one machine-dependent change visible in the actual output.
3. **1:30–2:15 — Show evidence.** Validate that output with the independent kit
   tool. Show the five-machine benchmark totals; distinguish aggregate sample
   speedup from a geometric mean and from hidden-test performance.
4. **2:15–3:00 — Show a boundary case.** Run the smoke suite. Explain that a
   division whose result is dead still has to execute when it may trap. Explain
   that the self-check is a safeguard and cannot prove equivalence.

```sh
./kopt "$KIT/bench/sum_sq.kir" --machine "$KIT/machines/machine_default.cfg" -o /tmp/demo.kir
python3 "$KIT/kvalidate" /tmp/demo.kir --against "$KIT/bench/sum_sq.kir" --machine "$KIT/machines/machine_default.cfg"
./build/kopt-bin --sim "$KIT/bench/sum_sq.kir" --machine "$KIT/machines/machine_default.cfg" --input "$KIT/bench/sum_sq.in"
./build/kopt-bin --sim /tmp/demo.kir --machine "$KIT/machines/machine_default.cfg" --input "$KIT/bench/sum_sq.in"
```

## Thirty questions and answers

1. **What exactly must the optimizer preserve?** The returned value or trap kind
   and explicit trap code, ordered volatile log, and final words 0–3071. At a
   trap, effects that already happened must still be visible.

2. **Why use SSA?** Each value has one definition, so propagation, dominance-based
   reuse and dead-code analysis can reason about values independently of reused
   input register names. Phis express values arriving through different edges.

3. **How do you construct SSA?** Compute dominators and dominance frontiers,
   insert needed phis, and rename along the dominator tree. Reads without a
   prior definition use zero, as required by KIR.

4. **What if execution jumps back into the entry block?** The SSA builder adds
   an entry block when the original entry has predecessors, separating initial
   parameter values from values arriving on backedges.

5. **What does SCCP add beyond constant folding?** It tracks executable edges as
   well as value constants. That lets it discover unreachable branches and
   simplify phis when only some incoming edges can execute.

6. **Can signed overflow invalidate algebraic rewrites?** KIR arithmetic wraps
   modulo 2^32. Rewrites use that arithmetic rather than relying on C++ signed
   overflow. Signed comparisons and division need their own exact semantics.

7. **Why is division by a power of two delicate?** Signed division truncates
   toward zero, while a shift does not implement that for every negative value.
   The shift rewrite requires a provably non-negative dividend.

8. **How are large or negative shift amounts handled?** KIR masks the amount to
   five bits. A shift by 33 is a shift by 1; a shift by -1 is a shift by 31.
   The arithmetic smoke fixture checks these boundaries.

9. **Can you delete an unused division?** Only if it cannot trap. A dead result
   does not make division by zero unobservable. DCE treats potentially trapping
   instructions as roots.

10. **Can you delete an unused load?** Only after proving its address valid.
    Otherwise a bad-address trap would disappear.

11. **Why is speculation safe?** Its operands must be available and the work
    must be pure and non-trapping. Computing such a value on an extra path has
    no observable effect. A guarded dangerous operation cannot be speculated.

12. **When can a load move out of a loop?** Its address must be invariant and
    valid, and no loop store may alias it. Unknown aliases block the rewrite.

13. **How does load forwarding avoid aliasing errors?** It reuses a prior value
    only while intervening stores cannot change that address. Unknown stores
    invalidate the relevant knowledge. Volatile accesses are separate effects.

14. **When is an earlier store dead?** A later store must overwrite the same
    address before a read or trap can observe the earlier value. Possible aliasing
    or a possible trap prevents an unsafe deletion.

15. **What does the scheduler preserve?** Register dependencies, aliasing memory
    order, observable effect order, and required order between traps and effects.
    It cannot swap different possible trap kinds and change the first trap.

16. **Why does if-conversion need restrictions?** Executing both arms and using
    `select` is valid only for small pure, non-trapping arms. Otherwise the
    formerly untaken arm could introduce a store, volatile event or trap.

17. **How do phi copies survive register allocation?** SSA destruction emits
    parallel copies on incoming edges, splitting critical edges when necessary.
    A temporary breaks copy cycles so a source is not overwritten too soon.

18. **How is the Kiln register model unusual?** Arbitrarily many register names
    are legal. The timing model charges when a previously evicted name is touched
    again in an LRU cache of K names. Naming and reuse therefore affect cost.

19. **Why have two allocators?** Unlimited names avoid explicit scratch traffic
    but may incur LRU penalties. K-name allocation trades those penalties for
    explicit loads and stores. The simulator compares the resulting candidates.

20. **When can you use scratch memory?** Only when every original memory address
    is proven below 3072. Otherwise the original program could use the scratch
    words and conflict with spills. Scratch is unobservable, but still usable by
    the original program.

21. **What did the spill-web change do?** Copy-related spilled values can share
    a scratch word, removing unnecessary memory-to-memory copies. Newly created
    short reload temporaries are protected from being spilled again.

22. **Why can fusion make a program slower?** It may lengthen a loop-carried
    dependency even while reducing instruction count. Fusion on reductions is
    one candidate choice rather than an unconditional final decision.

23. **How do you handle a machine without fused instructions?** Skip unsupported
    fusion and expand any remaining `mac` or `addsh`. The smoke suite checks that
    neither appears in output for a machine that disables both.

24. **Why stop unrolling at bounded factors?** Copies reduce branch overhead but
    grow code and register pressure. The instruction-cache costs and simulation
    can make a larger unroll lose. Exit checks remain in unrolled copies.

25. **Do you use profiles?** The CLI accepts and reads the named profile, but
    this version does not use it. Layout uses loop-nesting estimates, and candidate
    ranking uses simulated typical inputs. Profile counts never prove semantics.

26. **How is output deterministic?** Fixed candidate order, fixed input seeds,
    stable tie handling and no clock-based selection. Timing diagnostics do not
    influence the output. Development tests compare repeated output bytes.

27. **Does the self-check prove correctness?** No. It compares finite executions
    of original and candidate programs. It can miss untested inputs and shared
    interpreter mistakes. Semantic reasoning and the independent kit gates remain
    necessary; source timeouts are skipped.

28. **How do you avoid spending too long searching?** Programs above 4,000
    instructions get the default pipeline rather than the full candidate search.
    Runtime still needs measurement on the target machine; the threshold alone
    does not guarantee a time bound.

29. **What do the reported speedups measure?** Original sample cycles divided
    by optimized sample cycles, summed across the public programs for one
    machine. They are aggregate ratios, not geometric means. Hidden programs and
    inputs can have different speedups.

30. **What would you improve next?** Spill reload reuse, counted-loop unrolling
    with a remainder loop, and scheduling across blocks. Each needs independent
    correctness checks and a before/after cycle comparison; none is claimed here
    as already implemented.
