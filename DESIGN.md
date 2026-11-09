# DESIGN.md

kopt reads a KIR program and a machine file, optimizes the program in SSA form, turns it back into KIR for that machine, and checks the result against the input before writing it. It is about 5,000 lines of C++17 in `src/`.

| File | Role |
|---|---|
| `kir.*` | KIR parser and printer |
| `sim.*` | Exact interpreter and cycle model (a port of the kit's `kirlib.py`), plus input generators |
| `ir.h`, `ssa.cpp` | SSA form and its construction |
| `cfg.*` | Reverse postorder, dominators, dominance frontiers, natural loops, irreducible regions |
| `passes.*` | SSA optimizations |
| `loops.*` | Loop and jump transformations on the register form |
| `backend.*` | SSA destruction, register allocation, block layout, scheduling |
| `optimizer.*` | The driver: candidate programs, self-check, choice |

Sources: Cytron et al. (SSA construction), Cooper, Harvey and Kennedy ("A Simple, Fast Dominance Algorithm"), Wegman and Zadeck (SCCP), Briggs, Cooper and Torczon (conservative coalescing), Chaitin (graph colouring with spilling), Muchnick and the Dragon book (LICM, strength reduction, list scheduling), Tarjan (strongly connected components). The interpreter and timing model in `sim.cpp` are a C++ port of the kit's `kirlib.py`, as the rules allow.

## 1. What is implemented

**Analyses**
- Dominator tree, dominance frontiers, natural loops with nesting, and detection of irreducible regions.
- Liveness by path exploration from uses.
- Value ranges: depth-limited and recursive, with ranges for induction variables.
- Recurrences: strongly connected components of the SSA graph.

**SSA optimizations**
- Sparse conditional constant propagation.
- Algebraic simplification with copy propagation and trivial-phi removal.
- Like-term combining (`x*8 + x*10 = x*18`).
- Global value numbering, including division, remainder and loads, with store-to-load forwarding.
- Dead-code elimination and dead-store elimination.
- CFG cleanup: constant branches, block merging, jump threading through empty blocks.
- Loop-invariant code motion.
- Strength reduction of induction-variable multiplies.
- Reassociation of loop-carried add chains.
- Speculative hoisting of pure work above branches.
- If-conversion to `select`.
- Fusion into `mac` and `addsh`.

**Register-form transformations**
- Loop rotation.
- Unrolling by 2, 4 or 8.
- Peeling of 8 or 16 iterations.
- Jump threading on known branch outcomes.

**Back end**
- SSA destruction with parallel copies.
- Two register allocators: unlimited names with aggressive coalescing, or K names with spill slots in scratch memory.
- Block layout by chains.
- List scheduling against the exact issue model.

**Driver**
- Builds many candidate programs and ranks them by exact simulated cycles on typical inputs.
- Verifies the winner on about 120 inputs before writing it.

**Missing or partial**
- No loop unrolling without exit checks (counted-loop unrolling).
- No software pipelining.
- No scheduling across blocks other than the speculative hoisting above.
- The profile file is not used yet (section 6).

## 2. Pass order

1. **Parse.** If the machine lacks `mac` or `addsh` and the input uses them, they are expanded first.
2. **Build SSA.**
3. **Clean-up loop**, up to four rounds, repeated until nothing changes:
   - induction-variable ranges
   - SCCP
   - like-term combining
   - CFG cleanup
   - simplification
   - GVN
   - simplification
   - DCE
   - dead stores
   - CFG cleanup
   - LICM

   Constant propagation first exposes dead branches and constant addresses. Simplification and GVN then find shared work. DCE removes what became unused. LICM runs last so it sees the final, smallest loop bodies.
4. **Loop shaping**, once:
   1. Strength reduction.
   2. Reassociation.
   3. Speculation.
   4. Fusion into `mac` and `addsh`. It comes after the others because it is machine-specific and would hide patterns from them.
   5. If-conversion.
   6. A final simplify, DCE and CFG pass.
5. **Back end.**
   1. SSA destruction.
   2. Register allocation.
   3. Removal of copies that became `mov r, r`.
   4. CFG cleanup again, because empty copy blocks disappear.
   5. Layout.
   6. Scheduling.
6. **The driver repeats steps 2 to 5 to build candidates.**
   - **Phase 1:** six pass-option variants (reassociation on or off, `mac` on reductions, speculation), each lowered with both allocators.
   - **Phase 2:** the best distinct phase-1 programs go through the register-form transforms (rotate plus unroll, thread, peel) and the whole pipeline again.
   - **Phase 3:** two rounds of jump threading on the best programs so far.

   The variant search runs only for programs of up to 4,000 instructions. A larger program gets the default pipeline once, so a 100,000-instruction program takes about one second.

## 3. Each pass

n is the number of instructions, b the number of blocks.

| Pass | How it works | Cost | Why the change is safe |
|---|---|---|---|
| SSA construction | Phis on iterated dominance frontiers for registers read before being written in a block, then renaming along the dominator tree. A register read before any write becomes the constant 0. If the entry block has predecessors, a new entry block is added. | O(n + b·d) | Registers start at 0 (spec section 3). Renaming keeps every def-use pair. |
| SCCP | Optimistic lattice (unknown / constant / varying) over values and executable edges. Constant values become literals, never-executed blocks are deleted, branches with a known condition become jumps. | O(n) passes over a worklist | Only values computed the same on every execution are replaced. A division by a constant 0 is never folded, so it still traps. |
| Simplification | Algebra per instruction: `x+0`, `x-x`, `x*2^k -> shl`, `(x+c1)+c2`, `(y+c)-y = c`, double xor, shift amount taken mod 32, comparisons decided by ranges, `div` and `mod` by a power of two when the dividend is provably non-negative, trivial phis. | O(n) per round, at most 20 rounds | Every rule is an identity of 32-bit wrapping arithmetic. Signed division only becomes a shift when the value range proves the dividend is non-negative. |
| Like-term combining | An add/sub/mul-by-constant tree whose inner nodes have one use is a sum of coefficient times value. Equal values are merged and zero terms dropped. | O(n) | Multiplication distributes over addition modulo 2^32. |
| GVN | Hash-based value numbering in a dominator-tree walk. A load reuses an earlier load or store to the same address while no store that may alias comes between (inside a block, or along a chain of single-predecessor blocks). | O(n) expected | An identical dominating computation gives the same value. A repeated division cannot trap, because the first one already ran without trapping. |
| DCE | Mark and sweep from roots: stores, volatile operations, terminators, and every instruction that may trap. | O(n) | Nothing observable is removed. A division or load is kept unless its divisor or address is proven safe. |
| Dead stores | Inside a block, a store is removed if a later store writes the same address and nothing in between can read it or trap. | O(n·k) | The overwritten value is never observable. A store that may trap is never treated as an overwrite. |
| CFG cleanup | Constant branches, merging a block into its only predecessor, threading jumps through empty blocks. | O(n) per round | The paths and the instructions on them are unchanged. |
| LICM | Innermost loops first. Pure instructions with loop-invariant operands move to a preheader, which is created if needed. A load moves too if its address is proven in range and no store in the loop may alias it. | O(n) per loop | Pure work gives the same value earlier. Only instructions that cannot trap are moved. |
| Induction-variable ranges | P = phi(init, P + c) with a small constant c > 0. Every iteration that continues must have passed a test `X < N` that dominates the latch, with X being P or P + c and N invariant. If init and N are non-negative and N + c < 2^31, then P stays in [init, N + c - 1]. | O(loops · phis) | The counter cannot wrap, so the bound holds for every value P ever takes. |
| Strength reduction | `P * c` inside the loop becomes a new induction variable Q = phi(init·c, Q + s·c). | O(n) | (P + s)·c = P·c + s·c modulo 2^32. |
| Reassociation | In an add chain on a loop-carried cycle, the cycle value is added last, so the other terms are computed off the critical path. | O(n) | Wrapping addition is associative and commutative. |
| Speculation | Pure, non-trapping instructions move from a block into its only predecessor, which ends in a branch. | O(n) | In SSA the hoisted value is only computed earlier, and nobody on the other path uses it. |
| If-conversion | Small branch arms that only compute pure values are inlined, and the join's phis become `select`. | O(n) | Both arms are side-effect free and cannot trap. `select` picks the same value the branch would have taken. |
| Fusion | `mul` + `add` becomes `mac`, `shl` + `add` becomes `addsh`, and `x*(2^k+1)` becomes `addsh x, x, k`. A multiply in a reduction is not fused unless the multiply itself is on the recurrence. | O(n) | Same arithmetic. Only used when the machine has the instruction. |
| SSA destruction | Phi inputs become parallel copies at the end of the predecessor, or in a new block on a critical edge. Copies are ordered so that no source is overwritten too early, using a temporary to break cycles. | O(n) | Parallel copy semantics are preserved exactly. |
| Allocation, unlimited names | Interference graph from liveness. Copy-related values that do not interfere are merged, largest-weight copies first. Then smallest-last greedy colouring. | O(n + edges) | Values that are live at the same time never share a name. |
| Allocation, K names | Chaitin-Briggs: conservative (Briggs) coalescing, simplify and select with K colours. A value that cannot be coloured lives in a scratch word (`4095 - slot`): a store after each definition, a load before each use. Repeated until colourable. | O(iterations · (n + edges)) | Used only when every load and store address of the program is provably below 3072, so the scratch words belong to kopt alone. The scratch region is not observable (spec section 7). |
| Layout | Chains from the entry block. Each block is followed by its most frequent unplaced successor, preferring the successor that stays in the current loop. | O(b) | Order does not change semantics: every block ends in an explicit jump or branch. |
| Scheduling | List scheduling per block, in windows of 96 instructions, against the exact issue model (width, memory ports, latencies, in-order issue). The greedy choice is the earliest possible issue, then the longest path to the end of the block. | O(n · window) | See section 5 for the dependence rules. |
| Loop rotation | A latch that jumps back to a small exit-test header gets a copy of the test. | O(n) | In register form, executing the header's instructions at the end of the latch is exactly what the jump did. |
| Unroll, peel, thread | Block copies with redirected edges, all in register form. | O(n · factor) | Register form has no SSA names to repair. Every path of the new program executes the same instruction sequence as a path of the old one. |

## 4. The machine

`machine.cfg` is parsed in full; every key is used.

- **`registers` (K).** The cycle model charges `reg_spill_penalty` when a name evicted from its LRU register file is touched again. kopt lowers every candidate with the unlimited-names allocator. When that uses more than K names and the scratch region is free, it also lowers with the K-name allocator. The simulator picks the faster. With 4 registers, the K-name version usually wins, for example `matmul4` goes from 2313 to 649 cycles.
- **Latencies, `issue_width`, `mem_ports`.** The scheduler uses them directly. Fusion uses them too: `mac` only if `lat_mac <= lat_mul + lat_alu`, and `addsh` only if `lat_addsh <= 2 * lat_alu`. If `lat_mul < lat_alu`, a shift by a constant goes back to being a multiply.
- **`fused_mac`, `fused_addsh`.** Fusion is skipped when the instruction is missing. The final program is checked again, and any leftover `mac` or `addsh` is expanded.
- **`taken_branch_penalty`.** The if-conversion budget is 2 x (penalty + 1) instructions. Layout and unrolling reduce taken branches.
- **`icache_size`, `icache_penalty`.** These bound unrolling and peeling (unrolled loops must fit `icache_size`), and they are part of every simulated cost.

The exact simulator decides between all candidates on the actual machine, so a new combination of numbers is handled the same way as the known ones.

## 5. Keeping the behaviour

The rules of spec section 7 are enforced in four places.

1. **Removal.**
   - `vload`, `vstore`, `store` and `trap` are never removed by DCE.
   - `div`, `mod`, `load` and `store` count as "may trap" unless a value range proves the divisor non-zero or the address below 4096. A may-trap instruction is never removed, never moved out of a loop, never speculated and never if-converted.
   - An unused load is removed only when its address is proven in range.
2. **Order.** The scheduler adds dependences so that:
   - effects (observable stores, `vload`, `vstore`, `trap`) keep their order;
   - a may-trap instruction never crosses an effect;
   - a may-trap division and a may-trap memory access never swap (different trap kinds);
   - loads and stores that may touch the same word keep their order. Two different constant addresses never alias.

   A store to a constant scratch address is not observable and cannot trap, so only the memory rule orders it.
3. **Memory reasoning.** Load forwarding, load hoisting and dead stores use an address model of base value plus constant offset, plus value ranges. Two addresses are distinct only if both are the same base with different offsets, or their ranges do not overlap.
4. **Self-check.** The input and each candidate run on the same inputs:
   - 16 typical inputs (moderate counts, small array values);
   - 64 inputs from the kit's own generator (edge values, special pairs, random);
   - 32 more with another seed.

   The result, trap kind and code, volatile log and data region must all match. Inputs where the input program does not finish are skipped, as in `kvalidate`. A failing candidate is dropped, and if every candidate fails, the input is written unchanged.

Determinism: no clock, no unseeded randomness. Every choice depends only on the program and the machine, including the fixed-seed inputs used for timing.

## 6. Profiles

The current version reads `--profile` but does not use it. Candidates are compared by exact simulated cycles on typical inputs instead, so a profile that is wrong for the measured run cannot lead kopt astray.

## 7. Known problems

- **Small-input bias.** The choice between candidates uses kopt's own typical inputs. If the hidden input is very different (for example a loop count of 100,000), a candidate tuned for short runs can be slightly slower than another candidate would have been. It is never wrong, only slower.
- **Variant search size limit.** The search is limited to programs of up to 4,000 instructions. Larger programs get the default pipeline only, to stay far inside the time limits.
- **Counted loops.** Counted loops still test the exit condition in every unrolled copy.
- **Scratch spilling.** It is only used when every program address is proven below 3072. In loops whose bounds cannot be proven, the 4-register machine still pays LRU penalties.
