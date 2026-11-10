# Scheduling research and experiment notes

The contest permits published ideas and forbids copying optimizer code or using
compiler frameworks. These references informed independent implementations;
there is no external optimizer code or dependency in kopt.

- Shobaki, Shawabkeh and Abu Rmaileh (2013),
  [Preallocation instruction scheduling with register pressure minimization](https://scholars.csus.edu/esploro/outputs/journalArticle/Preallocation-instruction-scheduling-with-register-pressure/99257888392901671).
  Latency and pressure objectives can conflict. Our earlier forward scheduler
  prioritizes earliest issue and only breaks timing ties using pressure. The
  new alternative is allowed to accept estimated delay to shorten live ranges.
  It uses a fixed heuristic, not the paper's branch-and-bound solver.
- [LLVM code-generator documentation](https://llvm.org/docs/CodeGenerator.html)
  explains the scheduling/allocation separation and latency/pressure tradeoff.
  Its public [scheduler policy declarations](https://github.com/llvm/llvm-project/blob/main/llvm/include/llvm/CodeGen/MachineScheduler.h)
  expose top-down and bottom-up directions. Those declarations were consulted
  as architectural references; the implementation was not copied.
- Knoop, Rüthing and Steffen (PLDI 1992),
  [Lazy Code Motion](https://www.cs.cmu.edu/afs/cs/academic/class/15411-f19/www/papers/krs92.pdf).
  Earlier placement can create unnecessary register pressure. Conservative
  pure instruction sinking is implemented as a measured alternative. Full
  partial-redundancy elimination is not implemented.
- Appel and Supowit (1987),
  [Generalizations of the Sethi-Ullman algorithm](https://collaborate.princeton.edu/en/publications/generalizations-of-the-sethiullman-algorithm-for-register-allocat/).
  This informed the existing pure-region tree order. Shared DAGs, memory and
  the Kiln issue model exceed its tree-optimality assumptions, so we measure
  alternatives rather than claim optimality.

For Kiln, fewer abstract live values alone is insufficient. Reusing a register
name can introduce a write-after-write latency stall; using too many names
causes LRU penalties; scratch spills add loads, stores and memory dependencies.
We therefore offer four backward-scheduled lowerings: compact or spread names,
with or without explicit scratch spills. The exact full-program model chooses
among them and existing candidates on the same deterministic training inputs.

The reverse scheduler reuses the established dependence graph. It starts from
exported values and terminator operands, kills definitions and generates reads
while placing sinks. Its heuristic cost is reverse issue time plus excess live
values times max(1, reg_spill_penalty). Ties prefer fewer new live values, longer
paths from entry, and stable original indices. No graph edge is removed. It
never speculates, duplicates, deletes or transfers instructions across a block
or 96-instruction window. Reverse issue times guide ordering only.

Measured public and independently generated hardware results belong in
BENCHMARKS.md. Research quality does not establish correctness or a hidden score:
all retained changes need direct tests, whole-pipeline checks and bounded time.

Finite-domain specialization combines a static information-dependence proof
with exhaustive evaluation of at most 64 equivalence classes. Every raw
parameter use remaining after safe SSA cleanup must be AND with a constant;
the union of masks determines exactly which bits can matter. High bits,
parameter aliases and phi users cannot silently bypass this gate. The original
program is interpreted for all projected cases, with hard instruction budgets;
any trap or timeout rejects the transformation. No input corpus is read.

Its result representation uses the familiar equal-subtree reduction associated
with [Bryant's graph-based Boolean-function work (1986)](https://www.cs.cmu.edu/~bryant/pubs.html).
Leaves here are 32-bit return values, rather than Boolean values. This is a
small independently implemented decision graph, not a BDD package or solver.
The broader idea is related to partial evaluation; see Jones, Gomard and
Sestoft's [Partial Evaluation and Automatic Program Generation](https://studwww.itu.dk/people/sestoft/pebook/).
The implementation does not import code from these references.

An early alternative coloring-order experiment was rejected. It recovered an
older spill_storm result but changed later search seeds and regressed several
other programs. That experiment is absent from production. The retained new
stages append candidates after earlier searches to preserve their paths.

The next finite-domain proof works backwards from observable result bits,
complete branch operands and division/remainder divisors. For addition,
subtraction and multiplication, a demanded output bit can depend on lower
input bits, so the transfer fills every bit through the highest demand.
Logical shifts map demands by their constant amount; variable shifts retain
the entire source and the count's low five bits. Phi demands are unioned to a
fixed point. These rules use KIR's wrapping arithmetic and shift semantics;
no cached range facts or optimizer cleanup are required. A bounded exact
constant pass handles masks introduced by const/mov without interval reasoning.

Related context: Stephenson, Babb and Amarasinghe,
[Bitwidth Analysis with Application to Silicon Compilation](https://dspace.mit.edu/entities/publication/0c6567bf-0998-454f-8579-54fb30c83954),
and Budiu and Goldstein,
[BitValue Inference](https://www.cs.cmu.edu/~seth/papers/budiu-tr00.html).
Our goal is a finite input-equivalence proof, rather than reducing machine
operand widths. The projected domain is still exhaustively interpreted.

A second representation packs finite results into constant words. The field
width is a power of two and a shifted mask extracts an entry; a small decision
graph selects words when needed. All constants are constructed from this run's
exhaustive table. Lookup metadata is never a program fingerprint or an external
answer store. The original decision representation remains available.

Large-program allocation integrates the independently developed changes from
this repository's `optimizer-final` snapshot `65e03e0`: lazy class-level
coalescing, compact K-allocator live lists, and block-local definition refresh.
An initial global lazy-coalescing experiment changed small-case search paths;
restricting it to more than 4,096 values preserves all practice cycle counts.
The separate deterministic compile-work budget was not imported, to keep the
existing search coverage while measuring these changes in isolation.
