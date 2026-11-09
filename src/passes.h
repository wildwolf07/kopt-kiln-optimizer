// passes.h - SSA optimization passes. Every pass keeps the program's
// observable behaviour (KIR_SPEC.md section 7) and returns true if it changed
// something. Facts that make each change safe are documented next to the code.
#pragma once

#include "ir.h"
#include "sim.h"

namespace kopt {

// Evaluate a pure instruction on constants. Returns false if it would trap or is
// not foldable (loads, volatile ops).
bool foldConstant(Op op, uint32_t a, uint32_t b, uint32_t c, int k, uint32_t &out);

// Instructions that may stop the program with a trap, given what we know about
// their operands (constant divisor != 0, constant/bounded address < 4096).
bool mayTrap(Func &f, const Inst &x);

// Is the address operand provably inside memory (< 4096)?
bool addressInRange(Func &f, Opnd addr);

bool simplifyCFG(Func &f);         // fold constant branches, merge blocks, thread empty jumps
bool sccp(Func &f);                // sparse conditional constant propagation
bool instSimplify(Func &f);        // algebraic simplification + copy propagation + trivial phis
bool gvn(Func &f);                 // dominator-scoped value numbering incl. loads and store forwarding
bool dce(Func &f);                 // remove values nobody needs (never removes possible traps)
bool deadStores(Func &f);          // remove stores overwritten before anything can observe them
bool licm(Func &f);                // hoist loop-invariant work into a preheader
bool fuseOps(Func &f, const Machine &m);      // mac / addsh / strength reduction for this machine
bool ifConvert(Func &f, const Machine &m);    // small branches -> select

}  // namespace kopt
