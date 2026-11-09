// loops.h - loop transformations on the register form of a program.
//
// In register form (not SSA) a register keeps its name everywhere, so copying
// blocks and redirecting jumps can never change what a program computes: every
// execution of the new program follows the same instructions as some
// execution of the old one, in the same order. That makes rotation and
// unrolling exact by construction. The SSA pipeline runs again afterwards to
// clean up the copies.
#pragma once

#include <vector>

#include "ir.h"
#include "kir.h"
#include "sim.h"

namespace kopt {

// Phi-free Func whose values are dense register indices; regNames maps back.
Func toRegisterForm(const Program &p, std::vector<uint32_t> &regNames);
Program fromRegisterForm(Func &f, const std::vector<uint32_t> &regNames);

// Loop inversion: a latch that jumps back to a small exit-test header gets its
// own copy of the test, so each iteration takes one branch instead of two.
bool rotateLoops(Func &f, int maxHeaderSize);

// Replicate the body of innermost loops `factor` times (exits kept in every
// copy). Loops whose replicated size would exceed sizeBudget are left alone.
bool unrollLoops(Func &f, int factor, int sizeBudget);

// Peel `count` iterations of innermost loops: copies of the body run first,
// then the original loop. With a constant trip count <= count, constant
// propagation later removes the loop entirely.
bool peelLoops(Func &f, int count, int sizeBudget);

// Jump threading: when the outcome of a block's branch is already known on an
// incoming edge (the register was just tested, or set to a constant), that
// edge gets its own copy of the block ending in a plain jump.
bool threadJumps(Func &f, int maxBlockSize, int maxNewInstrs);

// Counted-loop unrolling. For an innermost loop whose single latch ends with
//   add i, i, s ; lt c, i, n ; br c, HEADER, EXIT
// (s > 0 constant, i written only there, n loop-invariant), a group of
// `factor` body copies runs without the intermediate tests while
// n - i > (factor-1)*s (signed; a wrapped difference just picks the original
// loop). The original loop stays as the remainder. New registers get names
// appended to regNames.
// Unswitch loops on branches whose condition the loop never writes.
bool unswitchLoops(Func &f, int sizeBudget);

bool countedUnroll(Func &f, std::vector<uint32_t> &regNames, int factor, int sizeBudget,
                   bool chainRemainder = false);

}  // namespace kopt
