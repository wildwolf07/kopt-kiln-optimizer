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

}  // namespace kopt
