// optimizer.h - the kopt driver: optimize, then prove the result against the
// input on generated inputs with the exact simulator, and fall back to a
// safer pipeline (or the input itself) if anything differs.
#pragma once

#include <string>

#include "kir.h"
#include "sim.h"

namespace kopt {

struct Options {
    int maxLevel = 3;          // highest pipeline level to try
    bool verbose = false;      // diagnostics to stderr
    int checkInputs = 64;      // generated inputs for the self-check
};

std::string optimizeProgram(const std::string &origText, const Program &orig, const Machine &m,
                            const std::string &profileText, const Options &opt);

// Make a program legal for the machine (expand mac/addsh when not available).
Program legalize(const Program &p, const Machine &m);

}  // namespace kopt
