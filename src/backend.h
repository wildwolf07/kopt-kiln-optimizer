// backend.h - from SSA back to KIR text: SSA destruction, register
// allocation for the Kiln's LRU register file, block layout and scheduling.
#pragma once

#include <string>

#include "ir.h"
#include "kir.h"
#include "sim.h"

namespace kopt {

struct BackendOptions {
    bool schedule = true;        // list-schedule each block for the machine model
    bool coalesce = true;        // remove copies by giving both sides one register
    bool profileLayout = true;   // use block frequencies to choose fall-throughs
    bool spillToK = false;       // use at most K names, spilling to scratch memory if needed
    bool preSchedule = false;    // also list-schedule on values before register allocation
    int spillReuse = 4;          // a reload serves later uses within this many instructions
    bool spreadColors = false;  // use spare hardware names to break false dependencies
    bool pressureSchedule = false; // alternative: finish local live ranges before opening more
};

// True when lowering with spillToK may use the scratch region (all of the
// program's own memory accesses are provably below it).
bool canSpillToScratch(Func &f);

// Lower an optimized SSA function to a Program for machine m. The function is
// consumed (phis are replaced by copies).
Program lowerToProgram(Func &f, const Machine &m, const BackendOptions &opt);

// Reorder instructions inside each block to start them as early as the machine
// allows, keeping every dependence (registers, memory, traps, volatile order).
void scheduleProgram(Program &p, const Machine &m);

}  // namespace kopt
