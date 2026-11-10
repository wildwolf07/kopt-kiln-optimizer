#!/usr/bin/env python3
"""Direct load-splitting proof gates and independent official comparisons.

--kit-free uses tools/smoke.py BASE_MACHINE with no kirlib import: exact clone
counts, original/lowered SSA, repeated byte determinism, and local-interpreter
self-checks for all fixtures/modes. These self-checks are not official validation.
Full mode retains the original 31,360 independent comparisons.
"""
from pathlib import Path
import os
import random
import shlex
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
KIT = Path(os.environ.get("KIT", ROOT.parent / "official-LLH-26/Compilers/COMP10"))
sys.dont_write_bytecode = True
KIT_FREE = sys.argv[1:] == ["--kit-free"]
if sys.argv[1:] not in ([], ["--kit-free"]):
    raise SystemExit("usage: load_rematerialize.py [--kit-free]")
if not KIT_FREE:
    sys.path.insert(0, str(KIT))
    import kirlib as K

DRIVER = r'''
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <iterator>
#include "backend.h"
#include "passes.h"
namespace kopt { bool rematerializeLoads(Func &); }
using namespace kopt;
int main(int argc, char **argv) {
    if (argc != 4 && argc != 5) return 2;
    const bool kitFree=argc==5 && std::string(argv[4])=="--kit-free";
    std::string text((std::istreambuf_iterator<char>(std::cin)), {}), err;
    std::ifstream file(argv[1]); const std::string cfg((std::istreambuf_iterator<char>(file)), {});
    Program p; Func f; Machine m;
    if (!parseProgram(text,p,err) || !parseMachine(cfg,m,err) || !buildSSA(p,f,err)) return 3;
    const int nv=f.nvals, expected=std::atoi(argv[2]);
    err=verifyFunc(f); if (!err.empty()) {std::cerr<<err;return 5;}
    const bool changed=rematerializeLoads(f);
    if (changed!=(expected>0) || f.nvals-nv!=expected) {
        std::cerr << "changed=" << changed << " clones=" << f.nvals-nv; return 4;
    }
    err=verifyFunc(f); if (!err.empty()) {std::cerr<<err;return 5;}
    const int mode=std::atoi(argv[3]);
    if (mode<0) {std::cout<<dumpFunc(f);return 0;}
    BackendOptions bo;
    bo.preSchedule=(mode&1)!=0; bo.spillToK=(mode&2)!=0; bo.bottomUpSchedule=(mode&8)!=0;
    const Program out=lowerToProgram(f,m,bo);
    if (kitFree) {
        Func repeat;
        if (!buildSSA(p,repeat,err)) return 6;
        const int before=repeat.nvals;
        if (rematerializeLoads(repeat)!=changed || repeat.nvals-before!=expected) return 7;
        err=verifyFunc(repeat); if (!err.empty()) {std::cerr<<err;return 8;}
        if (printProgram(lowerToProgram(repeat,m,bo))!=printProgram(out)) return 9;
        Func lowered;
        if (!buildSSA(out,lowered,err)) return 10;
        err=verifyFunc(lowered); if (!err.empty()) {std::cerr<<err;return 11;}
        SimProgram original(p), candidate(out);
        for (uint32_t value : {0u,1u,5u,4095u,4096u,0x7fffffffu,0x80000000u,0xffffffffu}) {
            for (int pattern=0;pattern<4;++pattern) {
                Input input; input.args.assign(p.params.size(),value);
                std::vector<uint32_t> words(256);
                for (size_t i=0;i<words.size();++i)
                    words[i]=pattern==0 ? 0u : pattern==1 ? 0xffffffffu :
                             pattern==2 ? (static_cast<uint32_t>(i)*2654435761u)^value : static_cast<uint32_t>(i);
                input.segments.push_back({0,words});
                input.segments.push_back({3072,{value}}); input.segments.push_back({4095,{value}});
                input.vin[1]={value,13,17};
                const auto a=original.run(input,20000,false), b=candidate.run(input,20000,false);
                const auto diff=compareRuns(a,b);
                if (a.status==Status::TIMEOUT || b.status==Status::TIMEOUT || !diff.empty()) {
                    std::cerr<<"local self-check: "<<diff; return 12;
                }
            }
        }
    }
    std::cout<<printProgram(out);
}
'''


def straight(address="5", between="", padding=20, before="", after="", users=2):
    lines = ["func split(v0)", "entry:"]
    if before: lines += [before]
    lines += [f"load v1, {address}", "store 20, v1"]
    lines += [f"store {100+i}, v0" for i in range(padding)]
    if between: lines += [between]
    lines += ["store 21, v1"]
    for i in range(users-2): lines += [f"store {30+i}, v1"]
    if after: lines += [after]
    lines += ["ret v0"]
    return "\n".join(lines) + "\n"


def fixtures():
    cases = {
        "disjoint-stores": (straight(), 2),
        "address-zero": (straight("0"), 2),
        "address-scratch-boundary": (straight("3072"), 2),
        "address-last-valid": (straight("4095"), 2),
        "address-first-invalid": (straight("4096"), 0),
        "address-negative": (straight("-1"), 0),
        "variable-address": (straight("v0"), 0),
        "alias-store": (straight(between="store 5, v0"), 0),
        "unknown-store": (straight(between="store v0, 17"), 0),
        "bad-store": (straight(between="store 4096, 17"), 0),
        "bad-load": (straight(between="load v8, 4096\nstore 300, v8"), 0),
        "unknown-load": (straight(between="load v8, v0\nstore 300, v8"), 0),
        "disjoint-load": (straight(between="load v8, 6\nstore 300, v8"), 2),
        "vload-barrier": (straight(between="vload v8, 1\nstore 300, v8"), 0),
        "vstore-barrier": (straight(between="vstore 1, v0"), 0),
        "div-barrier": (straight(between="div v8, 17, v0\nstore 300, v8"), 0),
        "mod-barrier": (straight(between="mod v8, 17, v0\nstore 300, v8"), 0),
        "safe-div": (straight(between="div v8, v0, 2\nstore 300, v8"), 2),
        "safe-mod": (straight(between="mod v8, v0, -1\nstore 300, v8"), 2),
        "volatile-before": (straight(before="vstore 1, v0"), 2),
        "volatile-after": (straight(after="vload v8, 1\nvstore 2, v8"), 2),
        "alias-before": (straight(before="store 5, v0"), 2),
        "alias-after": (straight(after="store 5, v0"), 2),
        "reuse-at-limit": (straight(padding=15), 0),
        "reuse-over-limit": (straight(padding=16), 2),
        "nine-users": (straight(users=9), 0),
        "zero-initial": (straight().replace("store 21, v1", "add v2,v1,v999999\nstore 21,v2"), 2),
    }
    duplicate = straight().replace("store 20, v1", "add v2,v1,v1\nstore 20,v2")
    cases["duplicate-operand"] = (duplicate, 2)
    cross = straight().replace("store 21, v1\nret v0", "jmp next\nnext:\nstore 21,v1\nret v0")
    cases["cross-block-user"] = (cross, 0)
    phi = straight().replace("ret v0", "br v0,left,right\nleft:\njmp join\nright:\nconst v1,9\njmp join\njoin:\nret v1")
    cases["phi-user"] = (phi, 0)
    trap = straight().replace("store 21, v1", "trap 17\ndead:\nstore 21,v1")
    cases["cross-trap-user"] = (trap, 0)
    # An unreachable suffix cannot turn a trapping load into a safe recipe.
    cases["trap-before"] = (straight(before="div v9,17,0"), 2)
    cases["trap-after"] = (straight().replace("ret v0", "trap 17"), 2)
    loop = straight().replace("entry:\n", "entry:\nconst v9,3\njmp body\nbody:\n")
    loop = loop.replace("ret v0", "sub v9,v9,1\nbr v9,body,done\ndone:\nret v0")
    cases["loop-local"] = (loop, 2)
    budget = ["func budget(v0)", "entry:"]
    budget += [f"load v{10+i}, {i}" for i in range(40)]
    budget += [f"store {100+i}, v{10+i}" for i in range(40)]
    budget += [f"store {200+i}, v{10+i}" for i in range(40)]
    cases["clone-budget"] = ("\n".join(budget + ["ret v0"]) + "\n", 64)
    return cases


def main():
    rng = random.Random(111023)
    edges = [0, 1, 5, 4095, 4096, 0x7fffffff, 0x80000000, 0xffffffff]
    args = edges + [rng.getrandbits(32) for _ in range(48)]
    memory = [[0]*256, [0xffffffff]*256,
              [rng.getrandbits(32) for _ in range(256)], list(range(256))]
    checks = 0
    with tempfile.TemporaryDirectory() as tmp:
        td = Path(tmp); driver = td / "driver.cpp"; binary = td / "driver"
        driver.write_text(DRIVER)
        sources = sorted(str(p) for p in (ROOT / "src").glob("*.cpp")
                         if p.name not in ("main.cpp", "optimizer.cpp"))
        subprocess.run([*shlex.split(os.environ.get("CXX","c++")), "-std=c++17", "-O1", "-Wall", "-Wextra",
                        "-Werror", "-pedantic", "-I"+str(ROOT / "src"), str(driver), *sources,
                        "-o", str(binary)], check=True)
        if KIT_FREE:
            sys.path.insert(0,str(ROOT/"tools"))
            from smoke import BASE_MACHINE
            cfg=td/"own-machine.cfg"
            cfg.write_text("".join(f"{key} = {value}\n" for key,value in BASE_MACHINE.items()))
        else:
            cfg = KIT / "machines/machine_slow_memory.cfg"
        for name, (text, clones) in fixtures().items():
            if not KIT_FREE:
                original = K.compile_program(K.parse_program(text))
            for mode in (0,1,9,11):
                command=[str(binary),str(cfg),str(clones),str(mode)]
                if KIT_FREE: command.append("--kit-free")
                result = subprocess.run(command,input=text,
                                        text=True,capture_output=True,check=True)
                if KIT_FREE:
                    checks+=len(edges)*len(memory)
                    continue
                out = K.parse_program(result.stdout); K.check_machine_features(out,K.load_machine(str(cfg)))
                optimized = K.compile_program(out)
                for value in args:
                    for words in memory:
                        segments = [(0,words),(3072,[value]),(4095,[value])]
                        vin = {1:[value,13,17]}
                        a = K.execute(original,[value],segments,vin,20000)
                        b = K.execute(optimized,[value],segments,vin,20000)
                        diff = K.first_difference(a,b)
                        assert not diff,(name,mode,value,diff,result.stdout)
                        checks += 1
            print("PASS",name,flush=True)
    if KIT_FREE:
        print(f"{checks} local-interpreter self-checks (kit-free, not official); "
              f"{len(fixtures())} fixtures x 4 modes; exact clone counts, original/lowered SSA, "
              "repeat determinism and address/alias/barrier gates passed")
    else:
        print(f"{checks} official comparisons; exact clone counts, address/alias/barrier/SSA gates passed")


if __name__ == "__main__":
    main()
