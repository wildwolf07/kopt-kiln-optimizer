#!/usr/bin/env python3
"""Direct wide-finite oracle checks: every projected state, no search/fallback.

python3 -B tests/wide_finite.py --source-root /path/to/current/src
Add --kit-free for CI: no kirlib import; direct C++ proof/SSA/cap/determinism
gates and local-interpreter table self-checks (not official validation).
KIT names the official COMP10 kit. Compilation snapshots sources into a temp
directory; production files and shared worktrees are never modified.
"""
import argparse
import ast
import hashlib
import json
import os
from pathlib import Path
import random
import shlex
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
KIT = Path(os.environ.get("KIT", ROOT.parent / "official-LLH-26/Compilers/COMP10"))
KIT_FREE = '--kit-free' in sys.argv[1:]
if not KIT_FREE:
    sys.path.insert(0, str(KIT))
    import kirlib as K

DRIVER = r'''
#include <cstdlib>
#include <iostream>
#include <iterator>
#include <stdexcept>
#include "passes.h"
using namespace kopt;
int main(int argc, char **argv) {
    try {
        if (argc != 3) return 2;
        const std::string text((std::istreambuf_iterator<char>(std::cin)), {}), mode = argv[1];
        std::string err; Program p;
        if (!parseProgram(text, p, err)) throw std::runtime_error(err);
        const std::string original = printProgram(p);
        if (mode == "masks") {
            const unsigned cap = static_cast<unsigned>(std::atoi(argv[2]));
            std::vector<uint32_t> masks{123456789};
            const bool accepted = finiteInputMasksUpTo(p, masks, cap);
            if (!accepted && masks != std::vector<uint32_t>{123456789}) return 3;
            if (cap == 6) {
                std::vector<uint32_t> old{123456789};
                if (finiteInputMasks(p, old) != accepted || old != masks) return 4;
            }
            std::cout << accepted;
            if (accepted) for (uint32_t mask : masks) std::cout << ' ' << mask;
            std::cout << '\n'; return 0;
        }
        std::vector<Program> outputs;
        if (mode == "legacy") {
            outputs = finiteAlternatives(p, true, true);
            Machine m; Program a = p, b = p;
            const bool da = finiteFunction(p, m, a), db = finitePackedFunction(p, m, b);
            if ((!da && printProgram(a) != original) || (!db && printProgram(b) != original)) return 5;
            if (outputs.size() != static_cast<size_t>(da) + static_cast<size_t>(db)) return 6;
            size_t i = 0;
            if (da && printProgram(outputs[i++]) != printProgram(a)) return 7;
            if (db && printProgram(outputs[i++]) != printProgram(b)) return 8;
        } else if (mode == "wide" || mode == "kit-wide") {
            outputs = finiteWideAlternatives(p);
            const auto again = finiteWideAlternatives(p);
            if (outputs.size() != again.size() || outputs.size() > 4) return 9;
            for (size_t i = 0; i < outputs.size(); ++i)
                if (printProgram(outputs[i]) != printProgram(again[i]) || outputs[i].instrCount() > 1024) return 10;
        } else return 11;
        if (printProgram(p) != original) return 12;
        std::cout << outputs.size() << '\n';
        for (const Program &out : outputs) {
            if (out.params != p.params || out.name != p.name) return 13;
            for (const Block &b : out.blocks) for (const Instr &x : b.ins) {
                if (isMemOp(x.op) || x.op == OP_TRAP || x.op == OP_DIV || x.op == OP_MOD) return 14;
                if (hasDest(x.op)) for (uint32_t param : out.params) if (x.dst == param) return 15;
            }
            Func f; if (!buildSSA(out, f, err)) throw std::runtime_error(err);
            err = verifyFunc(f); if (!err.empty()) throw std::runtime_error(err);
            if (mode == "kit-wide") {
                std::vector<uint32_t> masks;
                if (!finiteInputMasksUpTo(p, masks, 10)) return 16;
                std::vector<std::pair<size_t, uint32_t>> bits;
                for (size_t i = 0; i < masks.size(); ++i) for (unsigned b = 0; b < 32; ++b)
                    if (masks[i] & (uint32_t{1} << b)) bits.push_back({i, uint32_t{1} << b});
                SimProgram source(p), candidate(out);
                for (size_t key = 0; key < (size_t{1} << bits.size()); ++key) {
                    Input input; input.args.assign(p.params.size(), 0);
                    for (size_t bit = 0; bit < bits.size(); ++bit)
                        if ((key >> bit) & 1u) input.args[bits[bit].first] |= bits[bit].second;
                    for (int outside = 0; outside < 2; ++outside) {
                        if (outside) for (size_t i = 0; i < masks.size(); ++i) input.args[i] |= ~masks[i];
                        const auto a = source.run(input, 20000, false), b = candidate.run(input, 20000, false);
                        if (a.status != Status::RET || !compareRuns(a, b).empty()) return 17;
                    }
                }
            }
            const auto result = printProgram(out);
            std::cout << result.size() << '\n' << result;
        }
    } catch (const std::exception &e) { std::cerr << e.what() << '\n'; return 1; }
}
'''


def program(lines, params="v0"):
    return f"func wide({params})\nentry:\n" + "\n".join(lines) + "\n"


def high_case(n, modulus=3):
    lines = [f"shr v2,v0,{32-n}", f"mod v3,v2,{modulus}",
             "xor v4,v3,2147483648", "ret v4"]
    return program(lines), [(0, b) for b in range(32-n, 32)]


def pair_case(n):
    a = n - 3
    lines = [f"shr v2,v999999,{32-a}", "shl v2,v2,3", "and v3,v0,1",
             "shr v4,v0,10", "and v4,v4,2", "shr v5,v0,29", "and v5,v5,4",
             "or v6,v3,v4", "or v7,v6,v5", "or v8,v2,v7", "mod v9,v8,3",
             "add v10,v9,4294967293", "ret v10"]
    return program(lines, "v999999,v0"), [(0,b) for b in range(32-a,32)] + [(1,0),(1,11),(1,31)]


def late_case(timeout=False):
    body = ["shr v1,v0,22", "eq v2,v1,1023", "br v2,bad,good", "good:", "ret 1", "bad:"]
    body += ["jmp bad"] if timeout else ["div v3,1,0", "ret v3"]
    return program(body)


def total_budget_case():
    # Every one of 1024 cases terminates in ~1200 instructions (<20000), but
    # their aggregate exceeds 1M. The unused divisor keeps all ten bits live.
    return program(["and v1,v0,1023", "add v2,v1,1", "div v3,1,v2", "const v4,600",
                    "jmp loop", "loop:", "sub v4,v4,1", "br v4,loop,done", "done:", "ret 0"])


def invoke(binary, text, mode="wide", cap=10):
    p = subprocess.run([str(binary),mode,str(cap)],input=text,text=True,capture_output=True,timeout=60)
    assert p.returncode == 0,(mode,p.returncode,p.stderr)
    if mode == "masks": return [int(v) for v in p.stdout.split()]
    header, rest = p.stdout.split('\n',1)
    outputs = []
    for _ in range(int(header)):
        size,rest = rest.split('\n',1)
        count = int(size); outputs.append(rest[:count]); rest = rest[count:]
    assert not rest, repr(rest[:100])
    return outputs


def execute(cp, args, trace=False):
    r = K.execute(cp,args,[(0,[17,99]),(3072,[31])],{0:[7]},30000,want_trace=trace)
    assert r.status == "RET",(args,r.status,r.value)
    return r


def inherited_fixtures():
    # Reuse only these pure fixture factories. Importing the older test module
    # itself would import kirlib even in kit-free CI.
    path = ROOT/'tests/finite.py'
    module = ast.parse(path.read_text(), filename=str(path))
    factories = [n for n in module.body if isinstance(n, ast.FunctionDef)
                 and n.name in ('recurrence', 'fixtures')]
    assert len(factories) == 2
    namespace = {}
    exec(compile(ast.Module(body=factories, type_ignores=[]), str(path), 'exec'), namespace)
    return namespace['fixtures']()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source-root',type=Path,default=ROOT/'src')
    ap.add_argument('--artifacts',type=Path)
    ap.add_argument('--kit-free',action='store_true',help='no official kit required; structural/local self-check gates only')
    args = ap.parse_args()
    cfgs = [KIT/'machines'/f'machine_{m}.cfg' for m in
            ('default','few_registers','no_fused','slow_memory','wide_fast')]
    if args.artifacts: args.artifacts.mkdir(parents=True,exist_ok=True)
    comparisons = candidates = legacy_cases = 0
    rows = []
    with tempfile.TemporaryDirectory(prefix='kopt-wide-finite-') as temp:
        td = Path(temp); src = td/'src'; src.mkdir()
        for path in args.source_root.iterdir():
            if path.suffix in ('.h','.cpp'): (src/path.name).write_bytes(path.read_bytes())
        hashes = {name:hashlib.sha256((src/name).read_bytes()).hexdigest()
                  for name in ('finite.cpp','finite_domain.cpp','passes.h')}
        driver,binary = td/'driver.cpp',td/'driver';driver.write_text(DRIVER)
        sources = sorted(str(p) for p in src.glob('*.cpp') if p.name not in ('main.cpp','optimizer.cpp'))
        subprocess.run([*shlex.split(os.environ.get('CXX','c++')),'-std=c++17','-O1','-Wall','-Wextra',
                        '-Werror','-pedantic','-I'+str(src),str(driver),*sources,'-o',str(binary)],check=True)
        print('snapshot sha256',json.dumps(hashes,sort_keys=True),flush=True)
        inherited = inherited_fixtures()
        for name,(text,expected) in inherited.items():
            result = invoke(binary,text,'legacy')
            assert bool(result) == expected,('legacy gate',name,expected,len(result))
            legacy_cases += 1
        print('PASS',legacy_cases,'inherited six-bit gates and wrapper/vector equivalence',flush=True)
        rng = random.Random(230711)
        cases = [(f'high-{n}',*high_case(n)) for n in range(7,11)]
        cases += [(f'pair-{n}',*pair_case(n)) for n in range(7,11)]
        cases += [('ten-bit-one-bit-field',*high_case(10,2))]
        for name,text,positions in cases:
            masks = [0]*(max(p for p,_ in positions)+1)
            for p,b in positions: masks[p] |= 1 << b
            assert invoke(binary,text,'masks',10) == [1,*masks],(name,masks)
            assert invoke(binary,text,'masks',6) == [0],name
            assert invoke(binary,text,'masks',11) == [0],name
            assert not invoke(binary,text,'legacy'),name
            outputs = invoke(binary,text,'kit-wide' if args.kit_free else 'wide')
            assert len(outputs) == 4,(name,'expected forward/reverse BDD/packed',len(outputs))
            if args.kit_free:
                candidates += len(outputs)
                comparisons += len(outputs)*2*(1 << len(positions))
                rows.append(dict(case=name,candidates=len(outputs),projection_states=1 << len(positions)))
                print('PASS',name,'4 candidates; masks/SSA/caps/local table self-checks',flush=True)
                continue
            source = K.parse_program(text); original = K.compile_program(source)
            vectors = []
            for key in range(1 << len(positions)):
                vector = [0]*len(masks)
                for bit,(p,b) in enumerate(positions): vector[p] |= ((key >> bit)&1) << b
                vectors.append(vector)
            # Also set every unobserved bit and mix arbitrary high/negative words.
            vectors += [[(v | (~m & 0xffffffff)) for v,m in zip(a,masks)] for a in vectors]
            vectors += [[rng.getrandbits(32) for _ in masks] for _ in range(80)]
            refs = [execute(original,a) for a in vectors]
            for i,output in enumerate(outputs):
                p = K.parse_program(output); cp = K.compile_program(p)
                for a,ref in zip(vectors,refs):
                    actual = execute(cp,a); diff = K.first_difference(ref,actual)
                    assert not diff,(name,i,a,diff,output)
                    comparisons += 1
                timings = {}
                for cfg in cfgs:
                    mc = K.load_machine(str(cfg));K.check_machine_features(p,mc)
                    value = sum(K.time_trace(cp,execute(cp,a,True).trace,mc) for a in vectors[:16])
                    timings[cfg.stem] = value
                rows.append(dict(case=name,index=i,instructions=len(p.instrs),timings=timings))
                if args.artifacts: (args.artifacts/f'{name}-{i}.kir').write_text(output)
            candidates += len(outputs)
            print('PASS',name,'4 candidates;',1 << len(positions),'projection states plus outside-mask variants',flush=True)
        rejects = [('late-trap',late_case()),('late-timeout',late_case(True)),
                   ('aggregate-budget',total_budget_case()),
                   ('eleven-input-bits',program(['and v1,v0,2047','mod v2,v1,3','ret v2'])),
                   ('ten-bit-code-size-cap',program(['and v1,v0,1023','ret v1']))]
        for name,text in rejects:
            if name in ('late-trap','late-timeout','aggregate-budget'):
                assert invoke(binary,text,'masks',10) == [1,0xffc00000 if name!='aggregate-budget' else 1023],name
            assert not invoke(binary,text),(name,'should reject all representations')
            print('PASS rejected',name,flush=True)
        summary = dict(source_root=str(args.source_root.resolve()),hashes=hashes,kit_free=args.kit_free,comparisons=comparisons,
                       candidates=candidates,legacy_cases=legacy_cases,rows=rows)
        if args.artifacts: (args.artifacts/'evidence.json').write_text(json.dumps(summary,indent=2)+'\n')
    oracle = 'local-interpreter self-checks (kit-free, not official)' if args.kit_free else 'official comparisons'
    print(f'PASS {comparisons} {oracle} across {candidates} wide candidates; '
          f'{legacy_cases} legacy gates, late traps/timeouts, aggregate/code/bit budgets, '
          'determinism, SSA, high/sign/sparse/multi-parameter bits checked',flush=True)


if __name__ == '__main__': main()
