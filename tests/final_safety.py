#!/usr/bin/env python3
"""Direct matrix-recognition and store-edge memory-safety regressions.

Run with CXX sanitizer flags to detect arithmetic overflow and stale references.
No optimizer search or fallback can hide a failure. --source-root supports
checking an older source tree with the same fixtures.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True
DRIVER = r'''
#include "passes.h"
#include "backend.h"
#include <fstream>
#include <iostream>
#include <iterator>
#include <stdexcept>
using namespace kopt;
void need(bool b, const std::string &s) { if (!b) throw std::runtime_error(s); }
int main(int argc, char **argv) { try {
    need(argc == 4, "mode expected output-directory");
    const std::string mode = argv[1], dir = argv[3];
    const bool expected = std::string(argv[2]) == "1";
    const std::string text((std::istreambuf_iterator<char>(std::cin)), {});
    Program p; std::string err; need(parseProgram(text,p,err),err);
    Machine m;
    std::vector<Program> programs;
    if (mode == "store") {
        Func f; need(buildSSA(p,f,err),err);
        // The first inserted edge must reallocate the block vector.
        std::vector<BB> tight(f.bb.begin(),f.bb.end()); f.bb.swap(tight);
        need(f.bb.capacity()==f.bb.size(),"fixture requires exact block capacity");
        const size_t count=f.bb.size();
        need(sinkDeadStores(f),"positive store fixture did not transform");
        need(f.bb.size()>count,"fixture did not insert an edge");
        for(int mode=0;mode<4;++mode) {
            Func copy=f; BackendOptions bo;
            bo.preSchedule=mode!=0;bo.bottomUpSchedule=mode==2;bo.spillToK=mode==3;
            programs.push_back(lowerToProgram(copy,m,bo));
        }
    } else {
        programs=mode=="row"?rowPairAlternatives(p):matmulAlternatives(p,m);
        need((!programs.empty())==expected,"matrix proof gate mismatch");
    }
    SimProgram original(p); Rng rng(131313);
    for(size_t k=0;k<programs.size();++k) {
        SimProgram candidate(programs[k]);
        for(unsigned trial=0;trial<20;++trial) {
            Input in;
            for(size_t i=0;i<p.params.size();++i)
                in.args.push_back(trial<4 ? (trial==0?0:trial==1?1:trial==2?0xffffffffu:0x80000000u) : uint32_t(rng.next()));
            std::vector<uint32_t> words(4096);
            for(auto &v:words) v=trial%3==0?0xffffffffu:uint32_t(rng.next());
            in.segments={{0,words}};
            const auto a=original.run(in,100000,false),b=candidate.run(in,100000,false);
            need(a.status!=Status::TIMEOUT&&b.status!=Status::TIMEOUT,"fixture timeout");
            need(compareRuns(a,b).empty(),compareRuns(a,b));
        }
        std::ofstream out(dir+"/"+std::to_string(k)+".kir");
        out<<printProgram(programs[k]); need(bool(out),"write candidate");
    }
    std::cout<<programs.size()<<'\n';
} catch(const std::exception &e) {std::cerr<<e.what()<<'\n';return 1;} }
'''


STORE = '''func stores(v0)
entry:
  store 0, 1
  br v0, overwritten, kept
overwritten:
  store 0, 2
  jmp done
kept:
  jmp done
done:
  load v1, 0
  ret v1
'''

DEAD = '''func dead()
entry:
  ret 0
dead1:
  const v999999, 1
  mov v888888, v777777
  load v765432, 0
  load v654321, 1
  store 0, 2
  jmp dead2
dead2:
  ret 0
dead3:
  ret 0
dead4:
  ret 0
dead5:
  ret 0
dead6:
  ret 0
'''

ROW = '''func row(v90)
entry:
  const v0, 0
  jmp outer
outer:
  lt v1, v0, 2
  br v1, init, done
init:
  const v2, 0
  const v3, 0
  jmp inner
inner:
  lt v4, v2, 2
  br v4, body, save
body:
  mul v5, v0, 2
  add v5, v5, v2
  add v5, v5, 16
  load v6, v5
  add v7, v2, 128
  load v8, v7
  mul v9, v6, v8
  add v3, v3, v9
  add v2, v2, 1
  jmp inner
save:
  add v10, v0, 256
  store v10, v3
  add v0, v0, 1
  jmp outer
done:
  ret v90
'''


def matrix(kind):
    prefix = []
    row = 'v0'
    if kind != 'positive':
        if kind == 'negative': prefix += ['sub v100, 0, v0']
        elif kind == 'zero': prefix += ['mul v100, v0, 0']
        else: prefix += ['mov v100, v0']
        for i in range(6):
            if kind == 'shift': prefix += [f'shl v{101+i}, v{100+i}, 12']
            elif kind == 'addsh': prefix += [f'addsh v{101+i}, 0, v{100+i}, 12']
            else: prefix += [f'mul v{101+i}, v{100+i}, 4096']
        prefix += ['add v107, v106, v0']
        row = 'v107'
    lines = ['func matrix(v90)', 'entry:', 'const v0, 0', 'jmp h1',
             'h1:', 'lt v2, v0, 2', 'br v2, b1, x1',
             'b1:', 'const v3, 0', 'jmp h2',
             'h2:', 'lt v5, v3, 2', 'br v5, b2, x2',
             'b2:', 'const v6, 0', 'const v7, 0', 'jmp h3',
             'h3:', 'lt v9, v7, 2', 'br v9, b3, x3', 'b3:', *prefix,
             f'mul v11, {row}, 2', 'add v12, v11, v7', 'add v12, v12, 16', 'load v13, v12',
             'mul v16, v7, 2', 'add v17, v16, v3', 'add v18, v17, 128', 'load v19, v18',
             'mul v20, v13, v19', 'add v6, v6, v20', 'add v7, v7, 1', 'jmp h3',
             'x3:', 'mul v26, v0, 2', 'add v27, v26, 256', 'add v28, v27, v3', 'store v28, v6',
             'add v3, v3, 1', 'jmp h2', 'x2:', 'add v0, v0, 1', 'jmp h1', 'x1:', 'ret v90']
    return '\n'.join(lines) + '\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--kit-free', action='store_true')
    parser.add_argument('--source-root', type=Path, default=ROOT)
    parser.add_argument('--only', choices=('store', 'matrix', 'all'), default='all')
    parser.add_argument('--reuse-driver', action='store_true')
    parser.add_argument('--evidence-dir', type=Path, default=ROOT/'build/final-safety')
    args = parser.parse_args()
    source = args.source_root.resolve()/'src'
    out = args.evidence_dir.resolve(); out.mkdir(parents=True, exist_ok=True)
    (out/'driver.cpp').write_text(DRIVER)
    names = ('kir.cpp','ssa.cpp','cfg.cpp','passes.cpp','backend.cpp','sim.cpp','matmul.cpp','row_pairs.cpp')
    command = shlex.split(os.environ.get('CXX','c++')) + ['-std=c++17','-O1','-Wall','-Wextra',
              '-Werror','-pedantic','-I'+str(source),str(out/'driver.cpp'),
              *(str(source/n) for n in names),'-o',str(out/'driver')]
    if not args.reuse_driver: subprocess.run(command, check=True)
    cases = []
    if args.only != 'matrix': cases.append(('store-edge-growth','store',STORE,True))
    if args.only != 'store':
        cases += [(f'matrix-{kind}','matrix',matrix(kind),kind in ('positive','zero'))
                  for kind in ('positive','mul','negative','shift','addsh','zero')]
        cases += [('matrix-dead-ssa','matrix',DEAD,False),
                  ('row-dead-ssa','row',DEAD,False), ('row-positive','row',ROW,True),
                  ('matrix-dead-junk','matrix',matrix('positive')+
                   'dead:\n  mov v999999, v765432\n  const v888888, 7\n  jmp dead\n',True)]
    K = None
    if not args.kit_free:
        kit=Path(os.environ.get('KIT',ROOT.parent/'official-LLH-26/Compilers/COMP10'))
        sys.path.insert(0,str(kit)); import kirlib as K
    records=[]; comparisons=0
    for name,mode,text,expected in cases:
        target=out/name;target.mkdir(exist_ok=True);(target/'original.kir').write_text(text)
        result=subprocess.run([str(out/'driver'),mode,str(int(expected)),str(target)],input=text,
                              text=True,capture_output=True,timeout=60)
        assert result.returncode==0 and not result.stderr,(name,result.returncode,result.stderr[-6000:])
        count=int(result.stdout)
        if mode=='store': assert count==4
        if K is not None and count:
            original=K.compile_program(K.parse_program(text))
            for i in range(count):
                candidate=K.compile_program(K.load_program(str(target/f'{i}.kir')))
                for trial in range(20):
                    values=[(0,1,0xffffffff,0x80000000)[trial%4]]
                    words=[(j*2654435761+trial)&0xffffffff for j in range(4096)]
                    a=K.execute(original,values,[(0,words)],{},100000)
                    b=K.execute(candidate,values,[(0,words)],{},100000)
                    assert K.first_difference(a,b) is None,(name,i,trial,K.first_difference(a,b))
                    comparisons+=1
        records.append(dict(name=name,candidates=count,accepted=expected))
        print('PASS',name,'candidates',count,flush=True)
    report=dict(cases=records,official_comparisons=comparisons,
                local_comparisons=sum(r['candidates']*20 for r in records),
                source_sha256={name:hashlib.sha256((source/name).read_bytes()).hexdigest() for name in names})
    (out/'result.json').write_text(json.dumps(report,indent=2)+'\n')
    print(f'PASS {len(records)} memory-safety regressions; {comparisons} official comparisons',flush=True)


if __name__=='__main__':main()
