#!/usr/bin/env python3
"""Direct select factoring gates; adapted from build/check-selects.py.

Snapshots --source-root/src before compiling. No optimizer pipeline or fallback.
--kit-free imports no external kit: SSA/structure/determinism and local Sim checks
are not an independent oracle. Default mode additionally uses official kirlib.
All generated sources, binaries, fixtures, outputs, and hashes stay in build/.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import random
import shlex
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True
DRIVER = r'''
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <iterator>
#include <stdexcept>
#include <vector>
#include "passes.h"
#include "backend.h"
namespace kopt { bool factorSelects(Func &); }
using namespace kopt;
void need(bool b,const std::string &s){if(!b)throw std::runtime_error(s);}
void valid(Func &f){const auto e=verifyFunc(f);need(e.empty(),e);}
int selects(const Func &f){int n=0;
 for(const BB &b:f.bb){if(b.alive){
  for(const Inst &x:b.insts){n+=x.op==OP_SELECT;}
 }}
 return n;
}
std::string effects(Func &f){std::string s;
 for(size_t i=0;i<f.bb.size();++i){if(f.bb[i].alive){for(const Inst &x:f.bb[i].insts){
 if(isMemOp(x.op)||x.op==OP_DIV||x.op==OP_MOD||isTerminator(x.op)){
  s+=std::to_string(i)+":"+opName(x.op)+":";
  for(int a=0;a<x.n;++a)s+=x.a[a].isConst?"c"+std::to_string(x.a[a].c)+",":"v"+std::to_string(x.a[a].v)+",";
  s+=std::to_string(x.tgt[0])+","+std::to_string(x.tgt[1])+";";
 }
 }}}
 return s;
}
int main(int argc,char **argv){try{
 need(argc==6,"cfg new-values removed-selects mode poison");
 std::string text((std::istreambuf_iterator<char>(std::cin)),{}),err;
 std::ifstream mf(argv[1]);std::string cfg((std::istreambuf_iterator<char>(mf)),{});
 Program p;Machine m;need(parseProgram(text,p,err),err);need(parseMachine(cfg,m,err),err);
 const int expected=std::atoi(argv[2]),removed=std::atoi(argv[3]),mode=std::atoi(argv[4]);
 auto make=[&](std::string &ssa){
  Func f;need(buildSSA(p,f,err),err);valid(f);f.resolveAll();
  const int nv=f.nvals,ns=selects(f);const auto before=effects(f);
  // Deliberately stale facts for an unused load's address: ADD(a,0) -> AND(a,4095).
  // A successful factor must clear both caches before trap-sensitive DCE.
  if(std::atoi(argv[5])){
   Func poison=f;
   for(BB &b:poison.bb)for(Inst &x:b.insts)
    if(x.op==OP_ADD&&x.a[1].isC(0)){x.op=OP_AND;x.a[1]=Opnd::cst(4095);}
   computeIVRanges(poison);computeVRP(poison);
  }else{computeIVRanges(f);computeVRP(f);}
  const bool changed=factorSelects(f);valid(f);
  need(f.nvals-nv<=64,"new-value cap exceeded");
  if(expected>=0)need(f.nvals-nv==expected,"unexpected new-value count "+std::to_string(f.nvals-nv));
  if(removed>=0)need(ns-selects(f)==removed,"nested budget exceeded or under-applied");
  need(expected!=0||removed!=0||!changed,"negative gate changed graph");
  need(effects(f)==before,"effect/trap instruction changed or moved");
  ssa=dumpFunc(f);BackendOptions bo;
  bo.preSchedule=mode!=0;bo.bottomUpSchedule=mode==2;
  bo.spillToK=mode==3&&canSpillToScratch(f);
  Program out=lowerToProgram(f,m,bo);Func rebuilt;
  need(buildSSA(out,rebuilt,err),err);valid(rebuilt);return out;
 };
 std::string ssa,again;Program out=make(ssa),repeat=make(again);
 need(ssa==again&&printProgram(out)==printProgram(repeat),"nondeterministic output");
 SimProgram a(p),b(out);auto inputs=generateInputs(static_cast<int>(p.params.size()),160,2415);
 const uint32_t edge[]={0,1,2,31,32,33,4095,4096,0x7fffffffu,0x80000000u,0xffffffffu};
 for(uint32_t c:edge)for(uint32_t x:edge){Input in;
  for(size_t j=0;j<p.params.size();++j)in.args.push_back(j==0?c:j==1?x:j==2?0x80000000u:j==3?0xffffffffu:j==4?32u:33u);
  inputs.push_back(in);
 }
 for(Input &in:inputs){
  in.segments.push_back({0,{0,1,0xffffffffu,0x80000000u,0x7fffffffu,33,32,31}});
  in.segments.push_back({4095,{17}});in.vin[1]={11,23,37};
  auto x=a.run(in,100000,false),y=b.run(in,100000,false);
  need(x.status!=Status::TIMEOUT&&y.status!=Status::TIMEOUT,"timeout");
  need(compareRuns(x,y).empty(),compareRuns(x,y));
 }
 std::cerr<<inputs.size()<<" local comparisons\n";std::cout<<printProgram(out);
 }catch(const std::exception &e){std::cerr<<"FAIL "<<e.what()<<"\n";return 1;}}
'''


def program(body):
    return 'func generated(v0,v1,v2,v3,v4,v5)\nentry:\n' + body + '\n'


def fixtures():
    cases = []
    def add(name, body, created=-1, removed=-1, poison=0):
        cases.append((name, program(body), created, removed, poison))
    ops = 'add sub mul and or xor shl shr lt eq select mac addsh'.split()
    for op in ops:
        arity = 3 if op in ('select', 'mac') else 2
        for varied in range(arity):
            left = ['v1', 'v2', 'v3'][:arity]
            right = left[:]
            right[varied] = 'v4'
            if op == 'addsh':
                left += ['13']; right += ['13']
            add(f'{op}-position-{varied}',
                f'{op} v10,'+','.join(left)+'\n'+f'{op} v11,'+','.join(right)+
                '\nselect v12,v0,v10,v11\nret v12', 1)
    for op in 'add mul and or xor eq'.split():
        add(op+'-commuted', f'{op} v10,v1,v2\n{op} v11,v3,v1\nselect v12,v0,v10,v11\nret v12', 1)
    for op in 'sub shl shr lt'.split():
        add(op+'-preserve-order', f'{op} v10,v1,v2\n{op} v11,v3,v1\nselect v12,v0,v10,v11\nret v12', 0, 0)
    add('select-preserve-order', 'select v10,v1,v2,v3\nselect v11,v2,v1,v3\nselect v12,v0,v10,v11\nret v12', 0, 0)
    add('mac-commute-product', 'mac v10,v1,v2,v3\nmac v11,v4,v1,v3\nselect v12,v0,v10,v11\nret v12', 1)
    add('mac-preserve-accumulator', 'mac v10,v1,v2,v3\nmac v11,v1,v3,v2\nselect v12,v0,v10,v11\nret v12', 0, 0)
    add('addsh-preserve-order', 'addsh v10,v1,v2,13\naddsh v11,v3,v1,13\nselect v12,v0,v10,v11\nret v12', 0, 0)
    add('addsh-distinct-shift', 'addsh v10,v1,v2,13\naddsh v11,v1,v3,14\nselect v12,v0,v10,v11\nret v12', 0, 0)
    pair = 'add v10,v1,v2\nadd v11,v1,v3\nselect v12,v0,v10,v11\n'
    add('multiuser', pair+'store 101,v10\nret v12', 0, 0)
    add('multiroot', pair+'store 101,v12\nxor v13,v2,v4\nxor v14,v2,v5\nselect v15,v1,v13,v14\nret v15', 2)
    add('nested-both', 'select v10,v0,v1,v2\nselect v11,v0,v2,v3\nselect v12,v0,v10,v11\nret v12', 0, 2)
    add('nested-multiuser', 'select v10,v0,v1,v2\nselect v11,v0,v10,v3\nstore 100,v10\nret v11', 0, 0)
    add('snapshot-factor-then-nested', pair+'select v13,v0,v12,v4\nret v13', 1)
    add('snapshot-nested-chain', 'select v10,v0,v1,v2\nselect v11,v0,v10,v3\nselect v12,v0,v4,v11\nret v12', 0)
    add('snapshot-reintroduced-use', pair+'add v13,v10,v4\nselect v14,v0,v12,v13\nret v14')
    for prefix, effect in [
        ('bad-load','store 100,v1\nload v70,4096\n'),
        ('variable-load','store 100,v1\nload v70,v1\n'),
        ('bad-store','store 100,v1\nstore 4096,v2\n'),
        ('volatile','vload v70,1\nvstore 1,v70\n'),
        ('div','store 100,v1\ndiv v70,v2,v1\nstore 101,v70\n'),
        ('mod','mod v70,v2,v1\nstore 101,v70\n'),
    ]:
        add('effect-'+prefix, effect+pair+'ret v12', 1)
    add('explicit-trap',pair+'store 101,v12\ntrap v1',1)
    add('poison-range-cache','add v70,v1,0\nload v71,v70\n'+pair+'ret v12',1,poison=1)
    add('reject-load-factor','load v10,v1\nload v11,v2\nselect v12,v0,v10,v11\nret v12',0,0)
    add('reject-div-factor','div v10,v1,v2\ndiv v11,v1,v3\nselect v12,v0,v10,v11\nret v12',0,0)
    add('loop', 'and v20,v0,7\nmov v21,0\nmov v22,0\njmp head\nhead:\nlt v23,v21,v20\nbr v23,body,exit\nbody:\nand v24,v21,1\nadd v10,v22,v2\nadd v11,v22,v3\nselect v22,v24,v10,v11\nadd v21,v21,1\njmp head\nexit:\nret v22',1)
    add('both-branch-definitions','br v0,yes,no\nyes:\n'+pair+'jmp join\nno:\nsub v10,v2,v1\nsub v11,v3,v1\nselect v12,v4,v10,v11\njmp join\njoin:\nret v12',2)
    body = []
    for i in range(65):
        r = 100+3*i
        body += [f'add v{r},v1,v2',f'add v{r+1},v1,v3',f'select v{r+2},v0,v{r},v{r+1}',f'store {100+i},v{r+2}']
    add('factor-budget-64','\n'.join(body)+'\nret v1',64)
    body = []
    for i in range(63):
        r = 100+2*i
        body += [f'select v{r},v0,v1,v2',f'select v{r+1},v0,v{r},v3',f'store {100+i},v{r+1}']
    body += ['select v500,v0,v1,v2','select v501,v0,v2,v3','select v502,v0,v500,v501','store 200,v502',
             'select v503,v0,v1,v2','select v504,v0,v503,v3','store 201,v504','ret v1']
    add('nested-budget-63-plus-two-plus-one','\n'.join(body),0,64)
    return cases


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--kit-free', action='store_true')
    ap.add_argument('--source-root', type=Path, default=ROOT)
    args = ap.parse_args()
    source = args.source_root.resolve()
    if source.name != 'src': source /= 'src'
    out = ROOT/'build/select-factor-tests'
    snap = out/'src'; snap.mkdir(parents=True, exist_ok=True)
    hashes = {}
    for path in sorted(source.iterdir()):
        if path.suffix not in ('.cpp','.h'): continue
        data=path.read_bytes(); (snap/path.name).write_bytes(data)
        hashes[path.name]=hashlib.sha256(data).hexdigest()
    assert 'select_factor.cpp' in hashes, 'source snapshot lacks select_factor.cpp'
    (out/'snapshot.json').write_text(json.dumps(dict(source=str(source),sha256=hashes),indent=2)+'\n')
    sys.path.insert(0,str(ROOT/'tools'))
    from smoke import BASE_MACHINE
    cfg=out/'machine.cfg'; cfg.write_text(''.join(f'{k} = {v}\n' for k,v in BASE_MACHINE.items()))
    driver=out/'driver.cpp'; driver.write_text(DRIVER)
    binary=out/'driver'
    sources=[str(snap/f'{name}.cpp') for name in ('kir','ssa','cfg','passes','backend','sim','select_factor')]
    subprocess.run(shlex.split(os.environ.get('CXX','c++'))+['-std=c++17','-O0','-Wall','-Wextra','-Werror','-pedantic',f'-I{snap}',str(driver),*sources,'-o',str(binary)],check=True)
    K=None
    if not args.kit_free:
        kit=Path(os.environ.get('KIT',ROOT.parent/'official-LLH-26/Compilers/COMP10'))
        sys.path.insert(0,str(kit)); import kirlib as K
    rng=random.Random(2415)
    edges=[0,1,2,31,32,33,4095,4096,0x7fffffff,0x80000000,0xffffffff]
    inputs=[[c,a,0x80000000,0xffffffff,32,33] for c in edges for a in edges]
    inputs += [[rng.getrandbits(32) for _ in range(6)] for _ in range(100)]
    checks=0; cases=fixtures()
    for name,text,created,removed,poison in cases:
        (out/f'{name}.kir').write_text(text)
        for mode in range(4):
            p=subprocess.run([str(binary),str(cfg),str(created),str(removed),str(mode),str(poison)],input=text,capture_output=True,text=True,timeout=60)
            assert p.returncode==0,(name,mode,p.stderr)
            (out/f'{name}-{mode}.kir').write_text(p.stdout)
            checks+=int(p.stderr.split()[0])
            if K is not None:
                a=K.compile_program(K.parse_program(text)); prog=K.parse_program(p.stdout)
                K.check_machine_features(prog,K.load_machine(str(cfg))); b=K.compile_program(prog)
                for argv in inputs:
                    segments=[(0,[0,1,0xffffffff,0x80000000,0x7fffffff,33,32,31]),(4095,[17])]
                    x=K.execute(a,argv,segments,{1:[11,23,37]},100000)
                    y=K.execute(b,argv,segments,{1:[11,23,37]},100000)
                    assert x.status!='TIMEOUT' and y.status!='TIMEOUT'
                    assert K.first_difference(x,y) is None,(name,mode,argv,K.first_difference(x,y))
        print('PASS',name,flush=True)
    report=dict(fixtures=len(cases),modes=4,local_comparisons=checks,official_comparisons=0 if K is None else len(cases)*4*len(inputs),module_sha256=hashes['select_factor.cpp'])
    (out/'result.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report),flush=True)


if __name__=='__main__': main()
