#!/usr/bin/env python3
"""Direct two-row proof gates and exhaustive bounded trip-domain equivalence.

Checks recipes directly, without optimizer selection/fallback. --kit-free uses
local Sim only; default uses the independent official interpreter. CXX accepts
compiler/sanitizer flags. Artifacts and exact source hashes stay in build/.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import random
import re
import shlex
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
DRIVER = r'''
#include "passes.h"
#include "backend.h"
#include <algorithm>
#include <fstream>
#include <iostream>
#include <iterator>
#include <stdexcept>
using namespace kopt;
void need(bool b,const std::string &s){if(!b)throw std::runtime_error(s);}
int main(int argc,char **argv){try{
 need(argc==5,"cfg expected outputdir kitfree");
 std::string t((std::istreambuf_iterator<char>(std::cin)),{}),e;
 std::ifstream f(argv[1]);std::string cfg((std::istreambuf_iterator<char>(f)),{});
 Program p;Machine m;need(parseProgram(t,p,e),e);need(parseMachine(cfg,m,e),e);
 const std::string before=printProgram(p);
 auto v=rowPairAlternatives(p),again=rowPairAlternatives(p);
 need((!v.empty())==(std::string(argv[2])=="1"),"acceptance gate");
 need(v.size()==again.size()&&printProgram(p)==before,"input changed/repeat acceptance");
 if(!v.empty()){
  Program permuted=p;
  auto index=[&](int b){return b<=0?b:static_cast<int>(p.blocks.size())-b;};
  std::reverse(permuted.blocks.begin()+1,permuted.blocks.end());
  for(Block &b:permuted.blocks)for(Instr &x:b.ins)
   for(int k=0;k<2;++k)if(x.target[k]>=0)x.target[k]=index(x.target[k]);
  const auto moved=rowPairAlternatives(permuted);
  need(moved.size()==v.size(),"layout changed acceptance");
  for(size_t i=0;i<v.size();++i)need(printProgram(v[i])==printProgram(moved[i]),"layout dependent recipe");
 }
 size_t n=0;
 for(size_t i=0;i<v.size();++i){
  need(v[i].name==p.name&&v[i].params==p.params,"metadata");
  need(printProgram(v[i])==printProgram(again[i]),"nondeterminism");
  Func ir;need(buildSSA(v[i],ir,e),e);need(verifyFunc(ir).empty(),verifyFunc(ir));
  auto save=[&](const Program &q){
   Func check;need(buildSSA(q,check,e),e);need(verifyFunc(check).empty(),verifyFunc(check));
   std::ofstream out(std::string(argv[3])+"/"+std::to_string(n++)+".kir");out<<printProgram(q);
   if(std::string(argv[4])=="1"){
    SimProgram a(p),b(q);
    for(uint32_t arg=0;arg<32;++arg)for(uint32_t hi:{0u,0x80000000u,0xffffffe0u}){
     Input in;in.args.assign(p.params.size(),0x76543210u);
     if(!in.args.empty())in.args[0]=arg|hi;
     if(in.args.size()>1)in.args[1]=0x87654321u;
     if(in.args.size()>2)in.args[2]=0xfedcba98u;
     std::vector<uint32_t>w(kMemWords);for(uint32_t j=0;j<kMemWords;++j)w[j]=(j*2654435761u)^arg^hi;
     in.segments.push_back({0,w});in.vin[1]={7,9};
     auto x=a.run(in,30000,false),y=b.run(in,30000,false);
     need(x.status!=Status::TIMEOUT&&y.status!=Status::TIMEOUT,"timeout");
     need(compareRuns(x,y).empty(),compareRuns(x,y));
    }
   }
  };
  save(v[i]);
  computeIVRanges(ir);computeVRP(ir);instSimplify(ir);dce(ir);fuseOps(ir,m,true);
  for(int mode=0;mode<4;++mode){
   Func copy=ir;BackendOptions bo;bo.preSchedule=mode!=0;bo.bottomUpSchedule=mode>=2;
   bo.spillToK=mode==3&&canSpillToScratch(copy);save(lowerToProgram(copy,m,bo));
  }
 }
 std::cout<<n<<"\n";
}catch(const std::exception &e){std::cerr<<e.what()<<"\n";return 1;}}
'''


def source(rows=8, cols=8, stride=8, a=0, b=512, c=768, count=None, ret='v1'):
    count = f'const v1,{rows}' if count is None else count
    return f'''func arbitrary_kernel(v0,v90,v91)
entry:
 {count}
 const v4,0
 jmp outer
outer:
 lt v5,v4,v1
 br v5,init,done
init:
 const v6,0
 const v7,0
 jmp inner
inner:
 lt v8,v7,{cols}
 br v8,body,store
body:
 mul v9,v4,{stride}
 add v9,v9,{a}
 add v10,v9,v7
 load v11,v10
 add v12,{b},v7
 load v13,v12
 mul v14,v11,v13
 add v6,v6,v14
 add v7,v7,1
 jmp inner
store:
 add v17,{c},v4
 store v17,v6
 add v4,v4,1
 jmp outer
done:
 ret {ret}
'''


def fixtures():
    cases = []
    def add(name,text,ok=True,exhaustive=False): cases.append((name,text,ok,exhaustive))
    # Exhaust every literal trip combination, including empty loops and tails.
    for rows in range(17):
        for cols in range(17):
            add(f'domain-{rows}-{cols}',source(rows,cols,stride=cols+1))
    for cols in range(17):
        add(f'masked-{cols}',source(cols=cols,stride=19,count='and v1,v0,15\nadd v1,v1,1'),exhaustive=True)
    for mask in (0,1,2,3,4,5,7,8,10,15,16):
        add(f'mask-{mask}',source(count=f'and v1,v0,{mask}'),exhaustive=True)
    add('overlapping-A-rows',source(rows=16,cols=16,stride=1))
    add('strided-shift-address',source(stride=16).replace('mul v9,v4,16','shl v9,v4,4'))
    add('MAC-source',source().replace('mul v14,v11,v13\n add v6,v6,v14','mac v6,v11,v13,v6'))
    add('commuted-product-and-sum',source().replace('mul v14,v11,v13','mul v14,v13,v11').replace('add v6,v6,v14','add v6,v14,v6'))
    add('last-valid-word',source(a=3800,b=4000,c=4080,rows=16,cols=8,stride=8))
    add('invariant-return-extra-arithmetic',source(ret='v92').replace('done:\n','done:\n xor v92,v90,v91\n mul v92,v92,v0\n'))
    add('invariant-return-defined-inside',source(ret='v92').replace('outer:\n','outer:\n xor v92,v90,v91\n'))
    add('zero-parameters',source(ret='2147483648').replace('(v0,v90,v91)','()'))
    add('eight-parameters',source(ret='v92').replace('(v0,v90,v91)','(v0,v90,v91,v1,v4,v6,v7,v11)').replace(
        'done:\n','done:\nselect v92,v90,v91,v0\n'))
    add('wrapped-intermediate-exact-address',source().replace('add v10,v9,v7','sub v10,v9,1\n add v10,v10,v7\n add v10,v10,1'))
    # Layout/register renaming never supplies recognition information.
    t=source(count='and v1,v0,15\nadd v1,v1,1')
    ren={n:999999-103*i for i,n in enumerate(sorted(set(re.findall(r'v(\d+)',t)),key=int))}
    t=re.sub(r'v(\d+)',lambda m:'v'+str(ren[m[1]]),t).replace('arbitrary_kernel','renamed_dot')
    parts=re.split(r'(?m)^(\w+):\n',t); blocks=list(zip(parts[1::2],parts[2::2]))
    tail=blocks[1:];random.Random(93167).shuffle(tail)
    add('renamed-shuffled',parts[0]+''.join(n+':\n'+v for n,v in [blocks[0],*tail]),exhaustive=True)
    for name,kwargs in [('A-B-overlap',dict(b=20)),('A-C-overlap',dict(c=40)),('B-C-overlap',dict(c=516)),
                        ('A-invalid',dict(a=4096)),('B-invalid',dict(b=4096)),('C-invalid',dict(c=4096)),
                        ('A-negative',dict(a=-1)),('B-negative',dict(b=-1)),('C-negative',dict(c=-1)),
                        ('A-end-invalid',dict(a=4050)),('B-end-invalid',dict(b=4092)),('C-end-invalid',dict(c=4092)),
                        ('stride-wrap',dict(stride=0x80000000)),('rows17',dict(rows=17)),('cols17',dict(cols=17)),
                        ('negative-inner',dict(cols=-1)),('zero-stride',dict(stride=0))]:
        add(name,source(**kwargs),False)
    for name,old,new in [
        ('row-start','const v4,0','const v4,1'),('col-start','const v7,0','const v7,1'),
        ('sum-start','const v6,0','const v6,1'),('row-step','add v4,v4,1','add v4,v4,2'),
        ('col-step','add v7,v7,1','add v7,v7,2'),('dynamic-stride','mul v9,v4,8','mul v9,v4,v90'),
        ('dynamic-A','add v9,v9,0','add v9,v9,v90'),('dynamic-B','add v12,512,v7','add v12,v90,v7'),
        ('dynamic-C','add v17,768,v4','add v17,v90,v4'),('wrong-reduction','add v6,v6,v14','xor v6,v6,v14'),
        ('scaled-reduction','mul v14,v11,v13','mul v14,v11,v13\nadd v14,v14,1'),
        ('extra-load','load v11,v10','load v11,v10\nload v95,400'),
        ('extra-store','load v11,v10','load v11,v10\nstore 400,v90'),
        ('volatile-load','load v11,v10','vload v11,v10'),('volatile-store','store v17,v6','vstore v17,v6'),
        ('dead-div','mul v14,v11,v13','mul v14,v11,v13\ndiv v95,v90,2'),
        ('dead-mod','mul v14,v11,v13','mul v14,v11,v13\nmod v95,v90,v91'),
        ('side-entry','jmp outer','br v90,outer,body'),
        ('wrong-store-value','store v17,v6','store v17,v14'),
        ('escape-row','ret v1','ret v4'),('escape-col','ret v1','ret v7'),
        ('escape-sum','ret v1','ret v6'),('escape-load','ret v1','ret v11'),
        ('live-extra-recurrence','add v7,v7,1','add v7,v7,1\nadd v92,v92,1'),
    ]:
        t=source().replace(old,new)
        if name=='live-extra-recurrence':t=t.replace('ret v1','ret v92')
        add(name,t,False)
    add('raw-count',source(count='mov v1,v0'),False)
    add('masked-17',source(count='and v1,v0,16\nadd v1,v1,1'),False)
    add('masked-wrap',source(count='and v1,v0,15\nadd v1,v1,-1'),False)
    add('row-dependent-count',source().replace('lt v5,v4,v1','and v1,v4,15\nlt v5,v4,v1'),False)
    add('extra-escaping-arithmetic',source(ret='v92').replace('done:\n','done:\n add v92,v4,v90\n'),False)
    add('extra-block',source().replace('jmp outer','jmp extra\nextra:\njmp outer',1),False)
    add('oversize',source().replace('entry:\n','entry:\n'+'add v99,v99,1\n'*160),False)
    return cases


def generated(count, seed):
    """Independent interval oracle plus structural positive/negative mutations."""
    rng = random.Random(seed)
    cases = []
    for i in range(count):
        cols = rng.randrange(17)
        stride = rng.randrange(1, 33)
        mask = rng.choice((0, 1, 3, 5, 7, 8, 10, 15, 16))
        offset = rng.randrange(17-mask)
        rows = mask + offset
        masked = bool(rng.randrange(2))
        count_text = f'and v1,v0,{mask}\nadd v1,v1,{offset}' if masked else None
        if not masked:
            rows = rng.randrange(17)
        bases = rng.sample(range(0, 4080), 3)
        if i % 3 == 0:
            # Separated bands give many positive instances, including addresses
            # in scratch. Other instances independently exercise interval gates.
            bands = [0, 1400, 3072]
            rng.shuffle(bands)
            bases = [v + rng.randrange(100) for v in bands]
        a, b, c = bases
        end_a = a + (max(rows, 1)-1)*stride + max(cols, 1)
        end_b = b + max(cols, 1)
        end_c = c + max(rows, 1)
        intervals = [(a, end_a), (b, end_b), (c, end_c)]
        ok = (max(end_a, end_b, end_c) <= 4096 and
              all(x[1] <= y[0] or y[1] <= x[0]
                  for j, x in enumerate(intervals) for y in intervals[j+1:]))
        t = source(rows, cols, stride, a, b, c, count=count_text)
        mutation = i % 11
        if mutation == 0:
            t = t.replace('ret v1', 'ret v92').replace(
                'done:\n', 'done:\n xor v92,v90,v91\nshl v92,v92,v0\nmac v92,v92,v90,v91\n')
        elif mutation == 1:
            t = t.replace('load v11,v10', 'load v11,v10\nstore 2000,v90')
            ok = False
        elif mutation == 2:
            t = t.replace('const v6,0', 'const v6,1')
            ok = False
        elif mutation == 3:
            t = t.replace('ret v1', 'ret v92').replace('done:\n', 'done:\nadd v92,v4,v90\n')
            ok = False
        elif mutation == 4:
            t = t.replace('mul v14,v11,v13\n add v6,v6,v14', 'mac v6,v13,v11,v6')
        elif mutation == 5:
            t = t.replace('add v7,v7,1', 'add v7,v7,2')
            ok = False
        elif mutation == 6:
            t = t.replace('mul v14,v11,v13', 'div v14,v11,v13')
            ok = False
        elif mutation == 7:
            t = t.replace(f'add v12,{b},v7', 'add v12,v90,v7')
            ok = False
        elif mutation == 8:
            # Commuted address arithmetic retains exactly the source equation.
            t = t.replace(f'add v12,{b},v7', f'add v12,v7,{b}')
        elif mutation == 9:
            t = t.replace('load v13,v12', 'load v13,v12\nvstore 1,v90')
            ok = False
        # Arbitrary names, sparse register IDs, and non-entry block layouts.
        ids = sorted(set(re.findall(r'v(\d+)', t)), key=int)
        remap = dict(zip(ids, rng.sample(range(100, 999999), len(ids))))
        t = re.sub(r'v(\d+)', lambda m: 'v'+str(remap[m[1]]), t)
        t = t.replace('arbitrary_kernel', f'generated_{seed}_{i}')
        parts = re.split(r'(?m)^(\w+):\n', t)
        blocks = list(zip(parts[1::2], parts[2::2]))
        tail = blocks[1:]
        rng.shuffle(tail)
        t = parts[0]+''.join(n+':\n'+v for n,v in [blocks[0], *tail])
        cases.append((f'fuzz-{seed}-{i}', t, ok, masked))
    return cases


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--kit-free',action='store_true')
    ap.add_argument('--reuse-driver',action='store_true')
    ap.add_argument('--quick',action='store_true',help='skip exhaustive 17x17 literal domain')
    ap.add_argument('--fuzz',type=int,default=0)
    ap.add_argument('--seed',type=int,default=931671)
    ap.add_argument('--only-fuzz',action='store_true')
    ap.add_argument('--evidence-dir',type=Path)
    a=ap.parse_args()
    evidence=a.evidence_dir or ROOT/'build'/'row-pairs-direct';evidence.mkdir(parents=True,exist_ok=True)
    driver=evidence/'driver';(evidence/'driver.cpp').write_text(DRIVER)
    if not a.reuse_driver:
        src=[str(ROOT/'src'/name) for name in ('row_pairs.cpp','ssa.cpp','cfg.cpp','kir.cpp',
                                               'passes.cpp','sim.cpp','backend.cpp')]
        subprocess.run([*shlex.split(os.environ.get('CXX','c++')),'-std=c++17','-O1','-Wall','-Wextra','-Werror','-pedantic','-I'+str(ROOT/'src'),str(evidence/'driver.cpp'),*src,'-o',str(driver)],check=True)
    if a.kit_free:
        sys.path.insert(0,str(ROOT/'tools'));from smoke import BASE_MACHINE
        cfg=evidence/'machine.cfg';cfg.write_text(''.join(f'{k} = {v}\n' for k,v in BASE_MACHINE.items()))
    else:
        kit=Path(os.environ.get('KIT',ROOT.parent/'official-LLH-26/Compilers/COMP10')).resolve()
        sys.path.insert(0,str(kit));import kirlib as K
        cfg=kit/'machines/machine_slow_memory.cfg';mc=K.load_machine(str(cfg))
    comparisons=0;records=[];rng=random.Random(93167)
    patterns=[[rng.getrandbits(32) for _ in range(4096)], [0xffffffff]*4096,
              [0x80000000 if j%2 else 0x7fffffff for j in range(4096)],
              [(j*2654435761)&0xffffffff for j in range(4096)]]
    cases = ([] if a.only_fuzz else fixtures()) + generated(a.fuzz, a.seed)
    for name,text,expected,exhaustive in cases:
        if a.quick and name.startswith('domain-'):continue
        out=evidence/name;out.mkdir(exist_ok=True);(out/'original.kir').write_text(text)
        run=subprocess.run([str(driver),str(cfg),str(int(expected)),str(out),str(int(a.kit_free))],input=text,text=True,capture_output=True,timeout=60)
        assert run.returncode==0,(name,run.stderr)
        n=int(run.stdout);assert n==(10 if expected else 0),(name,n)
        if expected and not a.kit_free:
            parsed=K.parse_program(text)
            original=K.compile_program(parsed)
            args=range(32) if exhaustive else (0,1,15,16)
            trials=[]
            for j in args:
                for hi,words in zip((0,0,0x80000000,0xffffffe0),patterns):
                    values=([j|hi,0x87654321,0xfedcba98]+[0x76543210]*8)[:len(parsed.params)]
                    inp=(values,[(0,words)],{1:[7,9]})
                    ref=K.execute(original,*inp,30000)
                    assert ref.status=='RET',(name,'source timeout/trap')
                    trials.append((inp,ref))
            for i in range(n):
                q=K.load_program(str(out/f'{i}.kir'));K.check_machine_features(q,mc);candidate=K.compile_program(q)
                for inp,ref in trials:
                    got=K.execute(candidate,*inp,30000,want_trace=i in (0,5))
                    diff=K.first_difference(ref,got);assert not diff,(name,i,inp[0],diff)
                    # Raw recipes must really eliminate one vector load per pair.
                    if i in (0,5):
                        rows=int(name.split('-')[1]) if name.startswith('domain-') else None
                        if rows is not None:
                            cols=int(name.split('-')[2]);want=(3*(rows//2)+2*(rows%2))*cols
                            assert sum(candidate.code[pc][0]==K.LOAD for pc in got.trace)==want,(name,i,'load count')
                    comparisons+=1
        elif expected:comparisons+=n*96
        records.append(dict(name=name,accepted=expected,candidates=n))
        if len(records)%30==0:print(f'checked {len(records)} fixtures / {comparisons} comparisons',flush=True)
    report=dict(fixtures=len(records),accepted=sum(r['accepted'] for r in records),comparisons=comparisons,
                oracle='local Sim' if a.kit_free else 'official kirlib',records=records,
                sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [ROOT/'src/row_pairs.cpp',ROOT/'src/optimizer.cpp',ROOT/'src/passes.h']})
    filename = f'fuzz-{a.seed}.json' if a.only_fuzz else 'local.json' if a.kit_free else 'evidence.json'
    (evidence/filename).write_text(json.dumps(report,indent=2)+'\n')
    print(f"PASS {report['fixtures']} fixtures, {report['accepted']} accepted; {comparisons} {report['oracle']} comparisons",flush=True)

if __name__=='__main__':
    sys.dont_write_bytecode=True
    main()
