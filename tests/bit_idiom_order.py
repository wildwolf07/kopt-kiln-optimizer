#!/usr/bin/env python3
"""Bit idioms must construct their DAG in the same order on every compiler."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import random
import shlex
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[1]
sys.dont_write_bytecode=True
DRIVER=r'''
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
 need(argc==3,"reverse output-directory");const bool reverse=std::string(argv[1])=="1";
 const std::string text((std::istreambuf_iterator<char>(std::cin)),{});
 Program p;std::string err;need(parseProgram(text,p,err),err);
 Func f;need(buildSSA(p,f,err),err);instSimplify(f);dce(f);simplifyCFG(f);
 const int first=f.nvals;need(popcountLoops(f),"idiom did not match");
 std::vector<Op> ops;
 for(const BB &b:f.bb)if(b.alive)for(const Inst &x:b.insts)if(x.dst>=first)ops.push_back(x.op);
 std::vector<Op> expected;
 if(reverse){for(int i=0;i<4;++i)for(Op op:{OP_SHR,OP_AND,OP_AND,OP_SHL,OP_OR})expected.push_back(op);
   for(Op op:{OP_SHR,OP_SHL,OP_OR})expected.push_back(op);
 }else expected={OP_SHR,OP_AND,OP_SUB,OP_AND,OP_SHR,OP_AND,OP_ADD,OP_SHR,OP_ADD,OP_AND,OP_MUL,OP_SHR};
 need(ops.size()>=expected.size()&&std::equal(expected.begin(),expected.end(),ops.begin()),"host-dependent idiom emission order");
 Machine m;Rng rng(131313);
 for(int mode=0;mode<4;++mode){
   Func copy=f;BackendOptions bo;bo.preSchedule=mode!=0;bo.bottomUpSchedule=mode==2;bo.spillToK=mode==3;
   const Program q=lowerToProgram(copy,m,bo);SimProgram sim(q);
   for(int i=0;i<256;++i){
     const uint32_t v=i==0?0:i==1?0xffffffffu:i<34?(uint32_t{1}<<(i-2)):uint32_t(rng.next());
     uint32_t want=0;for(unsigned bit=0;bit<32;++bit){if(reverse)want=(want<<1)|((v>>bit)&1u);else want+=(v>>bit)&1u;}
     Input in;in.args={v};const auto got=sim.run(in,100000,false);
     need(got.status==Status::RET&&got.value==want&&got.vlog.empty(),"wrong bit result");
     for(size_t k=0;k<kScratchBase;++k)need(got.mem[k]==0,"changed data memory");
   }
   std::ofstream out(std::string(argv[2])+"/"+std::to_string(mode)+".kir");out<<printProgram(q);need(bool(out),"write result");
 }
 std::cout<<"4 modes / 1024 independent scalar-oracle comparisons\n";
}catch(const std::exception &e){std::cerr<<e.what()<<'\n';return 1;}}
'''


def fixtures():
    return [
      ('clear',False,'''func pc(v0)
entry:
 const v1, 0
 jmp head
head:
 br v0, body, done
body:
 sub v2, v0, 1
 and v0, v0, v2
 add v1, v1, 1
 jmp head
done:
 ret v1
'''),
      ('shift',False,'''func pc(v0)
entry:
 const v1, 0
 jmp head
head:
 br v0, body, done
body:
 and v2, v0, 1
 add v1, v1, v2
 shr v0, v0, 1
 jmp head
done:
 ret v1
'''),
      ('indexed',False,'''func pc(v0)
entry:
 const v1, 0
 const v2, 0
 jmp head
head:
 lt v3, v2, 32
 br v3, body, done
body:
 shr v4, v0, v2
 and v4, v4, 1
 add v1, v1, v4
 add v2, v2, 1
 jmp head
done:
 ret v1
'''),
      ('reverse',True,'''func brv(v0)
entry:
 const v1, 0
 const v2, 0
 jmp head
head:
 lt v3, v2, 32
 br v3, body, done
body:
 shr v4, v0, v2
 and v4, v4, 1
 sub v5, 31, v2
 shl v4, v4, v5
 or v1, v1, v4
 add v2, v2, 1
 jmp head
done:
 ret v1
''')]


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--kit-free',action='store_true')
    ap.add_argument('--source-root',type=Path,default=ROOT)
    ap.add_argument('--evidence-dir',type=Path,default=ROOT/'build/bit-idiom-order')
    a=ap.parse_args();out=a.evidence_dir.resolve();out.mkdir(parents=True,exist_ok=True)
    source=a.source_root.resolve()/'src';(out/'driver.cpp').write_text(DRIVER)
    names=('kir.cpp','ssa.cpp','cfg.cpp','passes.cpp','backend.cpp','sim.cpp')
    subprocess.run([*shlex.split(os.environ.get('CXX','c++')),'-std=c++17','-O1','-Wall','-Wextra','-Werror','-pedantic',
      '-I'+str(source),str(out/'driver.cpp'),*(str(source/n) for n in names),'-o',str(out/'driver')],check=True)
    K=None
    if not a.kit_free:
      sys.path.insert(0,str(Path(os.environ.get('KIT',ROOT.parent/'official-LLH-26/Compilers/COMP10'))));import kirlib as K
    rng=random.Random(131313);values=[0,0xffffffff,0x55555555,0xaaaaaaaa,*[1<<i for i in range(32)]]
    values += [rng.getrandbits(32) for _ in range(220)]
    comparisons=0
    for name,reverse,text in fixtures():
      folder=out/name;folder.mkdir(exist_ok=True)
      p=subprocess.run([str(out/'driver'),str(int(reverse)),str(folder)],input=text,text=True,capture_output=True,timeout=60)
      assert p.returncode==0,(name,p.stderr)
      if K is not None:
        original=K.compile_program(K.parse_program(text))
        for mode in range(4):
          q=K.compile_program(K.load_program(str(folder/f'{mode}.kir')))
          for v in values:
            x=K.execute(original,[v],[],{},100000);y=K.execute(q,[v],[],{},100000)
            want=int(f'{v:032b}'[::-1],2) if reverse else v.bit_count()
            assert y.status=='RET' and y.value==want and K.first_difference(x,y) is None,(name,mode,v)
            comparisons+=1
      print('PASS',name,p.stdout.strip(),flush=True)
    result=dict(fixtures=4,modes=4,local_comparisons=4096,official_comparisons=comparisons,
      source_sha256={n:hashlib.sha256((source/n).read_bytes()).hexdigest() for n in names})
    (out/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True)


if __name__=='__main__':main()
