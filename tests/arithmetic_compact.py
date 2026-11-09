#!/usr/bin/env python3
"""Direct pass tests against the independent official interpreter."""
from pathlib import Path
import os
import random
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
KIT = Path(os.environ.get('KIT', ROOT.parent / 'official-LLH-26/Compilers/COMP10'))
sys.path.insert(0, str(KIT))
import kirlib as K

DRIVER = r'''
#include <fstream>
#include <iostream>
#include <iterator>
#include "backend.h"
#include "passes.h"
using namespace kopt;
int main(int argc, char **argv) {
    if (argc != 3) return 2;
    std::ifstream file(argv[1]); std::string text((std::istreambuf_iterator<char>(file)), {}), err;
    Program p; if (!parseProgram(text, p, err)) return 3;
    if (std::string(argv[2]) == "compact" || std::string(argv[2]) == "tails") {
        p = compactBlocks(p, std::string(argv[2]) == "tails");
    } else {
        Func f; if (!buildSSA(p, f, err)) return 4;
        Machine m;
        if (!shareDivRem(f, m)) return 5;
        err = verifyFunc(f); if (!err.empty()) { std::cerr << err; return 6; }
        p = lowerToProgram(f, m, BackendOptions());
    }
    std::cout << printProgram(p);
}
'''

def main():
    rng = random.Random(991127)
    edges = [0, 1, 2, 7, 8, 31, 0x7fffffff, 0x80000000, 0xffffffff, 0xfffffffe]
    inputs = [(a,b) for a in edges for b in edges]
    inputs += [(rng.getrandbits(32),rng.getrandbits(32)) for _ in range(900)]
    checks = 0
    with tempfile.TemporaryDirectory() as temp:
        td = Path(temp); driver = td / 'driver.cpp'; binary = td / 'driver'
        driver.write_text(DRIVER)
        sources = [str(p) for p in (ROOT/'src').glob('*.cpp') if p.name != 'main.cpp']
        subprocess.run([os.environ.get('CXX','c++'),'-std=c++17','-O1','-I'+str(ROOT/'src'),str(driver),*sources,'-o',str(binary)],check=True)
        fixtures=[]
        for reverse in (False,True):
            ops=['div v2, v0, v1','mod v3, v0, v1']
            if reverse: ops.reverse()
            text='func paired(v0,v1)\nentry:\n  store 11, v0\n  '+ops[0]+'\n  vstore 7, 37\n  '+ops[1]+'\n  store 12, v2\n  store 13, v3\n  add v4, v2, v3\n  ret v4\n'
            fixtures.append((text,'arithmetic'))
        fixtures.append(('''func duplicate(v0,v1)
entry:
  br v0, left, right
left:
  vstore 7, v1
  store 13, v1
  div v2, v0, v1
  ret v2
right:
  vstore 7, v1
  store 13, v1
  div v2, v0, v1
  ret v2
''','compact'))
        fixtures.append(('''func cyclic(v0,v1)
entry:
  and v0, v0, 31
  br v1, left, right
left:
  add v1, v1, v0
  sub v0, v0, 1
  br v0, left, exit
right:
  add v1, v1, v0
  sub v0, v0, 1
  br v0, left, exit
exit:
  vstore 7, v1
  ret v1
''','compact'))
        fixtures.append(('func tails(v0,v1)\nentry:\n  br v0, left, right\nleft:\n  mul v2, v0, 3\n  vstore 7, v2\n  add v3, v2, 7\n  store 13, v3\n  div v4, v3, v1\n  ret v4\nright:\n  mul v2, v0, 5\n  vstore 7, v2\n  add v3, v2, 7\n  store 13, v3\n  div v4, v3, v1\n  ret v4\n','tails'))
        for i,(text,mode) in enumerate(fixtures):
            src=td/'in.kir';src.write_text(text)
            result=subprocess.run([str(binary),str(src),mode],check=True,capture_output=True,text=True)
            a,b=[K.compile_program(K.parse_program(s)) for s in (text,result.stdout)]
            if mode in ('compact','tails'): assert len(b.code)<len(a.code) if hasattr(a,'code') else len(result.stdout)<len(text)
            for args in inputs:
                x=K.execute(a,list(args),[],{},20000)
                if x.status=='TIMEOUT':continue
                y=K.execute(b,list(args),[],{},20*x.steps+1000)
                diff=K.first_difference(x,y)
                assert not diff,(i,args,diff,result.stdout)
                checks+=1
    print('%d independent arithmetic/compact comparisons passed'%checks)
if __name__=='__main__':main()
