#!/usr/bin/env python3
"""Direct rolling-load proof gates, without runPipeline or optimizer fallback.

--source-root snapshots a repository's src/ (or a src directory) before building.
Most fixtures use a raw SSA uninitialized-zero IV. Marked nonzero/wrap fixtures
literalize only const/mov definitions; no range/CFG/optimization cleanup runs.
Full mode uses the independent official interpreter. --kit-free imports no
kirlib and uses tools/smoke.py BASE_MACHINE plus non-independent local Sim checks.
CXX is shell-split, allowing compiler wrappers and sanitizer flags.
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
MODES = (0, 1, 9, 11)  # plain, preallocation, bottom-up, bottom-up+safe scratch
COUNTS = (-3, -1, 0, 1, 2, 3, 5, 8)
DRIVER = r'''
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <iterator>
#include <stdexcept>
#include <utility>
#include <vector>
#include "backend.h"
#include "passes.h"
namespace kopt { bool promoteRollingLoad(Func &); }
using namespace kopt;
void require(bool ok,const std::string &why) { if(!ok) throw std::runtime_error(why); }
void valid(Func &f) {const auto e=verifyFunc(f);require(e.empty(),e);}
void setup(const Program &p,Func &f,bool literals) {
 std::string err;require(buildSSA(p,f,err),err);valid(f);
 if(literals) {
  // Fixture representation only: expose exact constant MOV initializers.
  // Do not simplify phis, arithmetic, control flow, ranges, or memory.
  for(int round=0;round<8;++round) {
   bool changed=false;
   for(const BB &b:f.bb) for(const Inst &x:b.insts)
    if((x.op==OP_CONST||x.op==OP_MOV)&&x.dst>=0) {
     Opnd o=f.resolve(x.a[0]);
     if(o.isConst && f.resolve(Opnd::val(x.dst))!=o) {f.replaceAll(x.dst,o);changed=true;}
    }
   if(!changed)break;
  }
  f.resolveAll();valid(f);
 }
}
using Stores=std::vector<std::pair<int,Inst>>;
Stores stores(const Func &f) {
 Stores result;
 for(int b=0;b<static_cast<int>(f.bb.size());++b)if(f.bb[b].alive)
  for(const Inst &x:f.bb[b].insts)if(x.op==OP_STORE||x.op==OP_VSTORE)result.push_back({b,x});
 return result;
}
void transform(Func &f,bool expected,uint32_t first) {
 const int nv=f.nvals;const Stores before=stores(f);const std::string raw=dumpFunc(f);
 const bool changed=promoteRollingLoad(f);
 require(changed==expected,"promotion gate differs: got "+std::to_string(changed));
 require(f.nvals==nv+(expected?2:0),"expected exactly two new values per promotion");valid(f);
 if(!expected) {require(dumpFunc(f)==raw,"rejected transform changed SSA");return;}
 const Stores after=stores(f);require(before.size()==after.size(),"store removed/added");
 for(size_t i=0;i<before.size();++i) {
  require(before[i].first==after[i].first && before[i].second.op==after[i].second.op,"store moved");
  for(int a=0;a<before[i].second.n;++a)
   require(f.resolve(before[i].second.a[a])==f.resolve(after[i].second.a[a]),"store address/value changed");
 }
 int init=0,phi=0,forwarded=0;
 for(const BB &b:f.bb)if(b.alive) {
  for(const Inst &x:b.insts)if(x.dst==nv) {
   require(x.op==OP_LOAD&&x.a[0].isC(first),"wrong initial read");++init;
  }
  for(const Phi &p:b.phis)if(p.dst==nv+1) {require(p.in.size()==2,"wrong memory phi arity");++phi;}
 }
 for(int v=0;v<nv;++v)if(f.resolve(Opnd::val(v))==Opnd::val(nv+1))++forwarded;
 require(init==1&&phi==1&&forwarded>=1,"missing exact initial-load/phi/replacement structure");
}
int main(int argc,char **argv) {
 try {
  require(argc==9,"arguments: cfg expected literals mode first unsafe kitfree name");
  std::string text((std::istreambuf_iterator<char>(std::cin)),{}),err;
  std::ifstream file(argv[1]);std::string cfg((std::istreambuf_iterator<char>(file)),{});
  Program p;Machine m;require(parseProgram(text,p,err),err);require(parseMachine(cfg,m,err),err);
  const bool expected=std::atoi(argv[2])!=0,literals=std::atoi(argv[3])!=0;
  const int mode=std::atoi(argv[4]);const uint32_t first=static_cast<uint32_t>(std::strtoull(argv[5],nullptr,10));
  const bool unsafe=std::atoi(argv[6])!=0,kitfree=std::atoi(argv[7])!=0;
  auto make=[&](std::string &ssa,bool &scratch) {
   Func f;setup(p,f,literals);transform(f,expected,first);ssa=dumpFunc(f);
   scratch=canSpillToScratch(f);require(!unsafe||!scratch,"scratch safety gate unexpectedly true");
   BackendOptions bo;bo.preSchedule=(mode&1)!=0;bo.bottomUpSchedule=(mode&8)!=0;
   bo.spillToK=(mode&2)!=0&&scratch;
   return lowerToProgram(f,m,bo);
  };
  std::string ssa,again;bool scratch=false,scratch2=false;
  Program out=make(ssa,scratch),repeat=make(again,scratch2);
  require(ssa==again&&scratch==scratch2&&printProgram(out)==printProgram(repeat),"repeat nondeterminism");
  Func lowered;require(buildSSA(out,lowered,err),err);valid(lowered);
  if(kitfree) {
   SimProgram original(p),candidate(out);
   for(uint32_t count:{0xfffffffdu,0xffffffffu,0u,1u,2u,3u,5u,8u})for(int pattern=0;pattern<4;++pattern) {
    Input in;in.args={count,pattern==0?0u:pattern==1?1u:pattern==2?0x80000000u:0xffffffffu,
                                  pattern==0?0u:pattern==1?4095u:pattern==2?4096u:0xffffffffu};
    std::vector<uint32_t> words(kMemWords);
    for(uint32_t i=0;i<kMemWords;++i)words[i]=pattern==0?0u:pattern==1?0xffffffffu:
            pattern==2?(i*2654435761u)^count:(i%4==0?0x80000000u:i%4==1?0x7fffffffu:i%4==2?i:0xffffffffu-i);
    in.segments.push_back({0,words});in.vin[1]={count,13u,17u};
    auto a=original.run(in,20000,false),b=candidate.run(in,20000,false);
    require(a.status!=Status::TIMEOUT&&b.status!=Status::TIMEOUT,"unexpected timeout");
    require(compareRuns(a,b).empty(),compareRuns(a,b));
   }
  }
  std::cerr<<"scratch="<<scratch<<" spill="<<((mode&2)!=0&&scratch)<<"\n";
  std::cout<<printProgram(out);
 }catch(const std::exception &e){std::cerr<<"FAIL "<<e.what()<<"\n";return 1;}
}
'''


def loop(*, initial=None, step="1", offset=0, carrier="load", prefix="", header="",
         after="", between="", entry="", count="v0", tail="", address=None):
    # v2 IV and v3 trip counter begin as the specified raw uninitialized zero.
    init = "" if initial is None else f"mov v2, {initial}\n"
    addr = address or ("v2" if offset == 0 else "v4")
    addrdef = "" if offset == 0 else f"add v4, v2, {offset}\n"
    nxt = f"add v6, v2, {offset + int(step)}" if step.lstrip("-").isdigit() else f"add v6, v2, {step}"
    known = "load v7, v6" if carrier == "load" else "add v7, v5, 17\nstore v6, v7"
    return f"""func rolling(v0,v90,v91)
entry:
{init}{entry}
 jmp head
head:
{header}
 lt v10, v3, {count}
 br v10, body, exit
body:
{addrdef}{prefix}
 load v5, {addr}
 store 100, v5
{between}
 {nxt}
 {known}
{after}
 add v8, v8, v5
 xor v8, v8, v7
 add v2, v2, {step}
 add v3, v3, 1
{tail}
 jmp head
exit:
 ret v8
"""


def fixtures():
    cases = {}

    def add(name, text, expected, *, literals=False, first=0, unsafe=False):
        cases[name] = dict(text=text, expected=expected, literals=literals, first=first, unsafe=unsafe)

    add("load-to-load-raw-zero", loop(), True)
    add("store-to-load-raw-zero", loop(carrier="store"), True)
    add("store-original-first-value", loop(after="store v2, v5"), True)
    add("store-next-from-original-first", loop(carrier="store", between="add v21,v5,0"), True)
    add("latest-store-wins-over-load", loop(after="store v6,v90"), True)
    add("latest-load-after-store", loop(carrier="store", after="load v21,v6\nxor v8,v8,v21"), True)
    add("disjoint-iv-store-after-known", loop(after="add v20,v2,2\nstore v20,v90"), True)
    add("disjoint-negative-offset-after-known", loop(initial="8", after="add v20,v2,-1\nstore v20,v90"), True, literals=True, first=8)
    add("unknown-store-before-known", loop(between="store v91,v90"), True, unsafe=True)
    add("same-address-store-before-known", loop(between="store v2,v90"), True)
    add("unknown-load-after-known", loop(after="load v20,v91\nxor v8,v8,v20"), True, unsafe=True)
    add("step-minus-one-load", loop(initial="8", step="-1"), True, literals=True, first=8)
    add("step-minus-one-store", loop(initial="8", step="-1", carrier="store"), True, literals=True, first=8)
    add("address-positive-offset", loop(offset=3), True, first=3)
    add("address-negative-offset", loop(initial="8", offset=-3), True, literals=True, first=5)
    add("wrap-initial-plus-offset-zero", loop(initial="-1", offset=1), True, literals=True, first=0)
    add("wrap-backedge-minus-one", loop(step="-1", offset=1), True, first=1)
    add("last-valid-then-trap", loop(initial="4095"), True, literals=True, first=4095, unsafe=True)
    add("partial-stores-before-future-trap", loop(initial="4094"), True, literals=True, first=4094, unsafe=True)
    add("partial-stores-before-later-trap", loop(carrier="store", after="load v20,4096\nxor v8,v8,v20"), True, unsafe=True)
    add("scratch-initial-and-next", loop(initial="3072"), True, literals=True, first=3072, unsafe=True)
    add("invalid-initial-4096", loop(initial="4096"), False, literals=True, unsafe=True)
    add("invalid-initial-minus-one", loop(initial="-1"), False, literals=True, unsafe=True)
    add("invalid-offset-initial", loop(offset=4096), False, unsafe=True)
    add("dynamic-initial", loop(initial="v91"), False, unsafe=True)
    add("raw-const-initial-not-literal", loop(initial="0"), False)
    add("literalized-const-initial", loop(initial="0"), True, literals=True)
    add("dynamic-step", loop(step="v90"), False, unsafe=True)
    add("zero-step", loop(step="0"), False)
    add("wrong-distance-two", loop().replace("add v6, v2, 1", "add v6, v2, 2"), False)
    add("non-affine-address", loop(address="v4", prefix="and v4,v2,15"), False)
    add("non-affine-next-address", loop().replace("add v6, v2, 1", "xor v6,v2,1"), False)
    add("unknown-store-after-known", loop(after="store v91,v90"), False, unsafe=True)
    add("constant-may-alias-store-after-known", loop(after="store 1,v90"), False)
    add("opaque-equal-store-after-known", loop(after="xor v20,v6,0\nstore v20,v90"), False, unsafe=True)
    add("first-effect-store", loop(prefix="store 200,v90"), False)
    add("first-effect-other-load", loop(prefix="load v21,7\nxor v8,v8,v21"), False)
    add("header-load", loop(header="load v21,7"), False)
    add("header-store", loop(header="store 200,v90"), False)
    for name, effect in (("vload", "vload v21,1"), ("vstore", "vstore 1,v90"),
                         ("div-variable", "div v21,v90,v91"), ("mod-variable", "mod v21,v90,v91"),
                         ("div-nonzero", "div v21,v90,2"), ("mod-nonzero", "mod v21,v90,-1")):
        add("body-after-"+name, loop(after=effect), False)
        add("body-before-"+name, loop(prefix=effect), False)
    add("header-div", loop(header="div v21,v90,v91"), False)
    add("header-volatile", loop(header="vstore 1,v90"), False)
    add("body-explicit-trap", loop().replace(" jmp head\nexit:", " trap 17\nexit:"), False)
    add("three-block-loop", loop().replace(" add v2,v2,1", " add v2,v2,1").replace(" add v2, v2, 1", " jmp latch\nlatch:\n add v2, v2, 1"), False)
    add("cross-entry-into-body", loop().replace(" jmp head\nhead:", " br v90,head,body\nhead:", 1), False)
    sibling = loop().replace(" jmp head\nhead:", " br v90,head,sibling\nsibling:\n store 200,v91\n ret v91\nhead:", 1)
    add("predecessor-sibling-exit", sibling, True)
    add("sibling-exit-invalid-initial", sibling.replace("entry:\n", "entry:\n mov v2,4096\n"), False, literals=True, unsafe=True)
    multi = loop().replace(" jmp head\nhead:", " br v90,left,right\nleft:\n jmp head\nright:\n jmp head\nhead:", 1)
    add("multiple-outside-predecessors", multi, False)
    add("nonloop-reject-safe-scratch", "func plain(v0,v90,v91)\nentry:\nload v2,0\nstore 1,v2\nret v0\n", False)
    return cases


def inputs():
    for count in COUNTS:
        for pattern in range(4):
            words = [(0 if pattern == 0 else 0xffffffff if pattern == 1 else
                      ((i*2654435761) ^ (count & 0xffffffff)) & 0xffffffff if pattern == 2 else
                      (0x80000000 if i % 4 == 0 else 0x7fffffff if i % 4 == 1 else i if i % 4 == 2 else 0xffffffff-i))
                     for i in range(4096)]
            yield count, pattern, [count & 0xffffffff, (0,1,0x80000000,0xffffffff)[pattern],
                                  (0,4095,4096,0xffffffff)[pattern]], [(0,words)], {1:[count & 0xffffffff,13,17]}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--source-root", type=Path, default=ROOT)
    ap.add_argument("--kit-free", action="store_true")
    ap.add_argument("--evidence-dir", type=Path)
    a = ap.parse_args()
    source = a.source_root.resolve()
    if (source/"src").is_dir():
        source /= "src"
    if not (source/"rolling_load.cpp").is_file():
        ap.error("source root lacks rolling_load.cpp; pass --source-root /path/to/kopt-stream")
    evidence = a.evidence_dir or ROOT/"build"/("rolling-load-kit-free" if a.kit_free else "rolling-load-evidence")
    evidence.mkdir(parents=True, exist_ok=True)
    snapshot = evidence/"src"
    snapshot.mkdir(exist_ok=True)
    manifest = {}
    for path in sorted(source.iterdir()):
        if path.suffix in (".cpp", ".h"):
            data = path.read_bytes()
            (snapshot/path.name).write_bytes(data)
            manifest[path.name] = hashlib.sha256(data).hexdigest()
    if a.kit_free:
        sys.path.insert(0,str(ROOT/"tools"))
        from smoke import BASE_MACHINE
        cfg = evidence/"machine.cfg"
        cfg.write_text("".join(f"{k} = {v}\n" for k,v in BASE_MACHINE.items()))
    else:
        kit = Path(os.environ.get("KIT", ROOT.parent/"official-LLH-26/Compilers/COMP10"))
        sys.path.insert(0,str(kit.resolve()))
        import kirlib as K
        cfg = kit/"machines/machine_slow_memory.cfg"
        machine = K.load_machine(str(cfg))
    cxx = shlex.split(os.environ.get("CXX", "c++"))
    driver = evidence/"driver.cpp"
    driver.write_text(DRIVER)
    binary = evidence/"driver"
    sources = [str(snapshot/name) for name in manifest if name.endswith(".cpp") and name not in ("main.cpp","optimizer.cpp")]
    command = [*cxx,"-std=c++17","-O1","-Wall","-Wextra","-Werror","-pedantic","-I"+str(snapshot),str(driver),*sources,"-o",str(binary)]
    print("snapshot rolling_load.cpp "+manifest["rolling_load.cpp"],flush=True)
    subprocess.run(command,check=True)
    checks = 0
    records = []
    cases = fixtures()
    trials = list(inputs())
    for name, case in cases.items():
        td = evidence/name
        td.mkdir(exist_ok=True)
        (td/"original.kir").write_text(case["text"])
        if not a.kit_free:
            original = K.compile_program(K.parse_program(case["text"]))
        for mode in MODES:
            cmd = [str(binary),str(cfg),str(int(case["expected"])),str(int(case["literals"])),str(mode),str(case["first"]),str(int(case["unsafe"])),str(int(a.kit_free)),name]
            p = subprocess.run(cmd,input=case["text"],text=True,capture_output=True)
            if p.returncode:
                raise AssertionError((name,mode,p.stderr,p.stdout))
            (td/f"mode{mode}.kir").write_text(p.stdout)
            (td/f"mode{mode}.log").write_text(p.stderr)
            if a.kit_free:
                checks += len(trials)
            else:
                program = K.parse_program(p.stdout)
                K.check_machine_features(program,machine)
                candidate = K.compile_program(program)
                for count,pattern,args,segments,vin in trials:
                    x = K.execute(original,args,segments,vin,20000)
                    y = K.execute(candidate,args,segments,vin,20000)
                    assert x.status != "TIMEOUT" and y.status != "TIMEOUT",(name,mode,count,pattern,"timeout")
                    diff = K.first_difference(x,y)
                    assert not diff,(name,mode,count,pattern,diff,p.stdout)
                    checks += 1
            records.append(dict(case=name,mode=mode,promoted=case["expected"],literal_setup=case["literals"],backend=p.stderr.strip()))
        print("PASS "+name,flush=True)
    report = dict(cases=len(cases),accepted=sum(c["expected"] for c in cases.values()),modes=list(MODES),comparisons=checks,
                  oracle="local Sim (not independent)" if a.kit_free else "official kirlib (independent)",
                  source_root=str(source),sha256=manifest,cxx=cxx,records=records)
    (evidence/"evidence.json").write_text(json.dumps(report,indent=2)+"\n")
    print(f"PASS {len(cases)} cases / {report['accepted']} promotions x {len(MODES)} modes; {checks} {report['oracle']} comparisons; exact gates/stores/SSA/determinism/scratch safety",flush=True)
    print("evidence: "+str(evidence.resolve()),flush=True)


if __name__ == "__main__":
    sys.dont_write_bytecode = True
    main()
