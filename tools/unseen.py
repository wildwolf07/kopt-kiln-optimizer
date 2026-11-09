#!/usr/bin/env python3
"""unseen.py - kopt on 12 random machine files (extreme widths, latencies,
register counts, caches, with or without fused ops) x 100 practice programs.
Reports outputs slower than the input, wrapper fallbacks and the slowest run."""
import os, sys, random, subprocess, glob, time, tempfile, multiprocessing as mp
KIT=os.path.abspath('../official-LLH-26/Compilers/COMP10'); sys.path.insert(0,KIT)
import kirlib as K
def rm(seed):
    r=random.Random(seed)
    return dict(issue_width=r.choice([1,1,2,3,4,6]),mem_ports=r.choice([1,1,2,3]),registers=r.choice([4,5,6,8,12,16,32]),
      reg_spill_penalty=r.choice([0,1,5,10,20]),taken_branch_penalty=r.choice([0,1,2,5,8]),icache_size=r.choice([8,16,24,32,64,128,256]),
      icache_penalty=r.choice([0,1,2,4,8]),lat_alu=r.choice([1,1,2]),lat_mul=r.choice([1,2,3,6,10]),lat_div=r.choice([2,12,30]),
      lat_load=r.choice([1,2,4,8,20]),lat_mac=r.choice([1,3,5,12]),lat_addsh=r.choice([1,2,4]),fused_mac=r.choice([0,1]),fused_addsh=r.choice([0,1]))
def job(a):
    seed,src=a; mc=rm(seed); name=os.path.basename(src)[:-4]
    with tempfile.TemporaryDirectory() as td:
        cfg=os.path.join(td,'m.cfg'); open(cfg,'w').write(''.join('%s = %d\n'%kv for kv in mc.items()))
        out=os.path.join(td,'o.kir'); t=time.time()
        p=subprocess.run(['./kopt',src,'--machine',cfg,'-o',out],capture_output=True,text=True); dt=time.time()-t
        o=K.load_program(src); n=K.load_program(out); K.check_machine_features(n,mc)
        inp=K.load_input(src[:-4]+'.in',len(o.params))
        def cyc(pr):
            cp=K.compile_program(pr); r=K.execute(cp,inp.args,inp.segments,inp.vin,5000000,True); return K.time_trace(cp,r.trace,mc)
        return (seed,name,cyc(o),cyc(n),dt,'fallback' in p.stderr)
if __name__=='__main__':
  srcs=sorted(glob.glob(KIT+'/bench/*.kir'))
  jobs=[(s,f) for s in range(12) for f in srcs]
  with mp.Pool(10) as pool: res=pool.map(job,jobs)
  worse=[r for r in res if r[3]>r[2]]; slow=max(r[4] for r in res); fb=[r for r in res if r[5]]
  print("cases",len(res),"worse_than_input",len(worse),"fallbacks",len(fb),"max_time %.2f"%slow)
  for r in sorted(worse,key=lambda r:r[2]-r[3])[:12]: print("WORSE m%d %s %d -> %d"%(r[0],r[1],r[2],r[3]))
  for r in sorted(res,key=lambda r:-r[4])[:6]: print("SLOW m%d %s %.2fs"%(r[0],r[1],r[4]))
  print("total in %d out %d"%(sum(r[2] for r in res),sum(r[3] for r in res)))
