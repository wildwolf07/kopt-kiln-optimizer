#!/usr/bin/env python3
"""Hash every public output for exact cross-compiler comparisons."""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bin', type=Path, default=ROOT/'build/kopt-bin')
    parser.add_argument('--label', default='build')
    parser.add_argument('--output', type=Path, default=ROOT/'build/output-manifest.json')
    parser.add_argument('--jobs', type=int, default=1)
    parser.add_argument('--timeout', type=float, default=180)
    args = parser.parse_args()
    assert args.jobs >= 1
    kit = Path(os.environ.get('KIT',ROOT.parent/'official-LLH-26/Compilers/COMP10')).resolve()
    binary = args.bin.resolve()
    folder = args.output.resolve().parent/(args.output.stem+'-outputs')
    folder.mkdir(parents=True,exist_ok=True)
    jobs = [(p,m) for p in sorted((kit/'bench').glob('*.kir'))
            for m in ('default','few_registers','no_fused','slow_memory','wide_fast')]
    assert len(jobs)==500, 'expected 100 public programs and five machines'
    env = {k:v for k,v in os.environ.items() if not k.startswith('KOPT_')}
    env['KOPT_STRICT']='1'
    def run(job):
        src,machine=job
        out=folder/(src.stem+'-'+machine+'.kir')
        command=[str(binary),str(src),'--machine',str(kit/'machines'/('machine_'+machine+'.cfg')),'-o',str(out)]
        profile=src.with_suffix('.prof')
        if profile.exists():command += ['--profile',str(profile)]
        process=subprocess.run(command,env=env,capture_output=True,text=True,timeout=args.timeout)
        assert process.returncode==0,(src.stem,machine,process.stderr[-2000:])
        assert 'optimizer failed' not in process.stderr, 'wrapper fallback masked failure'
        return src.stem+'|'+machine,hashlib.sha256(out.read_bytes()).hexdigest()
    rows={}
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        for future in as_completed([pool.submit(run,j) for j in jobs]):
            key,value=future.result();rows[key]=value
            if len(rows)%100==0:print(args.label,len(rows),flush=True)
    result=dict(label=args.label,binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),
                pairs=len(rows),outputs=dict(sorted(rows.items())))
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS',args.label,'500 outputs hashed',flush=True)


if __name__=='__main__':main()
