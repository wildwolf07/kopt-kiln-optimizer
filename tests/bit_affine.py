#!/usr/bin/env python3
"""Direct bitAffineFunction proof gates and official semantics/timing.

Run: python3 -B tests/bit_affine.py
KIT names the official COMP10 directory; CXX selects the C++17 compiler.
Optional --source supplies a standalone implementation without modifying src.
All drivers/builds live in a temporary directory. No optimizer search, fallback,
or local simulator is used to validate results. Zero/basis/random inputs and
independent affine identities are checked by the official interpreter.
"""
import argparse
import hashlib
import itertools
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
KIT_FREE = "--kit-free" in sys.argv
if not KIT_FREE:
    sys.path.insert(0, str(KIT))
    import kirlib as K

MASK = (1 << 32) - 1
DRIVER = r'''
#include <fstream>
#include <iostream>
#include <iterator>
#include <stdexcept>
#include "backend.h"
#include "passes.h"
namespace kopt { bool bitAffineFunction(const Program &, const Machine &, Program &); }
using namespace kopt;
int main(int argc, char **argv) {
    try {
        if (argc != 2) return 2;
        std::ifstream file(argv[1]);
        const std::string cfg((std::istreambuf_iterator<char>(file)), {});
        const std::string text((std::istreambuf_iterator<char>(std::cin)), {});
        Machine m; Program p, sentinel; std::string err;
        if (!parseMachine(cfg, m, err) || !parseProgram(text, p, err) ||
            !parseProgram("func sentinel()\nentry:\nret 123456789\n", sentinel, err))
            throw std::runtime_error(err);
        const std::string original = printProgram(p), untouched = printProgram(sentinel);
        Program out = sentinel, second = sentinel;
        const bool accepted = bitAffineFunction(p, m, out);
        if (accepted != bitAffineFunction(p, m, second) || printProgram(out) != printProgram(second))
            throw std::runtime_error("nondeterministic repeated direct invocation");
        if (printProgram(p) != original) throw std::runtime_error("input modified");
        if (!accepted) {
            if (printProgram(out) != untouched) throw std::runtime_error("rejection modified output");
            std::cout << "REJECT\n";
            return 0;
        }
        if (out.params != p.params || out.name != p.name) throw std::runtime_error("signature changed");
        for (const Block &b : out.blocks) for (const Instr &x : b.ins)
            if (isMemOp(x.op) || x.op == OP_DIV || x.op == OP_MOD || x.op == OP_TRAP)
                throw std::runtime_error("emission introduced memory/trap instruction");
        Func ssa;
        if (!buildSSA(out, ssa, err)) throw std::runtime_error(err);
        err = verifyFunc(ssa);
        if (!err.empty()) throw std::runtime_error(err);
        std::cout << printProgram(out);
    } catch (const std::exception &e) { std::cerr << e.what() << '\n'; return 1; }
}
'''


def program(body, params="v0,v1", name="proof"):
    return f"func {name}({params})\nentry:\n" + "\n".join(body) + "\n"


def crc(rounds=192, width=32):
    lines = [f"and v2, v0, {(1 << width)-1}"]
    for _ in range(rounds):
        lines += ["and v3, v2, 1", "shr v4, v2, 1",
                  "select v5, v3, 3988292384, 0", "xor v2, v4, v5"]
    return program(lines + ["xor v2, v2, 4294967295", "ret v2"], "v0", "crc_style")


def generated(seed, length):
    rng = random.Random(seed)
    body = ["and v4, v0, 65535", "shr v5, v1, 16"]
    pool = ["v4", "v5"]
    for i in range(length):
        dst = f"v{10+i}"
        op = rng.choice(("xor", "xor", "and", "or", "shl", "shr"))
        a = rng.choice(pool)
        if op == "xor":
            b = rng.choice(pool) if rng.randrange(2) else str(rng.getrandbits(32))
        elif op in ("and", "or"):
            b = str(rng.getrandbits(32))
        else:
            b = str(rng.choice((0, 1, 7, 13, 17, 31, 32, 63)))
        body.append(f"{op} {dst}, {a}, {b}")
        pool.append(dst)
    # Keep both parameter domains in the result even if random masking dies.
    body += [f"xor v9000, {pool[-1]}, v4", "xor v9001, v9000, v5", "ret v9001"]
    return program(body, name=f"linear_{seed}")


def fixtures():
    """None permits a future support-cap increase; accepted output is still checked."""
    cases = [
        ("constant-zero-params", program(["ret 2147483648"], ""), True),
        ("zero-initialized", program(["xor v5,v99,v0", "ret v5"], "v0"), True),
        ("identity-32-columns", program(["ret v0"], "v0"), True),
        ("bias-and-sign", program(["xor v2,v0,2147483649", "ret v2"], "v0"), True),
        ("two-high-domains", program(["and v2,v0,4026531855", "and v3,v1,2147549183",
                                     "xor v4,v2,v3", "xor v5,v4,4294967295", "ret v5"]), True),
        ("four-param-bit127-bias", program([
            "and v8,v0,255", "and v9,v2,255", "shl v9,v9,8", "and v10,v4,255",
            "shl v10,v10,16", "shr v11,v6,24", "shl v11,v11,24",
            "xor v12,v8,v9", "xor v13,v10,v11", "xor v14,v12,v13",
            "xor v15,v14,2147483648", "ret v15"], "v0,v2,v4,v6"), True),
        ("high-param-register-names", program(["shr v5,v999999,31", "shl v6,v0,31",
                                                "xor v7,v5,v6", "ret v7"], "v999999,v0"), True),
        ("wire-group-cross-param-collision", program([
            "and v2,v0,255", "and v3,v1,255", "xor v4,v2,v3", "shl v5,v4,17",
            "shr v6,v0,24", "xor v7,v5,v6", "ret v7"]), True),
        ("wire-reversal", program(["shr v2,v0,31", "and v3,v0,1", "shl v3,v3,31",
                                  "xor v4,v2,v3", "ret v4"], "v0"), True),
        ("shift-count-high-bits-ignored", program(["and v2,v1,4294967264", "or v3,v2,3",
                                                  "shr v4,v0,v3", "ret v4"]), True),
        ("shift-zero-mod32", program(["shl v2,v0,32", "ret v2"], "v0"), True),
        ("shift-sign-to-low", program(["shr v2,v0,31", "ret v2"], "v0"), True),
        ("pow2-multiply-bit31", program(["mul v2,v0,2147483648", "ret v2"], "v0"), True),
        ("pow2-multiply-left", program(["mul v2,8,v0", "ret v2"], "v0"), True),
        ("add-double-linear", program(["add v2,v0,v0", "ret v2"], "v0"), True),
        ("add-disjoint-fields", program(["and v2,v0,255", "and v3,v1,255", "shl v3,v3,8",
                                         "add v4,v2,v3", "ret v4"]), True),
        ("add-top-bit-linear", program(["add v2,v0,2147483648", "ret v2"], "v0"), True),
        ("subtract-top-bit-linear", program(["sub v2,v0,2147483648", "ret v2"], "v0"), True),
        ("subtract-equal", program(["sub v2,v0,v0", "ret v2"], "v0"), True),
        ("and-equal", program(["and v2,v0,v0", "ret v2"], "v0"), True),
        ("and-complement", program(["xor v2,v0,4294967295", "and v3,v0,v2", "ret v3"], "v0"), True),
        ("or-complement", program(["xor v2,v0,4294967295", "or v3,v0,v2", "ret v3"], "v0"), True),
        ("select-signbit", program(["and v2,v0,2147483648", "select v3,v2,2147483649,2147483647",
                                    "ret v3"], "v0"), True),
        ("select-repeated-guard-bits", program(["and v2,v0,1", "shl v3,v2,31", "or v4,v2,v3",
                                               "select v5,v4,4294967295,17", "ret v5"], "v0"), True),
        ("select-complement-guard-bits", program(["and v2,v0,1", "xor v3,v2,1", "shl v3,v3,31",
                                                 "or v4,v2,v3", "select v5,v4,31,17", "ret v5"], "v0"), True),
        ("select-known-nonzero-wide-guard", program(["or v2,v0,1", "select v3,v2,v0,0", "ret v3"], "v0"), True),
        ("select-guard-as-data", program(["and v2,v0,1", "select v3,v2,v2,0", "ret v3"], "v0"), True),
        ("eq-one-bit", program(["and v2,v0,1", "eq v3,v2,0", "ret v3"], "v0"), True),
        ("eq-replicated-bit", program(["and v2,v0,1", "shl v3,v2,17", "or v4,v2,v3",
                                      "eq v5,v4,0", "ret v5"], "v0"), True),
        ("lt-sign-bit", program(["lt v2,v0,0", "ret v2"], "v0"), True),
        ("flattened-linear-diamond", program(["and v2,v0,1", "br v2,left,right", "left:",
                                              "const v3,2147483649", "jmp done", "right:",
                                              "const v3,17", "jmp done", "done:", "ret v3"], "v0"), True),
        ("folded-signed-comparison", program(["lt v2,2147483648,0", "ret v2"], ""), True),
        ("crc-8", crc(8), True),
        ("crc-192", crc(), True),
        ("nonlinear-and", program(["and v2,v0,v1", "ret v2"]), False),
        ("nonlinear-or", program(["or v2,v0,v1", "ret v2"]), False),
        ("nonlinear-variable-shift", program(["shr v2,v0,v1", "ret v2"]), False),
        ("nonlinear-add-carry", program(["add v2,v0,1", "ret v2"], "v0"), False),
        ("nonlinear-sub-borrow", program(["sub v2,0,v0", "ret v2"], "v0"), False),
        ("nonlinear-multiply", program(["mul v2,v0,v1", "ret v2"]), False),
        ("nonlinear-multiply-three", program(["mul v2,v0,3", "ret v2"], "v0"), False),
        ("nonlinear-wide-eq", program(["eq v2,v0,0", "ret v2"], "v0"), False),
        ("nonlinear-positive-lt", program(["lt v2,0,v0", "ret v2"], "v0"), False),
        ("nonlinear-wide-guard", program(["select v2,v0,1,0", "ret v2"], "v0"), False),
        ("nonlinear-select-data", program(["and v2,v0,1", "select v3,v2,v1,0", "ret v3"]), False),
        ("memory-load", program(["load v2,0", "ret v2"], "v0"), False),
        ("memory-dead-load", program(["load v2,0", "ret 0"], "v0"), False),
        ("memory-store", program(["store 3072,v0", "ret v0"], "v0"), False),
        ("volatile-load", program(["vload v2,1", "ret v2"], "v0"), False),
        ("volatile-store", program(["vstore 1,v0", "ret v0"], "v0"), False),
        ("division-zero", program(["div v2,v0,0", "ret 7"], "v0"), False),
        ("division-safe", program(["div v2,v0,1", "ret v2"], "v0"), False),
        ("remainder-safe", program(["mod v2,v0,1", "ret v2"], "v0"), False),
        ("explicit-trap", program(["trap v0"], "v0"), False),
        ("remaining-loop", program(["and v2,v0,7", "jmp loop", "loop:", "sub v2,v2,1",
                                     "and v2,v2,7", "br v2,loop,done", "done:", "ret v2"], "v0"), False),
        ("infinite-loop", program(["jmp loop", "loop:", "jmp loop"], "v0"), False),
        ("five-params", program(["ret v0"], "v0,v1,v2,v3,v4"), False),
        ("support-128", program(["xor v4,v0,v1", "xor v5,v2,v3", "xor v6,v4,v5", "ret v6"],
                                "v0,v1,v2,v3"), False),
        ("support-33-or-future-cap64", program(["and v2,v1,1", "xor v3,v0,v2", "ret v3"]), None),
        ("support-64-or-future-cap64", program(["xor v2,v0,v1", "ret v2"]), None),
    ]
    # Exactly 1000 original instructions should be admissible; 1001 must reject.
    for count in (999, 1000):
        body = [f"xor v2,{('v0' if i == 0 else 'v2')},{i+1}" for i in range(count)] + ["ret v2"]
        cases.append((f"source-instructions-{count+1}", program(body, "v0"), count == 999))
    for seed in range(12):
        cases.append((f"generated-linear-{seed}", generated(98170+seed, 80+seed*19), True))
    return cases


def inputs(nparams, seed):
    rng = random.Random(seed)
    out = [[0]*nparams]
    out += [[(1 << bit) if p == active else 0 for p in range(nparams)]
            for active in range(nparams) for bit in range(32)]
    edges = (0, 1, 2, 31, 32, 63, 0x7fffffff, 0x80000000, 0xfffffffe, MASK)
    out += [[x]*nparams for x in edges]
    # Independent high bits, not just correlated edge tuples.
    if nparams > 1:
        out += [[a if p % 2 == 0 else b for p in range(nparams)]
                for a,b in itertools.product(edges, repeat=2)]
    out += [[rng.getrandbits(32) for _ in range(nparams)] for _ in range(80)]
    # These pairs also exercise linear superposition with the affine bias.
    for _ in range(16):
        a = [rng.getrandbits(32) for _ in range(nparams)]
        b = [rng.getrandbits(32) for _ in range(nparams)]
        out += [a,b,[x ^ y for x,y in zip(a,b)]]
    return out


def run(cp, args, trace=False):
    r = K.execute(cp, args, [(0,[17,MASK]),(3072,[29])], {0:[3,0,7]}, 20000, want_trace=trace)
    assert r.status == "RET", (args, r.status, r.value)
    return r


def invoke(binary, text, cfg):
    p = subprocess.run([str(binary),str(cfg)], input=text, text=True, capture_output=True, timeout=30)
    assert p.returncode == 0, (p.returncode,p.stderr)
    return None if p.stdout == "REJECT\n" else p.stdout


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--kit-free", action="store_true", help="run proof and structural gates without the external kit")
    ap.add_argument("--source", type=Path, default=ROOT / "src/bit_affine.cpp")
    ap.add_argument("--artifacts", type=Path, help="optional persistent output/timing directory")
    args = ap.parse_args()
    if not args.source.is_file():
        ap.error(f"implementation not available: {args.source}; provide --source PATH")
    cases = fixtures()
    cfgs = [KIT / "machines" / f"machine_{m}.cfg" for m in
            ("default", "few_registers", "no_fused", "slow_memory", "wide_fast")]
    if args.artifacts:
        args.artifacts.mkdir(parents=True, exist_ok=True)
    comparisons = accepted = rejected = 0
    timings = []
    with tempfile.TemporaryDirectory(prefix="kopt-bit-affine-") as temp:
        td = Path(temp); driver = td / "driver.cpp"; binary = td / "driver"
        if args.kit_free:
            sys.path.insert(0, str(ROOT / "tools"))
            from smoke import BASE_MACHINE
            cfg = td / "machine.cfg"
            cfg.write_text("".join("%s = %d\n" % kv for kv in BASE_MACHINE.items()))
            cfgs = [cfg]
        driver.write_text(DRIVER)
        # Compile a private snapshot so concurrent production edits cannot mix
        # implementation versions during one build.
        implementation = td / "bit_affine.cpp"
        implementation.write_bytes(args.source.read_bytes())
        digest = hashlib.sha256(implementation.read_bytes()).hexdigest()
        sources = sorted(str(p) for p in (ROOT / "src").glob("*.cpp")
                         if p.name not in ("main.cpp", "optimizer.cpp", "bit_affine.cpp"))
        subprocess.run([*shlex.split(os.environ.get("CXX", "c++")), "-std=c++17", "-O1",
                        "-Wall", "-Wextra", "-Werror", "-pedantic", "-I"+str(ROOT / "src"),
                        str(driver),str(implementation),*sources,"-o",str(binary)], check=True)
        print("implementation sha256",digest,flush=True)
        for index,(name,text,expected) in enumerate(cases):
            output = invoke(binary,text,cfgs[0])
            if expected is not None:
                assert (output is not None) == expected, (name,"unexpected acceptance",output)
            if output is None:
                rejected += 1
                print("PASS rejected",name,flush=True)
                continue
            accepted += 1
            if args.kit_free:
                print("PASS accepted", name, "proof/structural gates", flush=True)
                continue
            source = K.parse_program(text)
            transformed = K.parse_program(output)
            original, candidate = K.compile_program(source), K.compile_program(transformed)
            vectors = inputs(len(source.params),334170+index)
            reference_values = []
            for vector in vectors:
                a,b = run(original,vector),run(candidate,vector)
                difference = K.first_difference(a,b)
                assert not difference,(name,vector,difference,output)
                reference_values.append(a.value)
                comparisons += 1
            bias = reference_values[0]
            # Independently reconstruct the source's matrix from zero/basis
            # executions. This checks emitter support grouping and affine bias.
            columns = [r ^ bias for r in reference_values[1:1+32*len(source.params)]]
            for vector,value in zip(vectors,reference_values):
                predicted = bias
                for p,v in enumerate(vector):
                    for bit in range(32):
                        if v & (1 << bit): predicted ^= columns[32*p+bit]
                assert predicted == value,(name,"source not affine",vector,predicted,value)
            for cfg in cfgs:
                alternate = invoke(binary,text,cfg)
                assert alternate is not None,(name,cfg.name,"machine-dependent rejection")
                alt_program = K.parse_program(alternate)
                mc = K.load_machine(str(cfg))
                K.check_machine_features(alt_program,mc)
                cp = K.compile_program(alt_program)
                before = after = 0
                for vector in vectors[:min(len(vectors),33)]:
                    a,b = run(original,vector,True),run(cp,vector,True)
                    difference = K.first_difference(a,b)
                    assert not difference,(name,cfg.name,vector,difference)
                    comparisons += 1
                    before += K.time_trace(original,a.trace,mc)
                    after += K.time_trace(cp,b.trace,mc)
                row = dict(case=name,machine=cfg.stem,original=before,affine=after,
                           original_instructions=len(source.instrs),affine_instructions=len(alt_program.instrs))
                timings.append(row)
                if name == "crc-192": print("CYCLES",json.dumps(row,sort_keys=True),flush=True)
            if args.artifacts:
                (args.artifacts / f"{name}-original.kir").write_text(text)
                (args.artifacts / f"{name}-affine.kir").write_text(output)
            print("PASS accepted",name,"official inputs",len(vectors),flush=True)
        crc_timings = [r for r in timings if r["case"] == "crc-192"]
        if not args.kit_free:
            assert crc_timings and all(r["affine"] < r["original"] for r in crc_timings), crc_timings
        summary = dict(source=str(args.source.resolve()),sha256=digest,accepted=accepted,rejected=rejected,
                       comparisons=comparisons,timings=timings)
        if args.artifacts:
            (args.artifacts / "evidence.json").write_text(json.dumps(summary,indent=2)+"\n")
    if args.kit_free:
        print(f"PASS {accepted} accepted / {rejected} rejected proof/structural gates (kit-free)", flush=True)
    else:
        print(f"PASS {comparisons} official comparisons; {accepted} accepted / {rejected} rejected; "
              "zero/basis/edges/random/superposition, output preservation, SSA, "
              "determinism and five-machine timing checked",flush=True)


if __name__ == "__main__":
    main()
