#!/usr/bin/env python3
"""Direct windowPolish gates; no optimizer build or selection fallback.

Default: independent official kirlib checks EVERY callback candidate and result.
--kit-free: local Sim smoke oracle checks those same programs inside the driver.
CXX may include compiler/sanitizer flags. All generated files stay in build/.
"""
import argparse
from collections import Counter, defaultdict, deque
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
sys.dont_write_bytecode = True
EDGES = (0, 1, 2, 3, 31, 32, 4095, 4096, 0x7fffffff, 0x80000000, 0xfffffffe, 0xffffffff)
DRIVER = r'''
#include "passes.h"
#include <iostream>
#include <iterator>
#include <stdexcept>
using namespace kopt;
void need(bool ok, const std::string &why) { if (!ok) throw std::runtime_error(why); }
std::string order(const Program &p) {
    std::string s;
    for (const Instr &x : p.blocks[0].ins) {
        if (!s.empty()) s += ',';
        s += std::to_string(hasDest(x.op) ? x.dst : 1000000u + x.op);
    }
    return s;
}
int main(int argc, char **argv) { try {
    need(argc == 5, "budget mode target kitfree");
    const size_t budget = std::stoull(argv[1]);
    const std::string mode = argv[2], target = argv[3];
    const bool local = std::string(argv[4]) == "1";
    const std::string text((std::istreambuf_iterator<char>(std::cin)), {});
    Program p; std::string err;
    need(parseProgram(text, p, err), err);
    const std::string original = printProgram(p);
    const uint32_t edges[] = {0,1,2,3,31,32,4095,4096,0x7fffffffu,0x80000000u,0xfffffffeu,0xffffffffu};
    std::vector<Input> inputs;
    std::vector<RunResult> refs;
    SimProgram base(p);
    for (size_t i = 0; i < 12; ++i) {
        Input in;
        for (size_t j = 0; j < p.params.size(); ++j) in.args.push_back(edges[(i + j * 3) % 12]);
        std::vector<uint32_t> words(64);
        for (uint32_t j = 0; j < 64; ++j) words[j] = (j * 2654435761u) ^ edges[i];
        in.segments = {{0,words},{3070,{1,0xffffffffu,7,9}},{4095,{edges[i]}}};
        if (i % 2 == 0) for (uint32_t port : {0u,1u,0xffffffffu}) in.vin[port] = {7,9,0x80000000u};
        refs.push_back(base.run(in, 2000, false));
        need(refs.back().status != Status::TIMEOUT, "fixture timeout");
        inputs.push_back(std::move(in));
    }
    Machine machine;
    size_t calls = 0;
    auto cost = [&](const Program &q) -> uint64_t {
        ++calls; need(calls <= budget, "callback budget exceeded");
        SimProgram sim(q);
        uint64_t cycles = 0;
        if (local || mode == "cycles") for (size_t i = 0; i < inputs.size(); ++i) {
            const auto got = sim.run(inputs[i], 2000, mode == "cycles");
            need(compareRuns(refs[i], got).empty(), compareRuns(refs[i], got));
            need(refs[i].mem == got.mem, "scratch memory changed");
            if (mode == "cycles") cycles += sim.cycles(got.trace, machine);
        }
        uint64_t c = 100;
        if (mode == "target") c = order(q) == target ? 10 : 100;
        else if (mode == "descend") c = 1000000 - calls;
        else if (mode == "worse") c += calls;
        else if (mode == "last") c = calls == 1 ? 100 : calls == budget ? 10 : 200;
        else if (mode == "max") c = UINT64_MAX;
        else if (mode == "zero") c = 0;
        else if (mode == "cycles") c = cycles;
        std::cout << "@@cost " << c << '\n' << printProgram(q);
        return c;
    };
    const Program result = windowPolish(p, cost, budget);
    need(printProgram(p) == original, "input mutated");
    if (local) {
        SimProgram sim(result);
        for (size_t i = 0; i < inputs.size(); ++i) {
            const auto got = sim.run(inputs[i], 2000, false);
            need(compareRuns(refs[i], got).empty() && refs[i].mem == got.mem, "result differs");
        }
    }
    std::cout << "@@result " << calls << '\n' << printProgram(result);
} catch (const std::exception &e) { std::cerr << e.what() << '\n'; return 1; } }
'''


def program(lines, params='v0,v1,v2'):
    return f'func window_fixture({params})\nentry:\n' + '\n'.join('  ' + s for s in lines) + '\n'


def blocks(text):
    """Textual identities retain raw operands and all opcode fields."""
    lines = [s.strip() for s in text.splitlines() if s.strip()]
    out = []
    for line in lines[1:]:
        if line.endswith(':'):
            out.append((line, []))
        else:
            out[-1][1].append(re.sub(r'\s*,\s*', ',', line))
    return re.sub(r'\s*,\s*', ',', lines[0]), out


TERMS = {'trap', 'jmp', 'br', 'ret'}
EFFECTS = {'load', 'store', 'vload', 'vstore', 'div', 'mod', 'trap'}


def rw(line):
    op, args = line.split(' ', 1)
    args = args.split(',')
    writes = set()
    if op not in TERMS | {'store', 'vstore'}:
        writes.add(args.pop(0))
    return op, {a for a in args if re.fullmatch(r'v\d+', a)}, writes


def audit(original, candidate):
    """Independently enforce every original dependency/effect partial order."""
    h, a = blocks(original)
    hh, b = blocks(candidate)
    assert h == hh and len(a) == len(b), 'metadata/layout changed'
    for (label, before), (other, after) in zip(a, b):
        assert label == other and Counter(before) == Counter(after), 'instruction changed/moved across block'
        assert before[-1] == after[-1] and all(s.split()[0] not in TERMS for s in after[:-1]), 'terminator moved'
        occurrences = defaultdict(deque)
        for i, line in enumerate(before):
            occurrences[line].append(i)
        positions = {}
        for j, line in enumerate(after):
            positions[occurrences[line].popleft()] = j
        resources = [rw(line) for line in before]
        for i, (op, reads, writes) in enumerate(resources):
            for j in range(i + 1, len(resources)):
                other_op, other_reads, other_writes = resources[j]
                ordered = (writes & (other_reads | other_writes) or reads & other_writes or
                           op in TERMS or other_op in TERMS or op in EFFECTS and other_op in EFFECTS)
                assert not ordered or positions[i] < positions[j], ('crossed dependency/effect', before[i], before[j])


def one_move(before, after):
    h, a = blocks(before)
    hh, b = blocks(after)
    if h != hh or len(a) != len(b):
        return False
    changed = [i for i in range(len(a)) if a[i] != b[i]]
    if not changed:  # Identical instructions can produce an identical candidate.
        return True
    if len(changed) != 1:
        return False
    k = changed[0]
    left, right = a[k][1], b[k][1]
    for i in range(len(left)):
        for delta in (-3, -2, -1, 1, 2, 3):
            j = i + delta
            if 0 <= j < len(left):
                q = left[:]
                q.insert(j, q.pop(i))
                if q == right:
                    return True
    return False


def trials(nparams):
    for i, edge in enumerate(EDGES):
        args = [EDGES[(i + j * 3) % len(EDGES)] for j in range(nparams)]
        words = [((j * 2654435761) & 0xffffffff) ^ edge for j in range(64)]
        segments = [(0, words), (3070, [1, 0xffffffff, 7, 9]), (4095, [edge])]
        vin = {p: [7, 9, 0x80000000] for p in (0, 1, 0xffffffff)} if i % 2 == 0 else {}
        yield args, segments, vin


def fixtures():
    out = []
    def add(name, lines, **kw):
        out.append(dict(name=name, text=program(lines), **kw))
    independent = ['const v10,10', 'const v11,11', 'const v12,12', 'const v13,13', 'ret v10']
    for budget in (0, 1, 2, 3, 7, 13, 64, 2**64 - 1):
        add(f'budget-{budget}', independent, budget=budget)
    for mode in ('worse', 'max', 'zero', 'descend', 'last'):
        add(mode, independent, mode=mode, budget=7 if mode == 'last' else 2**64 - 1)
    # The baseline and EVERY adjacent swap cost 100; only the requested 2/3
    # rotation costs 10. All four directions/distances must be reachable.
    for target in ('12,10,11,13', '13,10,11,12', '11,12,10,13', '11,12,13,10'):
        add('jump-' + target, independent, mode='target', target=target + ',1000024', improve=True)
    hazards = [
        ('RAW', 'add v10,v0,1', 'mul v11,v10,7'),
        ('WAR', 'add v10,v11,1', 'mul v11,v0,7'),
        ('WAW', 'add v10,v0,1', 'mul v10,v1,7'),
        ('self-RAW', 'add v0,v0,1', 'mul v11,v0,7'),
        ('self-WAR', 'mul v11,v0,7', 'add v0,v0,1'),
        ('self-WAW', 'add v0,v0,1', 'xor v0,v0,v1'),
        ('zero-register', 'mov v10,v99', 'const v99,31'),
        ('select-third', 'select v10,v0,v1,v99', 'const v99,31'),
        ('mac-third', 'mac v10,v0,v1,v99', 'const v99,31'),
        ('addsh', 'addsh v10,v0,v99,31', 'const v99,31'),
        ('load-self', 'load v0,v0', 'add v11,v0,1'),
        ('store-address', 'store v0,v1', 'add v0,v0,1'),
        ('store-value', 'store v0,v1', 'add v1,v1,1'),
        ('vstore-port', 'vstore v0,v1', 'add v0,v0,1'),
        ('vstore-value', 'vstore v0,v1', 'add v1,v1,1'),
        ('divisor', 'div v10,v1,v0', 'add v0,v0,1'),
        ('mod-divisor', 'mod v10,v1,v0', 'add v0,v0,1'),
    ]
    for name, first, second in hazards:
        for gap in range(3):
            add(f'{name}-gap{gap}', [first, *[f'const v{50+i},{70+i}' for i in range(gap)], second,
                                   'store 0,v10', 'store 1,v11', 'store 2,v0', 'ret v10'])
    effects = ['load v10,v0', 'store v0,v1', 'vload v10,v0', 'vstore v0,v1',
               'div v10,v1,v0', 'mod v10,v1,v0']
    for i, first in enumerate(effects):
        for j, second in enumerate(effects):
            for gap in range(3):
                add(f'effects-{i}-{j}-gap{gap}', [first, *[f'const v{50+k},{k}' for k in range(gap)],
                                               second.replace('v10', 'v11'), 'ret v10'])
        # Positive proof: a single effect may move across three independent ops.
        for side in (0, 1):
            pure = independent[:3]
            # Avoid a WAW with v10, the effect's destination.
            pure = [s.replace('v10', 'v20') for s in pure]
            body = [first, *pure] if side == 0 else [*pure, first]
            desired = [*pure, first] if side == 0 else [first, *pure]
            add(f'legal-effect-{i}-{side}', [*body, 'ret v10'], required=program([*desired, 'ret v10']))
    totals = ['const v20,17', 'mov v20,v0', 'add v20,v0,v1', 'sub v20,v0,v1',
              'mul v20,v0,v1', 'and v20,v0,v1', 'or v20,v0,v1', 'xor v20,v0,v1',
              'shl v20,v0,v1', 'shr v20,v0,v1', 'lt v20,v0,v1', 'eq v20,v0,v1',
              'select v20,v0,v1,v2', 'mac v20,v0,v1,v2', 'addsh v20,v0,v1,31']
    for i, total in enumerate(totals):
        add(f'total-{i}', [total, 'store 0,v2', 'ret v20'],
            required=program(['store 0,v2', total, 'ret v20']))
    for term in ('ret v10', 'trap v10', 'trap 0'):
        add('terminal-' + term.replace(' ', '-'), [*independent[:4], 'store 0,v0', 'vstore 0,v1', term])
    add('divzero', ['store 0,17', 'const v20,5', 'vstore 0,11', 'div v10,v1,0',
                    'const v21,6', 'store 1,19', 'ret v10'])
    add('modzero', ['vload v12,0', 'const v20,5', 'mod v10,v1,0', 'vstore 0,v12', 'ret v10'])
    add('bad-address', ['vstore 0,11', 'const v20,5', 'load v10,4096', 'store 0,17', 'ret v10'])
    add('last-valid-address', ['load v10,4095', 'const v20,5', 'store 4095,v10', 'ret v10'])
    add('signed-div-overflow', ['div v10,2147483648,-1', 'const v20,5',
                                'mod v11,2147483648,-1', 'add v12,v10,v11', 'ret v12'])
    add('exact-cycles', ['const v20,1', 'const v21,2', 'const v22,3', 'mul v10,v0,v1',
                         'add v11,v10,v2', 'ret v11'], mode='cycles', improve=True)
    add('no-legal-move', ['add v0,v0,1', 'add v0,v0,2', 'ret v0'], calls=1)
    out.append(dict(name='no-registers', text=program(['ret 17'], params=''), calls=1))
    out.append(dict(name='no-params-zero-regs', text=program(
        ['mov v0,v999999', 'const v999999,31', 'add v10,v0,v999998', 'ret v10'], params='')))
    out.append(dict(name='branches-loop', text='''func window_fixture(v0,v1,v2)
entry:
  and v90,v0,3
  const v80,0
  const v81,1
  jmp head
head:
  lt v91,v80,v90
  const v83,5
  br v91,body,done
body:
  load v10,v80
  add v11,v10,v1
  store v80,v11
  vload v12,v80
  add v80,v80,1
  jmp head
done:
  vstore 0,v80
  ret v80
unreachable:
  const v10,13
  const v11,14
  trap v10
''', mode='descend'))
    out.append(dict(name='guarded-traps', text='''func window_fixture(v0,v1,v2)
entry:
  eq v10,v0,0
  const v20,7
  br v10,zero,nonzero
zero:
  store 0,v1
  const v21,8
  trap v2
nonzero:
  div v11,v1,v0
  const v22,9
  vstore 0,v11
  ret v11
'''))
    for size in (400, 401, 100001):
        body = [*[f'const v{i+10},{i}' for i in range(size-1)], 'ret v10']
        if size > 401:
            body = ['ret v0', 'unreachable:', *[f'const v{i+10},{i}' for i in range(size-2)], 'ret v10']
        add(f'size-{size}', body,
            budget=2, calls=2 if size == 400 else 0)
    return out


def generated(count, seed):
    rng = random.Random(seed)
    for i in range(count):
        lines = []
        for j in range(rng.randrange(8, 25)):
            dst = f'v{rng.randrange(9)}'
            def src():
                return f'v{rng.randrange(12)}' if rng.randrange(3) else str(rng.choice(EDGES))
            a, b, c = src(), src(), src()
            op = rng.choice(('add', 'sub', 'mul', 'and', 'or', 'xor', 'shl', 'shr', 'lt', 'eq',
                             'mov', 'const', 'select', 'mac', 'addsh', 'load', 'store', 'vload',
                             'vstore', 'div', 'mod'))
            if op == 'const': line = f'{op} {dst},{rng.choice(EDGES)}'
            elif op in ('mov', 'load', 'vload'): line = f'{op} {dst},{a}'
            elif op in ('store', 'vstore'): line = f'{op} {a},{b}'
            elif op in ('select', 'mac'): line = f'{op} {dst},{a},{b},{c}'
            elif op == 'addsh': line = f'{op} {dst},{a},{b},{rng.randrange(32)}'
            else: line = f'{op} {dst},{a},{b}'
            lines.append(line)
        lines.append(f'{"trap" if i % 7 == 0 else "ret"} v{rng.randrange(12)}')
        # Descending costs force three accepted moves; flat costs enumerate a
        # whole neighborhood including candidates which will never be returned.
        yield dict(name=f'fuzz-{seed}-{i}', text=program(lines), mode='descend' if i % 2 else 'flat', budget=128)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--kit-free', action='store_true')
    ap.add_argument('--fuzz', type=int, default=100)
    ap.add_argument('--seed', type=int, default=240006913)
    ap.add_argument('--evidence-dir', type=Path)
    a = ap.parse_args()
    evidence = (a.evidence_dir or ROOT / 'build/window-polish-direct').resolve()
    assert evidence.is_relative_to(ROOT), 'artifacts must stay inside isolated checkout'
    evidence.mkdir(parents=True, exist_ok=True)
    driver = evidence / 'driver'
    (evidence / 'driver.cpp').write_text(DRIVER)
    command = [*shlex.split(os.environ.get('CXX', 'c++')), '-std=c++17', '-O1', '-Wall', '-Wextra',
               '-Werror', '-pedantic', '-I' + str(ROOT / 'src'), str(evidence / 'driver.cpp'),
               *[str(ROOT / 'src' / p) for p in ('lru_polish.cpp', 'kir.cpp', 'sim.cpp')], '-o', str(driver)]
    subprocess.run(command, check=True)
    K = None
    if not a.kit_free:
        kit = Path(os.environ.get('KIT', ROOT.parent / 'official-LLH-26/Compilers/COMP10')).resolve()
        sys.path.insert(0, str(kit))
        import kirlib as K
    comparisons = candidates = improved_cases = 0
    records = []
    for case in [*fixtures(), *generated(a.fuzz, a.seed)]:
        name, text = case['name'], case['text']
        budget, mode = case.get('budget', 512), case.get('mode', 'flat')
        args = [str(driver), str(budget), mode, case.get('target', '-'), str(int(a.kit_free))]
        result = subprocess.run(args, input=text, text=True, capture_output=True, timeout=30)
        assert result.returncode == 0, (name, result.stderr)
        again = subprocess.run(args, input=text, text=True, capture_output=True, timeout=30)
        assert again.returncode == 0 and result.stdout == again.stdout, (name, 'nondeterministic')
        fields = re.split(r'(?m)^@@(cost|result) ([0-9]+)\n', result.stdout)
        assert fields[0] == '' and len(fields) % 3 == 1, (name, 'driver protocol')
        entries = [(fields[i], int(fields[i+1]), fields[i+2]) for i in range(1, len(fields), 3)]
        assert entries[-1][0] == 'result' and all(k == 'cost' for k, _, _ in entries[:-1])
        calls = entries[-1][1]
        assert calls == len(entries)-1 and calls <= budget, (name, calls, budget)
        if calls == 0:
            assert blocks(entries[-1][2]) == blocks(text), (name, 'skipped search changed input')
        if 'calls' in case: assert calls == case['calls'], (name, calls)
        if mode == 'descend': assert calls == 4, (name, 'three-round cap', calls)
        if mode == 'zero': assert calls == 1, (name, 'zero cost should stop')
        if name.startswith('budget-'):
            assert calls == min(budget, 13), (name, 'finite neighborhood cap', calls)
        # Size guards can return huge inputs: avoid quadratic partial-order QA
        # when there were no scheduling candidates at all.
        before = entries[0][2] if calls else entries[-1][2]
        best, best_cost, accepts = before, None, 0
        for index, (kind, score, q) in enumerate(entries):
            if not name.startswith('size-'):
                audit(before, q)
            if kind == 'cost':
                if index:
                    assert one_move(best, q), (name, 'candidate exceeded window or changed multiple blocks')
                if best_cost is None or score < best_cost:
                    accepts += int(best_cost is not None)
                    best, best_cost = q, score
            else:
                assert q == best, (name, 'result is not strictly best evaluated candidate')
        assert accepts <= 3, (name, 'round cap', accepts)
        if case.get('improve'): assert accepts, (name, 'required improvement missing')
        if mode == 'last': assert calls == budget and accepts == 1, (name, 'last callback improvement lost')
        if 'required' in case:
            assert blocks(case['required']) in [blocks(q) for _, _, q in entries[:-1]], (name, 'legal crossing absent')
        if K is not None:
            parsed = K.parse_program(text)
            cp = K.compile_program(parsed)
            inputs = list(trials(len(parsed.params)))
            refs = [K.execute(cp, *inp, 2000) for inp in inputs]
            assert all(ref.status != 'TIMEOUT' for ref in refs), (name, 'fixture timeout')
            for _, _, q in entries:
                candidate = K.compile_program(K.parse_program(q))
                for inp, ref in zip(inputs, refs):
                    got = K.execute(candidate, *inp, 2000)
                    diff = K.first_difference(ref, got)
                    assert not diff and ref.mem == got.mem, (name, diff or 'scratch changed', inp[0], q)
                    comparisons += 1
        else:
            comparisons += len(entries) * 12
        candidates += calls
        improved_cases += bool(accepts)
        records.append(dict(name=name, callbacks=calls, accepts=accepts))
        if len(records) % 50 == 0:
            print(f'checked {len(records)} fixtures / {candidates} callback candidates', flush=True)
    sources = [ROOT / p for p in ('src/lru_polish.cpp', 'src/passes.h', 'src/optimizer.cpp', 'tests/window_polish.py')]
    report = dict(fixtures=len(records), callbacks=candidates, comparisons=comparisons,
                  improved_cases=improved_cases, oracle='local Sim smoke' if a.kit_free else 'independent official kirlib',
                  seed=a.seed, compiler=command, records=records,
                  sha256={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources})
    filename = 'local.json' if a.kit_free else 'official.json'
    (evidence / filename).write_text(json.dumps(report, indent=2) + '\n')
    print(f'PASS {len(records)} fixtures; {candidates} callbacks; {comparisons} {report["oracle"]} comparisons; '
          f'{improved_cases} improved cases', flush=True)


if __name__ == '__main__':
    main()
