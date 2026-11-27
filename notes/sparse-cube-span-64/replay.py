"""Build both exact verifiers, replay the complete span-64 census and check its coverage."""
import csv
import io
import math
import subprocess
import sys
import tempfile
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def compiled(name, directory, control=False):
    exe = directory / (name + ('-mod11' if control else ''))
    flags = ['-DCONTROL_MOD11'] if control else []
    subprocess.run(['c++', '-std=c++17', '-O3', '-Wall', '-Wextra', '-pedantic',
                    *flags, str(HERE/(name+'.cpp')), '-o', str(exe)], check=True)
    return exe


def output(command):
    return subprocess.run(command, stdout=subprocess.PIPE, text=True, check=True).stdout


def baseline(filename, report):
    require(report == (HERE/filename).read_text(), 'replay differs from '+filename)


def table(report):
    result = {}
    for row in csv.DictReader(io.StringIO(report), delimiter='\t'):
        key = int(row.pop('span')), int(row.pop('endpoints'))
        require(key not in result, 'duplicated census row')
        result[key] = {name: int(value) for name,value in row.items()}
    return result


def reference_jets(arms):
    # Coefficients of (x-1)^k by direct binomial expansion, independent of moments.
    terms = Counter()
    for a,b,A,B,weight in arms:
        for j in range(4):
            terms[(3-j)*a+j*b] += weight*math.comb(3,j)*A**(3-j)*B**j
    return [sum(value*math.comb(t,k) for t,value in terms.items()) for k in range(9)]


def controls(scratch):
    order_seven = reference_jets([(2,3,-1,1,2250),(1,4,-1,1,-125),(0,5,-1,1,9)])
    require(order_seven[:8] == [0]*7+[2925], "order-seven reference failed")
    order_eight = reference_jets([(0,1,1,1,1),(0,10,1,9,4),(1,2,1,9,4)])
    require([v%11 for v in order_eight] == [0]*8+[2], "mod-11 witness failed")
    for name in ('aggregate','two_cubes'):
        print(output([compiled(name,scratch,control=True)]).strip())
    print(output([sys.executable,'-I',HERE/'aggregate_finish.py','--control-mod11']).strip())
    print('PASS direct Taylor controls at orders seven (rational) and eight (modulo eleven)')


def aggregate_run(scratch):
    first = scratch/'first.tsv'
    last = scratch/'last.tsv'
    report = output([compiled('aggregate',scratch),'1','64',first])
    baseline('aggregate.tsv',report)
    rows = table(report)
    cases = set()
    pending = Counter()
    for line in first.read_text().splitlines():
        shape=tuple(map(int,line.split()))
        require(len(shape)==6 and shape not in cases, 'invalid first-stage handoff')
        cases.add(shape)
        pending[max(shape),len(set(shape))] += 1
    require(all(pending[k]==row['unresolved'] for k,row in rows.items())
            and set(pending)<=set(rows), 'first-stage handoff counts disagree')
    final_report=output([sys.executable,'-I',HERE/'aggregate_finish.py',first,last])
    baseline('aggregate_finish.log',final_report)
    require(last.read_bytes()==b'', 'aggregate verifier retains a case')
    return rows


def projected_run(scratch):
    exe=compiled('two_cubes',scratch)
    results=[]
    for name,extra in [('two_cubes',[]),('complement',['complement'])]:
        pending=scratch/(name+'-pending.tsv')
        report=output([exe,'1','64',pending,*extra])
        baseline(name+'.tsv',report)
        require(pending.read_bytes()==b'', name+' retains a case')
        results.append(table(report))
    return results


def multiset_count(vertices):
    return math.comb(math.comb(vertices,2)+2,3)


def coverage(first,second,complement):
    lists=[(first,{3:1,4:18,5:30}), (second,{3:1,4:18,5:30}),
           (complement,{2:1,3:6,4:4,5:0,6:15})]
    for rows,weight in lists:
        require(set(rows)=={(s,v) for s in range(1,65) for v in weight},'missing census row')
        for (s,v),row in rows.items():
            expected=weight[v]*math.comb(s-1,v-2)
            require(sum(row.values())==expected, f'wrong pattern count in {(s,v)}')
            if 'excluded' in row:
                require(row['unresolved']==0, f'unresolved cases in {(s,v)}')
    total=0
    requested=0
    for s in range(1,65):
        pairwise=sum(second[s,v]['excluded'] for v in range(3,6))
        other=sum(complement[s,v]['excluded'] for v in range(2,7))
        expected=multiset_count(s+1)-2*multiset_count(s)+multiset_count(s-1)
        require(pairwise+other==expected,f'all-support count mismatch at span {s}')
        total+=pairwise+other
        if s>=33: requested+=pairwise
    print(f'PASS {requested:,} pairwise-overlap patterns in spans 33-64; both verifiers complete')
    print(f'PASS {total:,} support multisets over all spans 1-64 in the two-cube verifier')
    print('PASS all per-span counts match the independent combinatorial formulas')


def main():
    with tempfile.TemporaryDirectory(prefix='sparse-overlap64-') as tmp:
        directory=Path(tmp)
        controls(directory)
        with ThreadPoolExecutor(max_workers=2) as pool:
            first=pool.submit(aggregate_run,directory)
            second=pool.submit(projected_run,directory)
            coverage(first.result(),*second.result())


if __name__=='__main__':
    main()
