"""Verify both restricted minima, every surviving full source set, and the sharp grid control."""
from collections import Counter
from argparse import ArgumentParser
from itertools import combinations, permutations
from pathlib import Path
from tempfile import TemporaryDirectory
import subprocess

from cores import HERE, ROWS, bits, geometry, physical_tests, projected, run_solver
from sources import survivors

def columns(points, lines, bank):
    pos,neg = projected(points,lines)
    extra = sorted({m & lines for m in bank if (m&lines).bit_count()>1})
    raw = bits(points)+[m<<6 for m in bits(lines)]
    optional=[m<<6 for m in extra]
    for required in raw:
        others = [m for m in raw+optional if m!=required]
        assert any(x & required and not y & required
                   and all(not x&m or y&m for m in others) for x in pos for y in neg)
    return pos,neg,raw,optional

def canonical(rows, core, bank):
    # Normalize physical names, retaining the exact signed tests and every source.
    # Columns of these cores have distinct, nonempty incidence sets.
    points=sum(1<<r for r in rows)
    pos,neg,_,_=columns(points,core,bank)
    best=None
    for order in permutations(bits(points)):
        def point_code(x):
            return sum(1<<i for i,p in enumerate(order) if x&p)
        incidence = {l:point_code(sum(1<<r for r in rows if ROWS[r]&l)) for l in bits(core)}
        assert len(set(incidence.values()))==len(incidence)
        ls=sorted(incidence,key=incidence.get)
        def code(x):
            return point_code(x) | sum(1<<(4+i) for i,l in enumerate(ls) if x & (l<<6))
        key = (tuple(sorted(map(code,pos))),tuple(sorted(map(code,neg))),
               tuple(sorted({code((m&core)<<6) for m in bank}-{0})))
        if best is None or key<best:
            best=key
    return best

def check_ordinary():
    # The ordinary constructions only use the six raw points and eleven raw lines.
    plus,minus=physical_tests()
    raw=[]
    width=1<<17
    for b in range(17):
        step=1<<b
        raw.append(((1<<width)-1)//((1<<(2*step))-1)*(((1<<step)-1)<<step))
    for omitted in [0,*sorted(plus)]:
        wires=raw.copy()
        def add(a,b,is_and):
            wires.append(wires[a]&wires[b] if is_and else wires[a]|wires[b])
            return len(wires)-1
        def join(operands):
            out,*rest=operands
            for other in rest:
                out=add(out,other,False)
            return out
        terms=[]
        for r,row in enumerate(ROWS):
            ls=[6+l.bit_length()-1 for l in bits(row) if 1<<r | l<<6 != omitted]
            terms.append(add(r,join(ls),True))
        out=join(terms)
        assert len(wires)-17 == 29-bool(omitted)
        assert {x for x in plus if not (wires[out]>>x&1)}==({omitted} if omitted else set())
        assert not any(wires[out]>>y&1 for y in minus)
        if not omitted:
            target=0
            for r,row in enumerate(ROWS):
                mask=0
                for l in bits(row):
                    mask |= raw[6+l.bit_length()-1]
                target |= raw[r]&mask
            assert wires[out]==target

def run(binary):
    check_ordinary()
    cached=set()
    totals=Counter()
    for rows in combinations(range(6),4):
        p,u,c,bank=geometry(rows)
        key=canonical(rows,c,bank)
        if key not in cached:
            pos,neg,raw,extra=columns(p,c,bank)
            limit=11 if c.bit_count()==4 else 14
            records=[]
            for idx in range(1<<len(extra)):
                sources=raw+[v for i,v in enumerate(extra) if idx>>i&1]
                answer=run_solver(pos,neg,sources,limit,binary)
                kind,nodes=answer.split()
                assert kind=="EXHAUSTED"
                records.append(int(nodes))
            print("Core",''.join(map(str,rows)),limit,"gates",records,flush=True)
            # Construct a passing core of the next size from row stars.
            # Each bit of a word below represents one physical signed test.
            tests=pos+neg
            columns_on=[sum(1<<i for i,x in enumerate(tests) if x&m) for m in raw]
            def add(a,b,is_and):
                columns_on.append(columns_on[a]&columns_on[b] if is_and else columns_on[a]|columns_on[b])
                return len(columns_on)-1
            terms=[]
            for r in rows:
                line_inputs=[raw.index(l<<6) for l in bits(ROWS[r]&c)]
                val=line_inputs[0]
                for q in line_inputs[1:]: val=add(val,q,False)
                terms.append(add(raw.index(1<<r),val,True))
            output=terms[0]
            for q in terms[1:]: output=add(output,q,False)
            assert len(columns_on)-len(raw)==limit+1 and columns_on[output]==(1<<len(pos))-1
            cached.add(key)
        bank2,remaining=survivors(rows)
        assert bank2==bank
        pos,neg=projected(p,u)
        nodes=0
        for s in sorted(remaining):
            sources=bits(p)+[m<<6 for i,m in enumerate(bank) if s>>i&1]
            answer=run_solver(pos,neg,sources,18,binary)
            kind,count=answer.split()
            assert kind=="EXHAUSTED"
            nodes+=int(count)
        totals["sets"]+=len(remaining)
        totals["nodes"]+=nodes
        print("Active",''.join(map(str,rows)),len(remaining),"sets,",nodes,"states",flush=True)
    assert len(cached)==2 and totals["sets"]==494
    print("All 15 fixed pairs;",len(cached),"distinct signed cores;",dict(totals),flush=True)
    print("29-gate control checked on 131072 inputs; all 24 one-flag 28-gate controls passed.")

if __name__=="__main__":
    cli=ArgumentParser(description=__doc__)
    cli.add_argument("--independent",action="store_true",help="use the separate prefix/suffix circuit enumerator")
    args=cli.parse_args()
    with TemporaryDirectory() as tmp:
        exe=Path(tmp)/"frontier"
        source="crosscheck.cpp" if args.independent else "frontier.cpp"
        subprocess.run(["c++","-O3","-std=c++17",HERE/source,"-o",exe],check=True)
        run(exe)
