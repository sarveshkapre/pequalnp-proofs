"""Cross-check grammar coverage at smaller widths and replay two eight-mixed controls."""
import argparse
from itertools import combinations
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory
import sys

from classify import HERE, SHAPES, normalize
from mixing_bound_six import input_tables, row_profiles
from mixing_bound_seven import dag_tables
from split import project  # establishes import paths for the physical row helpers
from cases import ROWS, cases
sys.path.insert(0, str(HERE.parents[2]))
from pair_prune import layout, traces


def independent_profiles(width, shape):
    inputs = input_tables((1,2,4), width)
    leaves = tuple((column, i<3, i>=3) for i,column in enumerate(inputs))
    profiles=set()
    for table in dag_tables(leaves,1):
        data=row_profiles(table,width,SHAPES[shape])
        if data is None:
            continue
        domain, goals=data
        bits=[0]*8
        for code in range(1,1<<width):
            if domain>>code & 1:
                kind=sum(((g>>code)&1)<<i for i,g in enumerate(goals))
                bits[kind] |= 1<<code
        profiles.add(tuple(bits))
    return {normalize(bits,width,shape) for bits in profiles}


def crosscheck(executable):
    with TemporaryDirectory() as scratch:
        path=Path(scratch)/'raw.tsv'
        for width in (3,4):
            subprocess.run([executable,str(width),path],capture_output=True,check=True)
            observed={s:set() for s in SHAPES}
            for row in path.read_text().splitlines():
                s,_,_,_,*bits=row.split('\t')
                observed[s].add(normalize(tuple(map(int,bits)),width,s))
            for shape in SHAPES:
                assert observed[shape] == independent_profiles(width,shape)
                print('Independent labeled DAG enumeration:',width,'lines',shape,len(observed[shape]),'classes')


def control(chosen, shared_point):
    """Both halves of row 0 reach the output through different final arms."""
    frozen, _, _ = layout(chosen)
    gates = []
    first = 30+len(frozen)
    def new(op, a, b):
        gates.append((op,a,b))
        return first+len(gates)-1
    def union(wires):
        v,*tail=wires
        for w in tail: v=new('or',v,w)
        return v
    def row_inputs(p):
        return [6+j for j in range(11) if ROWS[p]>>j&1]
    p,q,r=chosen
    half,rest=row_inputs(p)[:2],row_inputs(p)[2:]
    b,c=union(half),union(rest)
    whole=union([b,c])
    d,e=union(row_inputs(q)),union(row_inputs(r))
    assert len(gates)==9
    if shared_point:
        # p is reused, but the mixed a = p AND b is read only once.
        a=new('and',p,b)
        a=new('and',a,whole)
        second=new('and',p,c)
    else:
        a=new('and',p,whole)
        second=new('and',a,c)
        a=new('and',a,b)
    left=new('or',a,second)
    qterm,rterm=new('and',q,d),new('and',r,e)
    out=union([left,qterm,rterm])
    assert len(gates)==17
    pure_sources={whole,b,c,d,e}
    occurrences={}
    for _,x,y in gates[9:]:
        for w in (x,y): occurrences[w]=occurrences.get(w,0)+1
    boundary={x for x in occurrences if x<first+9}
    assert boundary=={p,q,r,*pure_sources}
    twice,=[w for w,n in occurrences.items() if n==2]
    assert twice==(p if shared_point else first+9)
    assert all(n<=2 for n in occurrences.values())
    fixed_outputs=[30+i for i,(op,_,_) in enumerate(frozen) if op=='and']
    assert len(fixed_outputs)==3
    out=union([out,*fixed_outputs])
    tests=cases()
    assert traces(frozen+gates,tests)[-1]==sum(t[2]<<i for i,t in enumerate(tests))
    assert out==first+len(gates)-1


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('executable',type=Path)
    args=parser.parse_args()
    crosscheck(args.executable.resolve())
    for chosen in combinations(range(6),3):
        for shared_point in (True,False):
            control(chosen,shared_point)
    print('40 positive controls on all 177 physical tests, repeating a mixed wire or a point.')
