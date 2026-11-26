"""Check the certificates for spiders. Python 3.10+, no external packages."""
from itertools import product
from pathlib import Path
from subprocess import run
import json
import sys

HERE = Path(__file__).resolve().parent
# Earlier gate masks, in the order of the published four-gate reduction.
HOSTS = (
    ((0,0),(0,0),(0,3),(1,2)),
    ((0,0),(0,0),(1,2),(1,2)),
    ((0,0),(0,1),(0,2),(0,3)),
    ((0,0),(0,1),(0,3),(1,2)),
    ((0,0),(0,1),(1,2),(1,2)),
)

def zero_cell(wiring, code):
    gates = 0
    for index, (left, right) in enumerate(wiring):
        a = bool(code & (1 << (2*index))) and (left & gates) == left
        b = bool(code & (1 << (2*index+1))) and (right & gates) == right
        if a or b:
            gates |= 1 << index
    return (gates & 12) == 12

def maximal_pairs(wiring):
    table = [zero_cell(wiring, x) for x in range(256)]
    # Enumerate extremal ordered pairs by their union and intersection directly.
    maxima = {z for z,t in enumerate(table) if not t and
              all(table[y] for y in range(256) if y!=z and (y&z)==z)}
    pairs = [(r,c) for r,c in product(range(256), repeat=2)
             if (r|c)==255 and (r&c) in maxima]
    return table,pairs

def spider(legs):
    """Rows at even distance from the hub. Columns at odd distance."""
    next_row, next_col = 1, 0
    edges = set()
    for length in legs:
        vertex = 0
        for level in range(1,length+1):
            if level % 2:
                edges.add((vertex,next_col))
                vertex = next_col
                next_col += 1
            else:
                edges.add((next_row,vertex))
                vertex = next_row
                next_row += 1
    return next_row,next_col,edges

def evaluate_shape(shape, mask):
    if shape == -1:
        return bool(mask & 63)  # six rectangles joined
    a,b,c,d,e,f,g,h,k = [bool(mask & (1<<i)) for i in range(9)]
    if shape == 0:
        return (((a or b) and (c or d)) or e) and (f or g) and (h or k)
    if shape == 3:
        return (a or b or c or d or e) and (f or g)
    raise ValueError('unknown shape')

def check_formulas(formulas):
    for w in formulas:
        m,n,edges = spider(w['legs'])
        row,col = w['row'],w['column']
        assert (len(row),len(col)) == (m,n)
        for r,c in product(range(m),range(n)):
            assert ((r,c) in edges) != evaluate_shape(w['shape'],row[r]&col[c])

def check_negative(w):
    m,n,edges = spider(w['legs'])
    # Thus every vertex label on BOTH sides must satisfy f(label)=1.
    assert all(any((r,c) not in edges for c in range(n)) for r in range(m))
    assert all(any((r,c) not in edges for r in range(m)) for c in range(n))
    chosen = [tuple(p) for p in w['matching']]
    assert set(chosen) <= edges
    assert len({r for r,_ in chosen})==len(chosen)==len({c for _,c in chosen})
    return [sum(1<<j for j,(_,c) in enumerate(chosen) if (r,c) in edges)
            for r,_ in chosen]

def profiles():
    # Each arm uses floor(length/2) matching edges away from the hub.
    # An odd arm admits one further edge using the hub. At most one can do so.
    def visit(legs, pairs, odd):
        if pairs + int(odd) > 11:
            return
        yield legs
        if legs and legs[-1]==1:
            return
        for k in range(1,(legs[-1] if legs else 22)+1):
            yield from visit(legs+(k,),pairs+k//2,odd or bool(k%2))
    yield from visit((),0,False)

def contains(bigger, smaller):
    return len(bigger)>=len(smaller) and all(a>=b for a,b in zip(bigger,smaller))

def main(executable):
    data = json.loads((HERE/'evidence.json').read_text())
    yes,no = data['formulas'],data['exclusions']
    assert (len(yes),len(no)) == (44,57)
    check_formulas(yes)
    patterns = [check_negative(w) for w in no]
    universe = list(profiles())
    assert len(universe)==2486
    for legs in universe:
        assert (any(contains(w['legs'],legs) for w in yes)
                or any(contains(legs,w['legs']) for w in no)), legs
    print(f'{len(universe)} profiles covered by {len(yes)} explicit formulas and '
          f'{len(no)} forbidden spiders.',flush=True)
    rows=[]
    # Independent positive controls, obtained from a separate forest enumerator.
    # Pair indices use lexicographic (row, column) order in maximal_pairs.
    witnesses = (158608847799196,141012904215452,6721376474,619583112092,1168265741212)
    for wiring,witness in zip(HOSTS,witnesses):
        truth,pairs = maximal_pairs(wiring)
        chosen = [pair for i,pair in enumerate(pairs) if witness & (1<<i)]
        assert len(chosen)==11 and len({r for r,_ in chosen})==len({c for _,c in chosen})==11
        # Test acyclicity in the actual 22-vertex bipartite graph, without contraction.
        parent=list(range(22))
        def root(v):
            while v!=parent[v]:
                v=parent[v]
            return v
        for i,(r,_) in enumerate(chosen):
            for j,(_,c) in enumerate(chosen):
                if not truth[r&c]:
                    left,right=root(i),root(11+j)
                    assert left!=right
                    parent[left]=right
        # Correct upper bound uses every pair, including a full-neighborhood label.
        # The restricted exclusions have already passed the no-universal-vertex check.
        interior = sum(1<<i for i,(r,c) in enumerate(pairs) if truth[r] and truth[c])
        cross = [sum(1<<j for j,(_,c) in enumerate(pairs) if not truth[r&c])
                 for r,_ in pairs]
        rows.append([len(pairs),interior,*cross])
    stream = [str(len(patterns))]+[' '.join(map(str,[len(p),*p])) for p in patterns]
    stream += [' '.join(map(str,r)) for r in rows]
    run([str(Path(executable).resolve())],input='\n'.join(stream)+'\n',text=True,check=True)

if __name__=='__main__':
    if not __debug__ or len(sys.argv)!=2:
        raise SystemExit('Run python3 -I -B replay.py /path/to/checker with assertions enabled.')
    main(sys.argv[1])
