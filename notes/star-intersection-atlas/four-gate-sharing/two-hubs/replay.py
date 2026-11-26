"""Replay the leaf-core and two-branch certificates using only the Python standard library."""
from functools import lru_cache
from itertools import product
from pathlib import Path
import json
import runpy
import subprocess
import sys

HERE = Path(__file__).resolve().parent
F = runpy.run_path(str(HERE/'formulas.py'))
SPIDER = runpy.run_path(str(HERE.parent/'spiders'/'replay.py'))


def order_tree(code):
    """Read the canonical parenthesis tree in preorder, rooting even levels at minima."""
    edges, parity, stack = [], [], []
    for token in code:
        if token == '(':
            v=len(parity)
            parity.append(len(stack)%2)
            if stack:
                edges.append((stack[-1],v))
            stack.append(v)
        else:
            assert token==')'
            stack.pop()
    assert not stack
    return {(a,b) if not parity[a] else (b,a) for a,b in edges}


def adjacency(n, edges):
    neighbors=[[] for _ in range(n)]
    for u,v in edges:
        neighbors[u].append(v)
        neighbors[v].append(u)
    return neighbors


def unrooted_key(neighbors):
    def from_root(v,parent):
        return '('+''.join(sorted(from_root(u,v) for u in neighbors[v] if u!=parent))+')'
    return min(from_root(v,-1) for v in range(len(neighbors)))


@lru_cache(maxsize=None)
def rooted_trees(n):
    """A root with an unordered multiset of children totaling n-1 vertices."""
    if n==1:
        return ('()',)
    children=sorted((k,s) for k in range(1,n) for s in rooted_trees(k))
    def choose(total,start):
        if total==0:
            yield ''
            return
        for i in range(start,len(children)):
            size,code=children[i]
            if size>total:
                break
            for rest in choose(total-size,i):
                yield code+rest
    return tuple('('+s+')' for s in choose(n-1,0))


def evaluate(shape,x):
    if shape==-1:
        return bool(x&63)
    if shape==3:
        return bool(x&31) and bool(x&96)
    if shape==2:
        return bool(x&15) and bool(x&112)
    if shape==1:
        return bool(x&7) and bool(x&56) and bool(x&192)
    return SPIDER['evaluate_shape'](shape,x)


def check_cores():
    data=json.loads((HERE/'cores.json').read_text())
    constructed=set()
    for n in (11,12):
        for code in rooted_trees(n):
            constructed.add(unrooted_key(adjacency(n,order_tree(code))))
    assert len(constructed)==235+551
    assert set(data['cube']).isdisjoint(data['nested'])
    assert set(data['cube'])|set(data['nested']) == constructed
    for code in constructed:
        n=len(code)//2
        edges=order_tree(code)
        if code in data['cube']:
            words=data['cube'][code]
            assert len(words)==n and all(0<=x<64 for x in words)
            for i,j in product(range(n),repeat=2):
                assert F['subset'](words[i],words[j])==(i==j or (i,j) in edges)
        else:
            shape,rows,cols=data['nested'][code]
            assert n==12 and shape==3 and len(rows)==len(cols)==n
            for i,j in product(range(n),repeat=2):
                assert evaluate(shape,rows[i]&cols[j])!=(i==j or (i,j) in edges)
    print('All 235 order-11 and 551 order-12 tree cores covered.')


def tree(profile):
    distance,a,b,c,e=profile
    edges=[(i,i+1) for i in range(distance)]
    n=distance+1
    for root,length in ((0,a),(0,b),(distance,c),(distance,e)):
        v=root
        for _ in range(length):
            edges.append((v,n))
            v=n
            n+=1
    neighbors=adjacency(n,edges)
    parity=[0]*n
    for u,v in edges:
        parity[v]=1-parity[u]
    left=[v for v in range(n) if not parity[v]]
    right=[v for v in range(n) if parity[v]]
    if len(left)>len(right):
        left,right=right,left
    return [sum(1<<j for j,v in enumerate(right) if v in neighbors[u]) for u in left],len(right)


def profiles():
    pairs=[(a,b) for a in range(2,21) for b in range(1,a+1) if a+b<=20]
    for A in pairs:
        for B in pairs:
            if A<B:
                continue
            for d in range(1,21-A[0]-B[0]):
                odd_left = int(any(x % 2 for x in A))
                odd_right = int(any(x % 2 for x in B))
                matching = sum(x // 2 for x in A+B) + (d+1+odd_left+odd_right)//2
                if matching<=11:
                    yield (d,*A,*B)


def contains(big,small):
    if big[0]!=small[0]:
        return False
    pairs=big[1:]
    return any(all(x<=y for x,y in zip(small[1:],orientation))
               for orientation in (pairs,pairs[2:]+pairs[:2]))


def check_profiles(executable):
    data=json.loads((HERE/'profiles.json').read_text())
    good,bad=data['formulas'],data['exclusions']
    universe=set(profiles())
    assert len(universe)==4156
    for p,s,row,col in good:
        assert tuple(p) in universe and s in {-1,0,1,2,3}
        matrix,n=tree(p)
        assert len(row)==len(matrix) and len(col)==n
        for i,r in enumerate(row):
            for j,c in enumerate(col):
                assert bool(matrix[i]>>j&1)!=evaluate(s,r&c)
    patterns=[]
    for p,matching in bad:
        assert tuple(p) in universe
        matrix,n=tree(p)
        assert all(r!=(1<<n)-1 for r in matrix)
        assert all(any(not(r>>j&1) for r in matrix) for j in range(n))
        pairs=[divmod(cell,n) for cell in matching]
        assert all(0<=u<len(matrix) and matrix[u]>>v&1 for u,v in pairs)
        assert len({u for u,_ in pairs})==len(pairs)==len({v for _,v in pairs})
        patterns.append([sum(1<<j for j,(_,v) in enumerate(pairs) if matrix[u]>>v&1)
                         for u,_ in pairs])
    for p in universe:
        assert any(contains(w,p) for w,*_ in good) or any(contains(p,w) for w,_ in bad)
    hosts=[]
    for wiring in SPIDER['HOSTS']:
        truth,pairs=SPIDER['maximal_pairs'](wiring)
        interior=sum(1<<i for i,(r,c) in enumerate(pairs) if truth[r] and truth[c])
        cross=[sum(1<<j for j,(_,c) in enumerate(pairs) if not truth[r&c]) for r,_ in pairs]
        hosts.append([len(pairs),interior,*cross])
    lines=[[len(patterns)]]+[[len(p),*p] for p in patterns]+hosts
    stream='\n'.join(' '.join(map(str,row)) for row in lines)+'\n'
    subprocess.run([str(Path(executable).resolve())],input=stream,text=True,check=True)
    print(f'{len(universe):,} two-branch profiles covered by {len(good)} formulas and {len(bad)} exclusions.')


if __name__=='__main__':
    if not __debug__ or len(sys.argv)!=2:
        raise SystemExit('Use python3 -I -B replay.py /path/to/spider-matching-check with assertions enabled.')
    F['verify']()
    runpy.run_path(str(HERE/'three_gate.py'))['verify'](F['bistar_edges'](8))
    check_cores()
    check_profiles(sys.argv[1])
