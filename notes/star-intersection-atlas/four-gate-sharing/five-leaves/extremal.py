"""Classify the reduced 25-vertex trees in all five hosts and replay their formulas."""
from itertools import product
from pathlib import Path
import json
import runpy
import subprocess
import sys

HERE = Path(__file__).resolve().parent
STAR = runpy.run_path(str(HERE.parent/'spiders'/'replay.py'))


def incidence(table, rows, columns):
    return tuple(sum((not table[r&c]) << j for j,c in enumerate(columns)) for r in rows)


def tree_code(rows, n):
    """Root the tree at a center, sort unordered branches, and allow swapping the shores."""
    m = len(rows)
    adj = [[] for _ in range(m+n)]
    for i,mask in enumerate(rows):
        for j in range(n):
            if mask >> j & 1:
                adj[i].append(m+j)
                adj[m+j].append(i)
    assert sum(map(len,adj)) == 2*(m+n-1)
    assert len(set(rows)) == m and all(rows)
    columns = [sum(((r>>j)&1)<<i for i,r in enumerate(rows)) for j in range(n)]
    assert len(set(columns)) == n and all(columns)
    degree = list(map(len,adj))
    leaves = [v for v,d in enumerate(degree) if d==1]
    remaining = m+n
    while remaining > 2:
        assert leaves
        remaining -= len(leaves)
        next_layer = []
        for v in leaves:
            for w in adj[v]:
                degree[w] -= 1
                if degree[w] == 1:
                    next_layer.append(w)
        leaves = next_layer

    def rooted(v, parent):
        return '(' + ''.join(sorted(rooted(w,v) for w in adj[v] if w!=parent)) + ')'

    return min(rooted(v,-1) for v in leaves)


def decode(code):
    stack, edges = [], []
    rows = columns = 0
    for ch in code:
        if ch == ')':
            stack.pop()
            continue
        assert ch == '('
        if len(stack) % 2:
            v = columns
            columns += 1
            edges.append((stack[-1],v))
        else:
            v = rows
            rows += 1
            if stack:
                edges.append((v,stack[-1]))
        stack.append(v)
    assert not stack
    return tuple(sum(1<<j for u,j in edges if u==i) for i in range(rows)), columns


def components(target):
    groups = list(range(len(target)))
    for i,mask in enumerate(target):
        for j in range(i):
            if mask>>j&1 or target[j]>>i&1:
                a,b = groups[i],groups[j]
                groups = [a if k==b else k for k in groups]
    assert len(set(groups)) == 6
    return groups


def smaller_labels(word, opposite, table, signatures):
    """Retain original labels whose enlargement could give this matched endpoint."""
    by_type = {}
    for x in range(256):
        if not table[x] or (x&word)!=x:
            continue
        if any(table[word&y] and not table[x&y] for y in opposite):
            continue
        by_type[signatures[x]] = x
    return list(by_type.values())


def possible_connectors(opposite, side, table, signatures, group):
    by_type = {}
    for x in range(256):
        hits = [i for i,y in enumerate(opposite) if not table[x&y]]
        if len(hits)==2 and group[hits[0]]!=group[hits[1]]:
            by_type[signatures[x]] = (x,side,*hits)
    return list(by_type.values())


def spanning_selections(candidates, group, table):
    def choose(start, parts, chosen):
        if len(chosen)==5:
            assert len(set(parts))==1
            yield chosen
            return
        for pos in range(start,len(candidates)-(5-len(chosen))+1):
            x,side,a,b = candidates[pos]
            left,right = parts[a],parts[b]
            if left==right:
                continue
            if any(other!=side and not table[x&y] for y,other,_,_ in chosen):
                continue
            merged = [left if g==right else g for g in parts]
            yield from choose(pos+1,merged,chosen+[candidates[pos]])
    yield from choose(0,group,[])


def classify(table, selected, seen):
    original_a, original_b = zip(*selected)
    target = incidence(table,original_a,original_b)
    group = components(target)
    signatures = [tuple(table[x&j] for j in range(256)) for x in range(256)]
    row_options = [smaller_labels(a,original_b,table,signatures) for a in original_a]
    col_options = [smaller_labels(b,original_a,table,signatures) for b in original_b]
    shapes = set()
    lifts = selections = 0
    for r,c in product(product(*row_options),product(*col_options)):
        if incidence(table,r,c)!=target:
            continue
        lifts += 1
        candidates = (possible_connectors(c,0,table,signatures,group) +
                      possible_connectors(r,1,table,signatures,group))
        for chosen in spanning_selections(candidates,group,table):
            selections += 1
            rows = list(target)
            n = len(c)
            for _,side,a,b in chosen:
                if side:
                    rows[a] |= 1<<n
                    rows[b] |= 1<<n
                    n += 1
                else:
                    rows.append((1<<a)|(1<<b))
            key = (tuple(rows),n)
            if key not in seen:
                seen[key] = tree_code(*key)
            shapes.add(seen[key])
    return shapes, lifts, selections


def main(executable):
    hosts, lines = [], []
    for wiring in STAR['HOSTS']:
        table, pairs = STAR['maximal_pairs'](wiring)
        interior = [(a,b) for a,b in pairs if table[a] and table[b]]
        a,b = zip(*interior)
        lines.append(' '.join(map(str,[len(a),*incidence(table,a,b)])))
        hosts.append((table,interior))
    run = subprocess.run([str(Path(executable).resolve())],text=True,check=True,capture_output=True,
                         input='\n'.join(lines)+'\n')
    cases = []
    for line in run.stdout.splitlines():
        if line.startswith('case '):
            _,h,mask = line.split()
            cases.append((int(h),int(mask)))
        else:
            print(line,flush=True)
    assert len(set(cases))==len(cases)==11
    seen, by_host = {}, [set() for _ in range(5)]
    lifts = selections = 0
    for h,mask in cases:
        table,pairs = hosts[h]
        selected = [p for i,p in enumerate(pairs) if mask>>i&1]
        assert len(selected)==10
        shapes,l,s = classify(table,selected,seen)
        by_host[h].update(shapes)
        lifts += l
        selections += s
    assert [bool(shapes) for shapes in by_host]==[True,False,True,True,True]
    shapes = set.union(*by_host)
    formulas = json.loads((HERE/'order25.json').read_text())
    assert shapes==set(formulas) and (len(shapes),lifts,selections)==(313,336,439392)
    for shape,codes in formulas.items():
        rows,n = decode(shape)
        assert len(rows)+n==25 and tree_code(rows,n)==shape
        assert len(codes)==len(rows) and all(0<=x<64 for x in codes)
        cols = [63]*n
        for i,row in enumerate(rows):
            for j in range(n):
                if row>>j&1:
                    cols[j] &= ~codes[i]
        assert all(bool(row>>j&1)==(codes[i]&c==0)
                   for i,row in enumerate(rows) for j,c in enumerate(cols))
    # Maximum order for the second host is 23. Check the witness from its raw words.
    rows = [125,127,183,191,222,223,239,245,246,249,250,111]
    cols = [254,191,251,127,253,239,223,250,249,246,245]
    assert len(tree_code(incidence(hosts[1][0],rows,cols),len(cols)))==46
    print(f'{lifts} assignments and {selections:,} spanning selections. All {len(shapes)} '
          'unlabeled order-25 trees have an explicit five-gate formula.',flush=True)


if __name__=='__main__':
    if len(sys.argv)!=2 or not __debug__:
        raise SystemExit('Use python3 -I -B extremal.py /path/to/contact-check with assertions enabled.')
    main(sys.argv[1])
