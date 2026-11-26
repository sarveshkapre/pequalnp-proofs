"""Replay the finite proof through order 23 with the published matching checker."""
import gzip
import json
from pathlib import Path
import runpy
import sys

HERE = Path(__file__).resolve().parent
TREE = runpy.run_path(str(HERE / 'trees.py'))
PRIOR = runpy.run_path(str(HERE.parent / 'five-leaves' / 'replay.py'))


def flat(rows, n, words):
    """Each bit gives a free union missing exactly one nonedge rectangle."""
    assert len(rows) == len(words) and all(x < 64 for x in words)
    adjacent = [0]*6
    for word, row in zip(words, rows):
        for b in range(6):
            if word >> b & 1:
                adjacent[b] |= row
    for word, row in zip(words, rows):
        predicted = (1 << n)-1
        for b, neighbors in enumerate(adjacent):
            if word >> b & 1:
                predicted &= neighbors
        assert predicted == row


def nested(rows, n, words):
    assert len(words) == len(rows)+n and all(0 <= x < 128 for x in words)
    for i, row in enumerate(rows):
        for j, col in enumerate(words[len(rows):]):
            both = words[i] & col
            assert bool(row >> j & 1) == (not (both & 15) or not (both & 112))


def independent_count(n):
    """Tree dissymmetry on the nonleaf core, with optional private leaves."""
    from math import comb
    a, multiset = [0]*(n+1), [1]+[0]*n
    for k in range(2,n+1):
        # A nonroot core vertex without children must carry a private leaf.
        a[k] = (k == 2) + multiset[k-1] + (multiset[k-2] if k > 2 else 0)
        for total in range(n,k-1,-1):
            multiset[total] += sum(comb(a[k]+j-1,j)*multiset[total-j*k]
                                   for j in range(1,total//k+1) if a[k])
    rooted = multiset[n-1] - a[n-1] + multiset[n-2]
    oriented = sum(a[k]*a[n-k] for k in range(n+1))
    symmetric = a[n//2] if n%2 == 0 else 0
    return rooted - (oriented-symmetric)//2


def pattern_key(rows):
    """Isomorphism of directed forests after contracting the specified matching."""
    n = len(rows)
    adj = [[j for j in range(n) if i != j and ((row >> j | rows[j] >> i) & 1)]
           for i, row in enumerate(rows)]
    def rooted(v, parent):
        pieces = [('>' if rows[v] >> w & 1 else '<') + rooted(w,v)
                  for w in adj[v] if w != parent]
        return '(' + ''.join(sorted(pieces)) + ')'
    unseen, parts = set(range(n)), []
    while unseen:
        seed = min(unseen)
        stack, component = [seed], {seed}
        while stack:
            for w in adj[stack.pop()]:
                if w not in component:
                    component.add(w)
                    stack.append(w)
        assert sum(len(adj[v]) for v in component) == 2*(len(component)-1)
        assert all(not (rows[v] >> w & rows[w] >> v & 1)
                   for v in component for w in adj[v])
        parts.append(min(rooted(v,-1) for v in component))
        unseen -= component
    return ''.join(sorted(parts))


def check_catalogue(patterns, program):
    """A normalized forest is obtained by deleting some directed cross edges."""
    import subprocess
    lines = []
    for i, wiring in enumerate(PRIOR['STAR']['HOSTS']):
        table, pairs = PRIOR['STAR']['maximal_pairs'](wiring)
        pairs = [(a,b) for a,b in pairs if table[a] and table[b]]
        arcs = [sum(1 << j for j, (_, b) in enumerate(pairs) if i != j and not table[a&b])
                for i, (a, _) in enumerate(pairs)]
        lines.append(' '.join(map(str,[i,len(pairs),*arcs])))
    result = subprocess.run([str(Path(program).resolve())], input='\n'.join(lines)+'\n',
                            capture_output=True, text=True, check=True)
    known = {}
    for line in result.stdout.splitlines():
        _, size, key = line.split()
        known.setdefault(int(size),set()).add(key)
    assert set(known) == {8,9,10,11} and all(known.values())
    lower = {n:min(c.count('<')+c.count('>') for c in codes) for n,codes in known.items()}
    cache = {}
    def fits(rows, edges):
        if edges < lower[len(rows)]:
            return False
        key = pattern_key(rows)
        if key in known[len(rows)]:
            return True
        if key not in cache:
            cache[key] = any(fits(rows[:i]+(row^(1<<j),)+rows[i+1:], edges-1)
                             for i,row in enumerate(rows) for j in range(len(rows))
                             if i != j and row >> j & 1)
        return cache[key]
    for rows in patterns:
        assert len(rows) in known
        assert not fits(rows,sum(row.bit_count()-1 for row in rows))
    print('Every directed matching exclusion passed the normalized-forest catalogue.',flush=True)


def main(program, direct):
    exceptional, patterns = set(), set()
    with gzip.open(HERE / 'order23.bin.gz','rb') as cert:
        for index, tree in enumerate(TREE['assemble'](23,11), 1):
            rows, n = TREE['matrix'](tree)
            assert len(rows) + n == 23
            tag, = cert.read(1)
            if tag == 0:
                flat(rows, n, cert.read(len(rows)))
            else:
                assert 2 <= tag <= 11
                cells = cert.read(tag)
                assert len(cells) == tag
                patterns.add(PRIOR['matching_pattern'](rows, n, cells))
                exceptional.add(TREE['canonical'](TREE['adjacency'](tree)))
        assert not cert.read(1)
    assert index == independent_count(23) == 528196 and len(exceptional) == 2591
    print(f'Order 23: {index-len(exceptional):,} explicit formulas and '
          f'{len(exceptional):,} exceptional trees with matchings.', flush=True)
    small = json.loads((HERE/'small.json').read_text())
    used = set()
    for order, expected in [(22,138), (21,9), (20,0)]:
        parents = TREE['exceptional_parents'](exceptional)
        assert len(parents) == expected
        exceptional = set()
        for tree in parents:
            rows,n = TREE['matrix'](tree)
            assert len(rows)+n == order
            kind, *data = small[tree]
            used.add(tree)
            if kind == 'm':
                patterns.add(PRIOR['matching_pattern'](rows,n,data))
                exceptional.add(tree)
            else:
                assert kind == 'u'
                nested(rows,n,data)
        print(f'Order {order}: {len(parents)} trees without an inherited formula, '
              f'{len(exceptional)} matching certificates.', flush=True)
    assert not exceptional and used == small.keys()
    print(f'Checking {len(patterns)} distinct ordered patterns in all five hosts.',flush=True)
    representatives = {pattern_key(p): p for p in sorted(patterns)}
    print(f'{len(representatives)} patterns up to relabelling matched pairs.', flush=True)
    if direct:
        PRIOR['verify_matching_patterns'](list(representatives.values()),program)
    else:
        check_catalogue(representatives.values(),program)
    print('All positive and negative certificates through order 23 passed.',flush=True)


if __name__ == '__main__':
    if not __debug__ or len(sys.argv) not in (2,3) or (len(sys.argv)==3 and sys.argv[2]!='--direct'):
        raise SystemExit('Run with assertions enabled and supply the compiled matching checker.')
    main(sys.argv[1], len(sys.argv)==3)
