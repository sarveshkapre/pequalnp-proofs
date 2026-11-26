"""Verify the five-leaf classification. Requires Python 3.10+ and the sibling matching checker."""
from collections import deque
from functools import lru_cache
from itertools import combinations
from pathlib import Path
import json
import runpy
import subprocess
import sys


HERE = Path(__file__).resolve().parent
SPIDERS = HERE.parent / 'spiders'
STAR = runpy.run_path(str(SPIDERS / 'replay.py'))
SEEDS = ((1, 2, 2, 1, 2, 1), (1, 1, 1, 2, 1, 2, 1))


def canonical(p):
    if len(p) == 6:
        return (p[0], *sorted(p[1:4], reverse=True), *sorted(p[4:], reverse=True))
    d, e, h, a, b, c, f = p
    left, right = sorted(((d, max(a,b), min(a,b)), (e, max(c,f), min(c,f))))
    return (left[0], right[0], h, *left[1:], *right[1:])


def tree(p):
    """Edges in parent-before-child order, including the spine between the hubs."""
    if len(p) == 6:
        d, a, b, c, f, h = p
        end = d
        arms = ((0,a), (0,b), (0,c), (d,f), (d,h))
    else:
        d, e, h, a, b, c, f = p
        end = d+e
        arms = ((d,h), (0,a), (0,b), (end,c), (end,f))
    edges = [(v, v+1) for v in range(end)]
    n = end+1
    for root, length in arms:
        for _ in range(length):
            edges.append((root,n))
            root, n = n, n+1
    adjacent = [[] for _ in range(n)]
    color = [0] * n
    for parent, child in edges:
        adjacent[parent].append(child)
        adjacent[child].append(parent)
        color[child] = 1-color[parent]
    cols = {v:i for i,v in enumerate(v for v in range(n) if color[v])}
    rows = [sum(1 << cols[w] for w in adjacent[v]) for v in range(n) if not color[v]]
    return adjacent, rows, len(cols)


def invariants(adjacent):
    """Tree matching by greedy disjoint leaf edges, diameter by two longest child paths."""
    n = len(adjacent)
    height, used = [0]*n, [False]*n
    matching = diameter = 0
    for v in reversed(range(n)):
        children = [w for w in adjacent[v] if w > v]
        free = next((w for w in children if not used[w]), None)
        if free is not None:
            used[v] = used[free] = True
            matching += 1
        heights = sorted([height[w]+1 for w in children] + [0,0], reverse=True)
        height[v] = heights[0]
        diameter = max(diameter, sum(heights[:2]))
    return matching, diameter


def enumerate_profiles(seed):
    seen, accepted, queue = {seed}, set(), deque([seed])
    while queue:
        p = queue.popleft()
        adjacent, _, _ = tree(p)
        matching, diameter = invariants(adjacent)
        if matching > 11 or diameter > 20:
            continue
        accepted.add(p)
        for j in range(len(p)):
            larger = canonical(p[:j] + (p[j]+1,) + p[j+1:])
            if larger not in seen:
                seen.add(larger)
                queue.append(larger)
    return accepted


def old_obstructions():
    spiders = [tuple(w['legs']) for w in json.loads((SPIDERS/'evidence.json').read_text())['exclusions']]
    pairs = {}
    previous = json.loads((HERE.parent/'two-hubs'/'profiles.json').read_text())
    for (d,a,b,c,f), _ in previous['exclusions']:
        pairs.setdefault(d, []).extend([((a,b),(c,f)), ((c,f),(a,b))])

    @lru_cache(maxsize=None)
    def bad_star(lengths):
        return any(len(s) <= len(lengths) and all(x <= y for x,y in zip(s,lengths)) for s in spiders)

    @lru_cache(maxsize=None)
    def bad_pair(d, left, right):
        return any(all(x <= y for x,y in zip(a,left)) and all(x <= y for x,y in zip(b,right))
                   for a,b in pairs.get(d, []))
    return bad_star, bad_pair


def earlier_result(adjacent, bad_star, bad_pair):
    # Small cores have an earlier formula. Otherwise look for an earlier forbidden induced tree.
    if sum(len(ns)>1 for ns in adjacent) <= 12:
        return True
    hubs = [v for v,ns in enumerate(adjacent) if len(ns)>2]
    branches = {}
    for h in hubs:
        longest = {}
        for neighbor in adjacent[h]:
            stack = [(neighbor,h,1)]
            while stack:
                v,parent,dist = stack.pop()
                longest[neighbor] = max(longest.get(neighbor,0),dist)
                if v in hubs:
                    branches[h,v] = (neighbor,dist)
                stack.extend((w,v,dist+1) for w in adjacent[v] if w != parent)
        branches[h,h] = longest
        if bad_star(tuple(sorted(longest.values(),reverse=True))):
            return True
    for a,b in combinations(hubs,2):
        def outward(v,w):
            first,_ = branches[v,w]
            return tuple(sorted((n for u,n in branches[v,v].items() if u!=first),reverse=True)[:2])
        if bad_pair(branches[a,b][1],outward(a,b),outward(b,a)):
            return True
    return False


def close(profiles, seeds, increment):
    """Extend a negative certificate or truncate a positive one along the five outer arms."""
    covered = set(seeds)
    queue = list(covered)
    for p in queue:
        start = 1 if len(p)==6 else 2
        for j in range(start,len(p)):
            q = canonical(p[:j] + (p[j]+increment,) + p[j+1:])
            if q in profiles and q not in covered:
                covered.add(q)
                queue.append(q)
    return covered


def matching_pattern(rows,n,matching):
    assert all(row!=(1<<n)-1 for row in rows)
    assert all(any(not (row>>j&1) for row in rows) for j in range(n))
    cells = [divmod(cell,n) for cell in matching]
    assert all(0<=r<len(rows) and (rows[r]>>c&1) for r,c in cells)
    assert len({r for r,_ in cells}) == len(cells) == len({c for _,c in cells})
    return tuple(sum(1<<j for j,(_,c) in enumerate(cells) if rows[r]>>c&1) for r,_ in cells)


def verify_matching_patterns(patterns,executable):
    hosts = []
    for wiring in STAR['HOSTS']:
        table, pairs = STAR['maximal_pairs'](wiring)
        interior = sum(1<<i for i,(a,b) in enumerate(pairs) if table[a] and table[b])
        masks = [sum(1<<j for j,(_,b) in enumerate(pairs) if not table[a&b]) for a,_ in pairs]
        hosts.append([len(pairs),interior,*masks])
    for i in range(0,len(patterns),300):
        batch = patterns[i:i+300]
        lines = [[len(batch)]] + [[len(p),*p] for p in batch] + hosts
        subprocess.run([str(Path(executable).resolve())],check=True,text=True,
                       input=''.join(' '.join(map(str,row))+'\n' for row in lines))


def main(executable):
    evidence = json.loads((HERE/'certificates.json').read_text())
    bad_star, bad_pair = old_obstructions()
    patterns = set()
    for seed,data,expected in zip(SEEDS,evidence['families'],[(9865,6814),(30306,24198)]):
        all_profiles = enumerate_profiles(seed)
        remaining = {p for p in all_profiles if not earlier_result(tree(p)[0],bad_star,bad_pair)}
        assert (len(all_profiles),len(remaining)) == expected
        positive, negative = set(), set()
        for profile, codes in data['six_rectangles']:
            p = tuple(profile)
            _,rows,n = tree(p)
            assert p in remaining and len(codes)==len(rows) and all(0<=x<64 for x in codes)
            cols = [63]*n
            for i,row in enumerate(rows):
                for j in range(n):
                    if row>>j&1:
                        cols[j] &= ~codes[i]
            assert all(bool(row>>j&1) == (codes[i]&c==0)
                       for i,row in enumerate(rows) for j,c in enumerate(cols))
            positive.add(p)
        for profile, matching in data['forbidden_matchings']:
            p = tuple(profile)
            assert p in remaining
            _,rows,n = tree(p)
            patterns.add(matching_pattern(rows,n,matching))
            negative.add(p)
        yes, no = close(remaining,positive,-1), close(remaining,negative,1)
        assert yes|no == remaining
        print(f'{len(all_profiles):,} profiles, {len(remaining):,} after prior results: '
              f'{len(yes):,} covered by six rectangles, {len(no):,} excluded from the five hosts.',flush=True)
    for profile,k,row_codes,col_codes in evidence['host_controls']:
        _,rows,n = tree(profile)
        assert len(row_codes)==len(rows) and len(col_codes)==n and 0<=k<5
        assert all(0<=x<256 for x in row_codes+col_codes)
        assert all(bool(row>>j&1) != STAR['zero_cell'](STAR['HOSTS'][k],row_codes[i]&col_codes[j])
                   for i,row in enumerate(rows) for j in range(n))
    print(f'{len(evidence["host_controls"])} four-gate circuit controls. '
          f'{len(patterns)} distinct ordered matching patterns to check.',flush=True)
    verify_matching_patterns(sorted(patterns), executable)


if __name__=='__main__':
    if len(sys.argv)!=2 or not __debug__:
        raise SystemExit('Use python3 -I -B replay.py /path/to/matching-check with assertions enabled.')
    main(sys.argv[1])
