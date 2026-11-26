"""Exhaustive semantics and path-geometry controls for the relay subdivision theorem."""
from functools import cache
from itertools import product
from random import Random


@cache
def raw_inputs(n):
    assignments = 1 << (2*n)
    full = (1 << assignments) - 1
    # Packed truth table of each independent raw input, alternating runs of size 2^j.
    raw = []
    for j in range(2*n):
        width = 1 << j
        pattern = ((1 << width) - 1) << width
        raw.append(pattern * (full // ((1 << (2*width)) - 1)))
    return raw, full


def vertices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length()-1
        mask ^= bit


def direct(arms):
    raw, full = raw_inputs(len(arms))
    pos = [0] * len(arms)
    for _ in range(len(arms)+1):
        nxt = []
        for i, pair in enumerate(arms):
            left, right = raw[2*i:2*i+2]
            for j in vertices(pair[0]):
                left |= pos[j]
            for j in vertices(pair[1]):
                right |= pos[j]
            nxt.append(left & right)
        if pos == nxt:
            return [full ^ x for x in pos]
        pos = nxt
    raise AssertionError("finite monotone iteration exceeded the gate count")


def rejection(values, roots):
    _, result = raw_inputs(len(values))
    for i in vertices(roots):
        result &= values[i]
    return result


def certificate_tables(arms, regions=()):
    n = len(arms)
    raw, full = raw_inputs(n)
    tables = []
    for choice in range(1 << n):
        if any((choice >> center) & 1 and all(((choice >> r) & 1) == bypass
               for r, bypass in readers) for center, readers in regions):
            continue
        adj = [pair[(choice >> i) & 1] for i, pair in enumerate(arms)]
        for mid in range(n):
            for i in range(n):
                if adj[i] & (1 << mid):
                    adj[i] |= adj[mid]
        for i in range(n):
            adj[i] |= 1 << i
        @cache
        def eligible(mask, word=choice):
            result = full
            for i in vertices(mask):
                result &= full ^ raw[2*i+((word >> i) & 1)]
            return result
        tables.append((adj,eligible))
    return tables


def joined(tables, roots, banned=0):
    result = 0
    if roots & banned:
        return result
    for reach, eligible in tables:
        active = roots
        for i in vertices(roots):
            active |= reach[i]
        if not active & banned:
            result |= eligible(active)
    return result


def runs(arms):
    n = len(arms)
    found = []
    for i in range(n):
        for step in (-1,1):
            path = [i]
            j = i+step
            while 0 <= j < n and arms[j][0] & arms[j][1] & (1 << path[-1]):
                path.append(j)
                j += step
            if len(path) > 1:
                found.append(path)
    return found


def clamp(arms, roots):
    return [(left & ~roots,right & ~roots) for left,right in arms]


def cut_controls():
    samples = tests = deep = 0
    for wires in product(range(4), repeat=6):
        arms = [[0,0] for _ in range(4)]
        for j in range(3):
            for pred, reader, value in ((j,j+1,wires[2*j]),(j+1,j,wires[2*j+1])):
                for e in range(2):
                    if value & (1 << e):
                        arms[reader][e] |= 1 << pred
        paths = runs(arms)
        if not paths:
            continue
        path = max(paths,key=len)
        pair = (1 << path[0]) | (1 << path[1])
        removed = sum(1 << i for i in path[1:])
        live = certificate_tables(clamp(arms,pair))
        inactive = certificate_tables(arms)
        values = direct(arms)
        for root in range(16):
            union = joined(live,root | pair) | joined(inactive,root,removed)
            assert union == rejection(values,root)
            tests += 1
        samples += 1
        deep += len(path) == 4
    assert samples == 4**6-3**6 and deep
    print(f"Relay split: {samples} of 4,096 four-gate path layouts have a double read; "
          f"{tests} output selections, all 256 raw settings, {deep} full-length runs.")


def region_controls():
    rng = Random(22619729)
    count = 0
    for trial in range(16):
        arms = [[0,0] for _ in range(8)]
        codes = []
        for start in (0,4):
            l, c, interior, r = range(start,start+4)
            for pred,reader in ((c,interior),(interior,c),(l,c),(r,interior)):
                value = 3 if (pred,reader)==(c,interior) else rng.randrange(4)
                for e in range(2):
                    if value & (1<<e):
                        arms[reader][e] |= 1<<pred
            exits = []
            for pred,reader in ((c,l),(interior,r)):
                arm = rng.randrange(2)
                arms[reader][arm] |= 1<<pred
                exits.append((reader,1-arm))
            codes.append((c,exits))
        ports = (0,3,4,7)
        for pred,reader in product(ports,repeat=2):
            for e in range(2):
                if rng.randrange(2):
                    arms[reader][e] |= 1<<pred
        table = certificate_tables(arms,codes)
        assert len(table) == 4*7**2
        truth = direct(arms)
        for mask in range(16):
            roots = sum(1<<ports[j] for j in vertices(mask))
            assert joined(table,roots)==rejection(truth,roots)
            count += 1
    print(f"Two disjoint two-vertex regions: {count} output/layout cases, 65,536 raw "
          "settings per case, exactly 196 retained codes per layout.")


def path_windows():
    windows = seed_cases = 0
    for t in (1,2,3):
        n = 2*t+2
        independent_seeds = [s for s in range(1<<n) if not s & (s<<1)]
        for flags in product(range(4),repeat=n-1):
            if any(all(flags[i+j]&d for j in range(t)) for i in range(n-t) for d in (1,2)):
                continue
            reaches = []
            for c in (t,t+1):
                lo = hi = c
                while lo and flags[lo-1]&2:
                    lo -= 1
                while hi<n-1 and flags[hi]&1:
                    hi += 1
                assert 0<lo<=c<=hi<n-1
                assert not flags[lo-1]&2 and not flags[hi]&1
                reaches.append(sum(1<<i for i in range(lo,hi+1)))
            for seed in independent_seeds:
                if any(((d&1 and seed & (1<<(i+1)) and not seed & (1<<i)) or
                        (d&2 and seed & (1<<i) and not seed & (1<<(i+1))))
                       for i,d in enumerate(flags)):
                    continue
                assert any(not seed & reach for reach in reaches)
                seed_cases += 1
            windows += 1
    assert windows and seed_cases
    print(f"Path dichotomy: all mandatory-direction patterns through eight vertices, "
          f"{windows} windows without a long run, {seed_cases} compatible seed patterns.")


def bank_controls():
    for n,g in ((2,2),(2,3),(3,2)):
        words = list(product(range(n),repeat=g))
        rectangles = obligations = 0
        required = {}
        for pattern in product(range(-1,n),repeat=g):
            left = tuple(max(x,0) for x in pattern)
            right = tuple(1 if x<0 else x for x in pattern)
            required[pattern] = (words.index(left),words.index(right))
        witnessed = set()
        # An arbitrary nonempty row or column projection fixes these coordinates.
        fixed = {}
        for mask in range(1,1<<len(words)):
            selected = [words[j] for j in vertices(mask)]
            fixed[mask] = tuple(x if all(w[i]==x for w in selected) else -1
                                for i,x in enumerate(selected[0]))
        for rows,rv in fixed.items():
            for cols,cv in fixed.items():
                rectangles += 1
                label = tuple(x if x==y else -1 for x,y in zip(rv,cv))
                l,r = required[label]
                if (rows>>l)&1 and (cols>>r)&1:
                    witnessed.add(label)
        for indices in product((False,True),repeat=g):
            for left,right in product(words,repeat=2):
                eligible = [p for p in required if tuple(v>=0 for v in p)==indices]
                covered = any(all(v<0 or v==x==y for v,x,y in zip(p,left,right))
                              for p in eligible)
                assert covered == all(not selected or x==y for selected,x,y in zip(indices,left,right))
            obligations += 1
        assert witnessed == set(required) and len(witnessed) == (n+1)**g
        print(f"Bank N={n}, g={g}: {rectangles} nonempty rectangles, "
              f"{obligations} requests, minimum {len(witnessed)}.")


def simultaneous_cuts():
    # Two internally disjoint paths per hub pair are unnecessary. Use the complete
    # bipartite graph K3,3 to force reconnections unless all nine corridors are cut.
    base_edges = [(i,j) for i in range(3) for j in range(3,6)]
    rng = Random(1972923239)
    trials = patterns = long_paths = region_paths = 0
    for _ in range(12):
        a,t = 2,3
        support = {i:set() for i in range(6)}
        singles = []
        doubles = []
        fresh = 6
        for e,(u,v) in enumerate(base_edges):
            length = a*(2*t+2)+1+rng.randrange(5)
            interior = list(range(fresh,fresh+length))
            fresh += length
            path = [u]+interior+[v]
            for x,y in zip(path,path[1:]):
                support.setdefault(x,set()).add(y)
                support.setdefault(y,set()).add(x)
            if e%3==0:
                # These windows have no mandatory reads. The middle singleton and
                # both neighboring readers make one protected region per window.
                singles.append((interior[-1],
                    [set(interior[i*(2*t+2)+t-1:i*(2*t+2)+t+2]) for i in range(a)]))
            else:
                run = interior[:t+1]
                doubles.append(run if rng.randrange(2) else run[::-1])
        for decisions in product((False,True),repeat=len(doubles)):
            removed = {x for x,_ in singles}
            broken = set()
            for live,run in zip(decisions,doubles):
                if live:
                    broken.add(frozenset(run[:2]))
                else:
                    removed.update(run[1:])
            assert len(removed)==len(singles)+t*(len(doubles)-sum(decisions))
            remain = set(support)-removed
            while remain:
                stack = [next(iter(remain))]
                seen = set()
                while stack:
                    x=stack.pop()
                    if x in seen:
                        continue
                    seen.add(x)
                    stack.extend(y for y in support[x] if y not in removed and
                                 frozenset((x,y)) not in broken)
                assert len(seen.intersection(range(6)))<=1
                for _,groups in singles:
                    assert all(not seen.intersection(group) or group <= seen for group in groups)
                remain.difference_update(seen)
            patterns += 1
        long_paths += len(doubles)
        region_paths += len(singles)
        trials += 1
    print(f"Global cuts: {trials} subdivided K3,3 layouts, {region_paths} region paths, "
          f"{long_paths} mandatory paths, all {patterns} binary branch patterns.")


def chain_controls():
    n = 4
    arrows = [(i,j) for i in range(n) for j in range(n) if i!=j]
    subsets = range(1<<n)
    partitions = [()]
    for i in range(n):
        partitions = [out for p in partitions for out in
                      [p+(1<<i,)] + [p[:j]+(p[j] | (1<<i),)+p[j+1:] for j in range(len(p))]]
    width_counts = [0]*(n+1)
    for graph in range(1<<len(arrows)):
        reach = [1<<i for i in range(n)]
        for bit in vertices(graph):
            a,b = arrows[bit]
            reach[a] |= 1<<b
        for mid in range(n):
            for i in range(n):
                if reach[i] & (1<<mid):
                    reach[i] |= reach[mid]
        comp = {(i,j) for i,j in product(range(n),repeat=2)
                if reach[i] & (1<<j) or reach[j] & (1<<i)}
        chains = {s for s in subsets if all((i,j) in comp for i,j in product(vertices(s),repeat=2))}
        cover = min((p for p in partitions if all(c in chains for c in p)), key=len)
        width = max(s.bit_count() for s in subsets if all(
                    i==j or (i,j) not in comp for i,j in product(vertices(s),repeat=2)))
        assert len(cover)==width
        final = [s for s in subsets if all(not reach[i] & ~s for i in vertices(s))]
        # Scale the geometric weights by 2^n and use integer arithmetic.
        mass = sum(1<<(n-s.bit_count()) for s in final)
        bound = 1
        for c in cover:
            bound *= (1<<(c.bit_count()+1))-1
        assert mass <= bound
        width_counts[width] += 1
    assert sum(width_counts)==4096
    print(f"Mandatory reachability: all 4,096 four-pivot directed graphs; "
          f"chain and antichain bounds agree; width counts {width_counts[1:]}.")


def weighted_traces():
    # Multiply all weights by 2*3*5*7 so every comparison is integral.
    denominators = (2,3,5,7)
    size = 1<<len(denominators)
    weights = []
    projections = []
    for subset in range(size):
        weight = 1
        for i,q in enumerate(denominators):
            if not subset & (1<<i):
                weight *= q
        weights.append(weight)
        fibers = {}
        for word in range(size):
            pattern = word & subset
            fibers[pattern] = fibers.get(pattern,0) | (1<<word)
        projections.append(list(fibers.values()))
    limits = [sum(w for s,w in enumerate(weights) if s.bit_count()<=v)
              for v in range(len(denominators)+1)]
    mass = [0]*(1<<size)
    equality = set()
    for family in range(1,1<<size):
        lowest = family & -family
        mass[family] = mass[family ^ lowest]+weights[lowest.bit_length()-1]
        dim = max(s.bit_count() for s in range(size)
                  if all(family & part for part in projections[s]))
        assert mass[family]<=limits[dim]
        if mass[family]==limits[dim]:
            equality.add(dim)
    assert equality==set(range(5))
    print("Signal patterns: all 65,535 nonempty four-pivot families satisfy the "
          "weighted shattering bound, with equality at all five dimensions.")


if __name__ == "__main__":
    cut_controls()
    region_controls()
    path_windows()
    simultaneous_cuts()
    bank_controls()
    chain_controls()
    weighted_traces()
