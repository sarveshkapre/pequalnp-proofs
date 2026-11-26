"""Finite checks for two-reader compression and subdivided gate wiring. Python 3.10+."""
from functools import lru_cache
from itertools import combinations, product
from math import comb
from random import Random


def raw_tables(k):
    n = 1 << (2*k)
    all_cells = (1 << n) - 1
    atoms = [sum(1 << x for x in range(n) if x & (1 << j)) for j in range(2*k)]
    @lru_cache(maxsize=None)
    def absent(mask):
        value = all_cells
        for j, atom in enumerate(atoms):
            if mask & (1 << j):
                value &= all_cells ^ atom
        return value
    return atoms, all_cells, absent


def direct(arms, atoms):
    state = [0]*len(arms)
    while True:
        nxt = []
        for i, pair in enumerate(arms):
            masks = []
            for e, deps in enumerate(pair):
                value = atoms[2*i+e]
                for j in deps:
                    value |= state[j]
                masks.append(value)
            nxt.append(masks[0] & masks[1])
        if nxt == state:
            return state
        state = nxt


def readers(arms, center):
    return {i: {e for e in range(2) if center in arms[i][e]}
            for i in range(len(arms)) if any(center in d for d in arms[i])}


def block_union(arms, sites, start, signature, triple, absent):
    value = 0
    slots = 0
    for bits in product(range(2), repeat=len(sites)):
        choice = dict(zip(sites, bits))
        if triple:
            center, taps = triple
            if choice[center] and all(choice[j] not in sides for j, sides in taps.items()):
                continue
        slots += 1
        seen = set()
        stack = list(start)
        valid = True
        while stack and valid:
            i = stack.pop()
            if i in seen:
                continue
            seen.add(i)
            for j in arms[i][choice[i]]:
                if j in signature:
                    if signature[j] < 0:
                        valid = False
                else:
                    assert j in sites
                    stack.append(j)
        if valid:
            value |= absent(sum(1 << (2*i+choice[i]) for i in seen))
    if triple:
        assert slots <= 7*2**(len(sites)-3)
    return value


def compare(arms, outputs, separator, blocks, tables, state):
    atoms, all_cells, absent = tables
    trimmed = [[deps - outputs for deps in both] for both in arms]
    center = 0
    taps = readers(trimmed, center)
    protected = center not in outputs and set(taps) <= {1, 2} and all(len(s)==1 for s in taps.values())
    value = 0
    for codes in product((-1,0,1), repeat=len(separator)):
        sig = dict(zip(separator, codes))
        demanded = set(outputs)
        raw = 0
        for i,e in sig.items():
            if e >= 0:
                raw |= 1 << (2*i+e)
                demanded.update(trimmed[i][e])
        if any(i in demanded and e < 0 for i,e in sig.items()):
            continue
        local = absent(raw)
        for block in blocks:
            triple = (center, taps) if protected and center in block else None
            local &= block_union(trimmed, block, demanded.intersection(block), sig, triple, absent)
        value |= local
    actual = all_cells
    for i in outputs:
        actual &= all_cells ^ state[i]
    assert actual == value
    return protected


def finite_semantics():
    tables = raw_tables(3)
    count = 0
    for records in product(range(3),range(3),range(4),range(4),range(4),range(4)):
        arms = [[set(),set()] for _ in range(3)]
        for (j,i), enc in zip([(0,1),(0,2),(1,0),(2,0),(1,2),(2,1)], records):
            for e in range(2):
                if enc & (1<<e):
                    arms[i][e].add(j)
        values = direct(arms, tables[0])
        for o in range(8):
            outputs = {i for i in range(3) if o & (1<<i)}
            count += compare(arms, outputs, [], [[0,1,2]], tables, values)
    assert count == 2304*4
    rng = Random(731)
    tables = raw_tables(6)
    with_cut = 0
    for trial in range(32):
        arms = [[set(),set()] for _ in range(6)]
        for i in range(6):
            for j in range(6):
                if j==0:
                    enc = rng.randrange(3) if i in (1,2) else 0
                elif i==5 or j==5 or (i<3)==(j<3):
                    enc = rng.randrange(4)
                else:
                    enc = 0
                for e in range(2):
                    if enc & (1<<e):
                        arms[i][e].add(j)
        values = direct(arms,tables[0])
        for o in range(64):
            outputs = {i for i in range(6) if o & (1<<i)}
            with_cut += compare(arms,outputs,[5],[[0,1,2],[3,4]],tables,values)
    print(f"2,304 three-gate wirings, every output and all 64 raw inputs; {count} protected cases.")
    print(f"32 six-gate separator layouts, every output and all 4,096 raw inputs; {with_cut} protected cases.")


def components(adj, removed):
    remaining = set(range(len(adj))) - removed
    while remaining:
        start = remaining.pop()
        found = {start}
        stack = [start]
        while stack:
            for j in adj[stack.pop()] & remaining:
                remaining.remove(j)
                found.add(j)
                stack.append(j)
        yield found


def layout_trials():
    rng = Random(1847)
    # Subdivide every edge of the pentagonal prism.
    n = 10
    links = [(i, (i+1)%5) for i in range(5)]
    links += [(i+5,j+5) for i,j in links] + [(i,i+5) for i in range(5)]
    length = 49
    k = n + length*len(links)
    paths = [[u, *range(n+t*length,n+(t+1)*length), v] for t,(u,v) in enumerate(links)]
    checked = 0
    for trial in range(75):
        outputs = {i for i in range(k) if rng.random() < (trial%5)/8}
        adj = [set() for _ in range(k)]
        use = [set() for _ in range(k)]
        for path in paths:
            for i,j in zip(path,path[1:]):
                mode = rng.choice((1,2,3)) if trial%3 else 1
                for flag,src,dst in ((1,i,j),(2,j,i)):
                    if mode & flag and src not in outputs:
                        use[src].add(dst)
                        adj[src].add(dst)
                        adj[dst].add(src)
        cuts,centers,triples = set(),set(),set()
        intact = 0
        for path in paths:
            if not all(j in adj[i] for i,j in zip(path,path[1:])):
                continue
            intact += 1
            cuts.add(path[-2])
            for t in range(12):
                group = path[1+4*t:5+4*t]
                u = next(x for x in group[1:3] if x not in outputs)
                triple = {u,group[group.index(u)-1],group[group.index(u)+1]}
                assert use[u] <= triple - {u} and not triple & triples
                centers.add(u)
                triples.update(triple)
        assert not cuts & triples and len(centers)==12*intact
        order = []
        for cc in components(adj,cuts):
            hubs = [v for v in cc if v<n]
            assert len(hubs)<=1
            if hubs:
                hub=hubs[0]
                order.append(hub)
                for j in sorted(adj[hub] & cc):
                    prev,cur=hub,j
                    while True:
                        order.append(cur)
                        ahead=(adj[cur]&cc)-{prev}
                        if not ahead:
                            break
                        assert len(ahead)==1
                        prev,cur=cur,ahead.pop()
            else:
                cur=next(j for j in cc if len(adj[j]&cc)<=1)
                prev=None
                while True:
                    order.append(cur)
                    ahead=(adj[cur]&cc)-{prev}
                    if not ahead:
                        break
                    prev,cur=cur,ahead.pop()
        assert len(set(order))==len(order)==k-len(cuts)
        # Integer weights in sixteenths; three units saved at each center.
        weight = {v:16-3*(v in centers) for v in order}
        total=sum(weight.values())
        subtotal=0
        left=set()
        for v in order:
            left.add(v)
            subtotal+=weight[v]
            if 2*subtotal>=total:
                break
        right=set(order)-left
        frontier={v for v in left if adj[v]&right}
        assert len(frontier)<=2 and not any(adj[v]&right for v in left-frontier)
        assert max(subtotal,total-subtotal)*2 <= total+32
        checked+=intact
    print(f"75 layouts on {k} gates: {checked} intact paths; disjoint triples, residual components, weighted cuts and frontier passed.")


def mixed_component_packing():
    # Plant connected groups of bad base edges; uncut links on a bad path
    # may use both arms. Their components must be placed whole.
    n, length = 200, 49
    half = n//2
    edges = [(i, (i+1)%half) for i in range(half)]
    edges += [(a+half,b+half) for a,b in edges] + [(i,i+half) for i in range(half)]
    k = n+length*len(edges)
    unit_cap = 16*(1+3*length)
    large_seen = 0
    for phase in range(4):
        adj = [set() for _ in range(k)]
        centers = set()
        cuts = set()
        isolated_base = set(range(n))
        for t,(u,v) in enumerate(edges):
            path = [u,*range(n+t*length,n+(t+1)*length),v]
            bad = t < 17 or (t+phase)%23==0
            if bad:
                isolated_base.difference_update((u,v))
            broken = (t+phase)%19==0
            for j,(a,b) in enumerate(zip(path,path[1:])):
                if not (broken and j==25):
                    adj[a].add(b)
                    adj[b].add(a)
            if not bad and not broken:
                cuts.add(path[-2])
                centers.update(path[2+4*i] for i in range(12))
        weights = []
        for cc in components(adj,cuts):
            if cc & isolated_base:
                assert len(cc & set(range(n)))==1 and len(cc)<=1+3*length
            weights.append(16*len(cc)-3*len(cc & centers))
        assert len(isolated_base)>=n//2 and len(centers)==12*len(cuts)
        total=sum(weights)
        assert total==16*(k-len(cuts))-3*len(centers)
        big=[w for w in weights if w>unit_cap]
        small=[w for w in weights if w<=unit_cap]
        assert big and sum(small)>2*max(big)
        loads=[0,0]
        for w in big:
            at=loads.index(min(loads))
            assert 2*(loads[at]+w)<=total
            loads[at]+=w
        for w in small:
            loads[loads.index(min(loads))]+=w
        assert sum(loads)==total and 2*max(loads)<=total+2*unit_cap
        large_seen+=len(big)
    print(f"Four mixed layouts on {k:,} gates: {large_seen} large pieces packed whole; isolated-core and weight bounds passed.")


def double_arm_relay():
    # On a cycle keep a double-arm tree path to the final gate, and the
    # remaining cycle link on one arm. Only the final gate is designated.
    k = 7
    arms = [[set(),set()] for _ in range(k)]
    for i in range(1,k):
        for side in range(2):
            arms[i][side].add(i-1)
    arms[-1][0].add(0)
    for x,y in product(range(1<<k), repeat=2):
        raw = []
        for i in range(k):
            a,b = (x>>i)&1,(y>>i)&1
            raw.extend((int(not a or not b), a|b))
        assert direct(arms, raw)[-1] == (x!=y)
    assert not any(k-1 in d for pair in arms for d in pair)
    print("One-output double-arm relay on a seven-cycle: all 16,384 label pairs give inequality.")


def thresholds():
    assert charge_is_covered(12,2) and not charge_is_covered(11,2)
    # In a cubic base with a 1/2 chance of a single-arm guarantee per link,
    # 152 disjoint four-vertex groups suffice for the mixed-wiring bound.
    assert 24*sum(comb(152,i)*7**(152-i) for i in range(12)) < 8**152
    print("Exact depth-two charge and mixed-wiring binomial tail passed.")


def charge_is_covered(groups, bins):
    return 2**(16+3*groups) >= 3**(16*bins)


if __name__ == '__main__':
    thresholds()
    finite_semantics()
    layout_trials()
    mixed_component_packing()
    double_arm_relay()
