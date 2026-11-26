"""Exact endpoint certificate and small-grid replay of the two-layer construction."""
from fractions import Fraction as F
from itertools import product
from math import lcm
from random import Random


def certificate():
    checks = 0
    rho = F(1,10)
    for lo, hi, p, q, tau in [(F(9,20),F(4,5),5,9,F(49,50)),
                                (F(4,5),F(1),3,5,F(1))]:
        lam, z = F(p,q), tau**p
        for x in (lo,hi):
            common = [(z,-(x-rho)),(x,-lam*x),(x-rho,lam*(x-rho)),
                      (rho,lam*rho),(F(2),-F(27,20))]
            for branch in [[(1+2*z,F(1))],[(F(2),F(1)),(1+tau**q,lam)]]:
                factors = common+branch
                scale = lcm(*(coefficient.denominator for _,coefficient in factors))
                ratio = F(1)
                for base,coefficient in factors:
                    ratio *= base**int(scale*coefficient)
                assert ratio < 1
                checks += 1
    print(f'{checks} rational endpoint comparisons passed with exact integer powers')


def vertices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length()-1
        mask ^= bit


def test(gates, output, out_raw, raw, cut, allowance, side):
    k = len(gates)
    all_cells = (1<<(side*side))-1

    def rectangle(exclusions):
        rows, cols = exclusions
        return sum(1<<(i*side+j) for i in range(side) if not rows>>i&1
                   for j in range(side) if not cols>>j&1)

    # Forward circuit evaluation, independently of every backward-choice rule.
    truth = []
    for i,arms in enumerate(gates):
        signals = []
        for e,refs in enumerate(arms):
            hit = all_cells ^ rectangle(raw[i][e])
            for j in vertices(refs):
                hit |= truth[j]
            signals.append(hit)
        truth.append(signals[0] & signals[1])
    expect = rectangle(out_raw)
    for i in vertices(output):
        expect &= ~truth[i]

    used = 0
    for i,(left,right) in enumerate(gates[:cut]):
        candidates = (left|right)&~used
        if candidates:
            used |= (1<<i) | (candidates&-candidates)
    early = (1<<cut)-1
    isolated = early ^ used
    pairs = list(vertices(used))
    # Cache the list of eligible separator signatures by requested active nodes.
    # Each entry stores all raw exclusions, the requested independent nodes, and
    # the signature's active vertices. It is independent of the suffix.
    signatures = []
    for vector in product((-1,0,1),repeat=len(pairs)):
        active = 0
        needed = 0
        rows = cols = 0
        for j,e in zip(pairs,vector):
            if e < 0:
                continue
            active |= 1<<j
            needed |= gates[j][e]
            r,c = raw[j][e]
            rows |= r
            cols |= c
        if not (needed & used & ~active):
            signatures.append((active,needed&isolated,rows,cols))

    cache = {}
    def bank_entry(sig,domain):
        key = (sig,domain)
        if key in cache:
            return cache[key]
        active,_,r0,c0 = sig
        names = list(vertices(domain))
        answer = 0
        for bits in range(1<<len(names)):
            rows,cols = r0,c0
            for pos,j in enumerate(names):
                e = (bits>>pos)&1
                if gates[j][e] & ~active:
                    break
                r,c = raw[j][e]
                rows |= r
                cols |= c
            else:
                answer |= rectangle((rows,cols))
        cache[key] = answer
        return answer

    result = 0
    for bits in range(1<<(k-cut)):
        needs = output
        rr,cc = out_raw
        for i in range(k-1,cut-1,-1):
            if needs>>i&1:
                e = (bits>>(i-cut))&1
                needs |= gates[i][e]
                r,c = raw[i][e]
                rr |= r
                cc |= c
        demand = needs & isolated
        labels = list(vertices(demand))
        # A deterministic test cover. The semantic argument permits ANY retained
        # subset within the omission budget, including the two extreme choices.
        omitted = sum(1<<j for j in labels[::2][:allowance])
        kept = demand ^ omitted
        omit_names = list(vertices(omitted))
        for eword in range(1<<len(omit_names)):
            required = needs & used
            rows,cols = rr,cc
            for pos,j in enumerate(omit_names):
                e = (eword>>pos)&1
                required |= gates[j][e]
                r,c = raw[j][e]
                rows |= r
                cols |= c
            lhs = 0
            for sig in signatures:
                if not (required & ~sig[0]):
                    lhs |= bank_entry(sig, kept | sig[1])
            result |= lhs & rectangle((rows,cols))
    assert result == expect, (gates,output,cut,allowance)


def controls():
    trials = 0
    k = 3
    side = 1<<(2*k)
    masks = [sum(1<<i for i in range(side) if i>>j&1) for j in range(2*k)]
    raw = [[(masks[2*i+e],masks[2*i+e]) for e in (0,1)] for i in range(k)]
    for shape in product(*(range(1<<i) for i in range(k) for _ in range(2))):
        gates = [shape[2*i:2*i+2] for i in range(k)]
        for output in range(1<<k):
            for b in range(k+1):
                test(gates,output,(0,0),raw,b,1,side)
                trials += 1
    print(f'{trials} exhaustive DAG, output and cut combinations on the full 64 by 64 raw grid')
    rng = Random(270350)
    for trial in range(2400):
        k = rng.randrange(10)
        side = 5
        gates = [tuple(sum(1<<j for j in range(i) if rng.randrange(4)==0) for _ in range(2))
                 for i in range(k)]
        def raw_mask():
            return 0 if rng.randrange(3) else rng.getrandbits(side)
        raw = [[(raw_mask(),raw_mask()) for _ in range(2)] for _ in range(k)]
        test(gates,rng.getrandbits(k),(raw_mask(),raw_mask()),raw,rng.randrange(k+1),trial%5,side)
    print('2400 larger random sources, including repeated and unused wires, passed forward evaluation')


def verify_projection_counts():
    from math import comb
    cases = 0
    for n in range(1,6):
        for t in range(n+1):
            layer = [b for b in range(1<<n) if b.bit_count()==t]
            total = 1<<len(layer)
            for mandatory in range(1<<n):
                d = mandatory.bit_count()
                sums = [0]*(n+1)
                for family in range(total):
                    projections = {layer[i] & ~mandatory for i in vertices(family)}
                    for j in projections:
                        sums[j.bit_count()] += 1
                for j in range(n-d+1):
                    ways = comb(d,t-j) if 0 <= t-j <= d else 0
                    expected = comb(n-d,j) * (total - total//(1<<ways))
                    assert sums[j] == expected
                    cases += 1
    print(f'{cases} exact projection expectations over all constant-size-layer subfamilies through five coordinates')


if __name__ == '__main__':
    certificate()
    verify_projection_counts()
    controls()
