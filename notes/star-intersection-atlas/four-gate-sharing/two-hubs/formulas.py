"""Explicit formulas for the two-branch family and checks on its lower bound."""
from itertools import combinations
from math import comb

FENCE = (7,23,22,30,28,29,25,27,11,43,42,46,44,45,37,53,49,51,50)


def subset(a, b):
    return (a & b) == a


def bistar_edges(n):
    # Labels p, q, x1, x2, y1, ...; the bipartite adjacency includes the diagonal.
    return [3 | sum(1 << i for i in range(4,n)), 2, 6, 10] + [1 << i for i in range(4,n)]


def check_family(t):
    h = t // 2
    middle = [v for v in range(1 << t) if v.bit_count() == h]
    w = (1 << (h-1)) - 1
    xs = [v for v in middle if not subset(w,v)][:2]
    ys = [v for v in middle if v not in xs]
    n = len(middle) + 2
    target = bistar_edges(n)
    top = (1 << t) - 1
    # First relation includes all middle-layer diagonals and p -> q.
    lower_1 = [w, top, *xs, *ys]
    upper_1 = [0, w, *xs, *ys]
    # Second relation is the union of two vertex-disjoint complete bipartite graphs.
    lower_2 = [1, 2, 2, 2] + [3] * len(ys)
    upper_2 = [1, 2, 0, 0] + [1] * len(ys)
    alpha, beta = 1 << t, 1 << (t+1)
    payloads = [v for v in middle if not subset(v,3)][:len(ys)]
    flat = [alpha, alpha|beta|3, beta|1, beta|2] + [alpha|v for v in payloads]
    assert len(flat) == n and len(xs) == 2 and len(ys) == comb(t,h)-2
    for i in range(n):
        for j in range(n):
            expected = bool(target[i] >> j & 1)
            assert expected == (subset(lower_1[i],upper_1[j]) or subset(lower_2[i],upper_2[j]))
            assert expected == subset(flat[i],flat[j])
    return n*n


def antichain_width(words):
    """Independent subset search on the small six-coordinate obstruction."""
    best = 0
    def extend(options, size):
        nonlocal best
        best = max(best,size)
        while size+len(options)>best:
            u = options[-1]
            options = options[:-1]
            extend([v for v in options if not subset(u,v) and not subset(v,u)], size+1)
    extend(words,0)
    return best


def verify():
    # Word 7 has three bits. The even positions are the minimal elements.
    for i,a in enumerate(FENCE):
        for j,b in enumerate(FENCE):
            assert subset(a,b) == (i==j or (i%2==0 and abs(i-j)==1))
    print('19-element fence: all 361 order cells checked.')
    # For the 12-element core with eight y vertices, p is a singleton by Sperner.
    # Permuting coordinates fixes p=1 and gives one q per rank.
    widths=[]
    for rank in range(2,6):
        q=(1<<rank)-1
        possible_x=[v for v in range(1,64) if not v&1 and subset(v,q)]
        best=0
        for x1,x2 in combinations(possible_x,2):
            if subset(x1,x2) or subset(x2,x1):
                continue
            possible_y=[v for v in range(64) if v&1 and not subset(v,q) and
                        not subset(q,v) and not subset(x1,v) and not subset(x2,v)]
            best=max(best,antichain_width(possible_y))
        widths.append(best)
    assert widths == [0,3,7,6]
    sizes = [check_family(t) for t in (4,5,6,8,10,12)]
    print(f'Family: {sum(sizes):,} cells checked in both constructions; six-coordinate width bounds {widths}.')
