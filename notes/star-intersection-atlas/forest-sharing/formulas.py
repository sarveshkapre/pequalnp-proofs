"""Exact rectangle-profile embedding test, with arc consistency and search."""
from functools import lru_cache


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask -= bit


def zero(shape, x):
    if shape == 0:
        return bool(x & 15)
    if shape == 1:
        return bool(x & 7) and bool(x & 24)
    if shape == 2:
        return bool(x & 3) and bool(x & 12) and bool(x & 48)
    if shape == 3:
        return bool(x & 1) or (bool(x & 6) and bool(x & 24))
    raise ValueError(shape)


def shape_profiles(shape):
    n = 1 << (4, 5, 6, 5)[shape]
    reps = {}
    for i in range(n):
        reps.setdefault(tuple(zero(shape, i & j) for j in range(n)), i)
    types = list(reps.values())
    rights = [sum(1 << j for j, c in enumerate(types) if zero(shape, r & c)) for r in types]
    return types, rights


def fit(rows, ncols, shape):
    types, rights = shape_profiles(shape)
    all_types = (1 << len(types)) - 1
    n = len(rows)
    cols = [sum(1 << i for i, row in enumerate(rows) if row & (1 << j)) for j in range(ncols)]
    visits = 0

    @lru_cache(maxsize=4096)
    def support(domain, edge):
        supported = 0
        for k in bits(domain):
            supported |= (all_types ^ rights[k]) if edge else rights[k]
        return supported

    def assign(domains, queue):
        nonlocal visits
        visits += 1
        while queue:
            v = queue.pop()
            if v < n:
                start, length, neighbors = n, ncols, rows[v]
            else:
                start, length, neighbors = 0, n, cols[v-n]
            choices = (support(domains[v], 0), support(domains[v], 1))
            for offset in range(length):
                i = start + offset
                remaining = domains[i] & choices[(neighbors >> offset) & 1]
                if not remaining:
                    return None
                if remaining != domains[i]:
                    domains[i] = remaining
                    queue.add(i)
        undecided = [i for i, domain in enumerate(domains) if domain & (domain-1)]
        if not undecided:
            return [types[d.bit_length()-1] for d in domains]
        v = min(undecided, key=lambda i: domains[i].bit_count())
        for k in bits(domains[v]):
            new = domains.copy()
            new[v] = 1 << k
            witness = assign(new, {v})
            if witness is not None:
                return witness
        return None

    return assign([all_types] * (n + ncols), set(range(n + ncols))), visits
