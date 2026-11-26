"""Exact finite checks for the four-symbol binary riffle identity. Standard library only."""
from itertools import combinations, combinations_with_replacement, product
from math import comb


def dot(x, y):
    return (x & y).bit_count() % 2


def surviving_dictionaries():
    # Order of the terms is immaterial. Zero and repeated first columns are allowed.
    masks = [tuple(dot(x, v) for v in range(16)) for x in range(1, 16)]
    tested = 0
    survivors = []
    for columns in combinations_with_replacement(range(16), 8):
        tested += 1
        if all(sum(row[v] for v in columns) >= 4 for row in masks):
            survivors.append(columns)
    assert tested == comb(23, 8)
    affine = {tuple(v for v in range(16) if dot(h, v)) for h in range(1, 16)}
    assert set(survivors) == affine
    return tested, survivors


def obstructed(columns, b):
    # At this target every four-term identity has both factor matrices invertible.
    # A pair occurring together in such an identity is independent on both sides.
    pairs = set()
    zero_planes = []
    for x in range(1, 16):
        support = tuple(i for i, v in enumerate(columns) if dot(x, v))
        if len(support) == 4:
            if dot(x, b):
                pairs.update(combinations(support, 2))
            else:
                zero_planes.append(support)
    return any(all(pair in pairs for pair in combinations(plane, 2)) for plane in zero_planes)


def binary_upper():
    # The two-symbol dictionary is (e0,e1,e0+e1). Each target has a singleton
    # recovery and a disjoint pair. Tensor two copies for the four-symbol model.
    columns = (1, 2, 3)
    recover = (((0,), (1, 2)), ((1,), (0, 2)))
    reads = tuple(product(range(3), repeat=2))
    entries = 0
    for a, b, c, d in product(range(4), repeat=4):
        total = 0
        for i, j in reads:
            first = dot(columns[i], 1 << (a // 2)) * dot(columns[j], 1 << (a % 2))
            left = i in recover[b // 2][c // 2] and j in recover[b % 2][c % 2]
            right = i in recover[b // 2][d // 2] and j in recover[b % 2][d % 2]
            total ^= first * left * right
        assert total == int(a == b and c == d)
        entries += 1
    return entries


def extension_targets(bits, polynomial):
    """Test the projective secant criterion on the normalized cube over GF(4) or GF(8)."""
    size = 1 << bits

    def multiply(a, b):
        value = 0
        while b:
            if b & 1:
                value ^= a
            a <<= 1
            if a >= size:
                a ^= polynomial
            b >>= 1
        return value

    scalars = range(1, size)
    inverse = {s: next(q for q in scalars if multiply(s, q) == 1) for s in scalars}

    def normalize(v):
        first = next((a for a in v if a), 0)
        return tuple(multiply(a, inverse[first]) for a in v) if first else (0,) * len(v)

    points = {normalize(v) for v in product(range(size), repeat=4) if any(v)}
    cube = {tuple((v >> i) & 1 for i in range(4)) for v in range(16) if v.bit_count() % 2}
    pairable = set()
    for b in points - cube:
        pivot = next(i for i in range(4) if b[i])
        counts = {}
        for v in cube:
            projected = normalize(tuple(x ^ multiply(v[pivot], y) for x, y in zip(v, b)))
            assert any(projected)
            counts[projected] = counts.get(projected, 0) + 1
        if all(count % 2 == 0 for count in counts.values()):
            pairable.add(b)
    even_binary = {tuple((v >> i) & 1 for i in range(4)) for v in range(1,16)
                   if v.bit_count() % 2 == 0}
    assert pairable == even_binary
    return len(points), len(pairable)


def main():
    tested, survivors = surviving_dictionaries()
    excluded = 0
    for columns in survivors:
        bad = {b for b in (1, 2, 4, 8) if obstructed(columns, b)}
        assert bad and bad == set(columns).intersection((1, 2, 4, 8))
        excluded += 1
    print(f"Width eight: {tested} unordered binary first-column dictionaries, zeros and repeats included.")
    print(f"Minimum-distance test: {len(survivors)} survivors. All {excluded} fail the zero-plane rank test.")
    print(f"Width nine: {binary_upper()} tensor entries verified over F2.")
    for bits, polynomial in ((2, 0b111), (3, 0b1011)):
        points, pairable = extension_targets(bits, polynomial)
        print(f"GF({1 << bits}) normalized cube: {points} projective targets, "
              f"{pairable} off-column targets pass the secant test.")


if __name__ == "__main__":
    main()
