"""Enumerate 13-element four-cube face antichains by number of nonvertices."""
from argparse import ArgumentParser
from itertools import combinations, permutations


def cube_actions():
    result = []
    for permutation in permutations(range(4)):
        permuted = [sum((x >> i & 1) << permutation[i] for i in range(4)) for x in range(16)]
        for translation in range(16):
            result.append(tuple(x ^ translation for x in permuted))
    return result


def image(mask, permutation):
    value = 0
    while mask:
        bit = mask & -mask
        value |= 1 << permutation[bit.bit_length() - 1]
        mask ^= bit
    return value


def faces():
    return sorted({sum(1 << x for x in range(16) if x & bits == v)
                   for bits in range(16) for v in range(16) if v & ~bits == 0})


def representatives(n):
    actions = cube_actions()
    nonpoints = [f for f in faces() if f.bit_count() > 1]
    seen_holes = set()
    for omitted in combinations(range(16), n+3):
        holes = sum(1 << x for x in omitted)
        if holes in seen_holes:
            continue
        stabilizer = []
        for a in actions:
            h = image(holes, a)
            seen_holes.add(h)
            if h == holes:
                stabilizer.append(a)
        options = [f for f in nonpoints if not f & ~holes]
        maps = [{f: image(f, a) for f in options} for a in stabilizer]
        singles = tuple(1 << x for x in range(16) if not (holes >> x & 1))
        for extra in combinations(options, n):
            if any((a & b) in (a, b) for a,b in combinations(extra, 2)):
                continue
            if any(tuple(sorted(m[f] for f in extra)) < extra for m in maps[1:]):
                continue
            yield singles + extra


if __name__ == "__main__":
    cli = ArgumentParser(description=__doc__)
    cli.add_argument("nonvertices", type=int, choices=range(14))
    args = cli.parse_args()
    for i, fam in enumerate(representatives(args.nonvertices)):
        print(i, *fam)
