"""Check the block inequalities and an irredundant six-target dictionary."""
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
from math import comb


# Candidate width, followed by the numerator and denominator of the cap slope.
STEPS = ((8, 65, 9, 10), (11, 69, 7, 8),
         (14, 73, 5, 6), (17, 77, 4, 5))


def best_partition(width, min_blocks, cap):
    """Independent exact optimization over sorted nonempty block sizes."""
    @lru_cache(None)
    def fill(budget, smallest, count):
        if count == 0:
            return 0
        if budget < count * smallest:
            return None
        choices = []
        for size in range(smallest, budget // count + 1):
            rest = fill(budget - size, size, count - 1)
            if rest is not None:
                choices.append(cap[size] + rest)
        return max(choices, default=None)

    scores = []
    for count in range(min_blocks, 2 * width // 5 + 1):
        for first in range(1, width // count + 1):
            rest = fill(width - first, max(first, 5 - first), count - 1)
            if rest is not None:
                scores.append(cap[first] + rest)
    return max(scores)


def check_steps():
    lower = [0, 32, 48, 56, 60, 62, 63, 64]
    for k, r, numerator, denominator in STEPS:
        while len(lower) < k:
            lower.append(lower[-1] + 1)
        assert len(lower) == k and lower[k-3] == r-3
        q = 64 - (r - k + 1)
        largest = r - 3 * (q - 1) + 1
        cap = {}
        for size in range(1, r + 1):
            feasible = [t for t in range(min(4, size), min(k, size) + 1)
                        if lower[k - t] <= r - size]
            # Only necessary conditions are used. An impossible size can be
            # omitted; in these four rows a rank is feasible for every size.
            assert feasible
            cap[size] = size - min(feasible) + 2
        peak = max(Fraction(cap[m], m) for m in range(3, largest + 1))
        assert cap[1] == cap[2] == 2 and peak <= Fraction(numerator, denominator)
        scaled = numerator * (r - 1) + 2 * denominator
        assert scaled < 64 * denominator
        opt = best_partition(r, q, cap)
        assert opt < 64
        print(f"k={k}: width {r} excluded; q>={q}, max block {largest}, "
              f"max ratio {peak}, exact partition cap {opt}/64.")
        lower.append(r + 1)
    assert lower[17] + 32 - 17 == 93
    print("At 32 targets, at least 93 columns are required.")


def check_translated_cube():
    shift = (2, 4, 8, 16, 32, 64)
    columns = [tuple((1 if mask & (1 << j) else -1) - t
                     for j, t in enumerate(shift)) for mask in range(64)]
    assert all(all(v) for v in columns)
    for target in range(6):
        bit = 1 << target
        pairs = [(mask, mask ^ bit) for mask in range(64) if mask & bit]
        assert len(pairs) == 32 and len({i for pair in pairs for i in pair}) == 64
        for a, b in pairs:
            diff = tuple(x-y for x, y in zip(columns[a], columns[b]))
            assert diff == tuple(2 * (i == target) for i in range(6))
    gram = [[sum(x*y for x, y in zip(a, b)) for b in columns] for a in columns]
    for a, b, c in combinations(range(64), 3):
        A, B, C = gram[a][a], gram[b][b], gram[c][c]
        u, v, w = gram[a][b], gram[a][c], gram[b][c]
        assert A*B*C + 2*u*v*w - A*w*w - B*v*v - C*u*u > 0
    print(f"Translated cube: 6 exact 32-pair decoders, 0 target-line columns, "
          f"all {comb(64, 3)} triples independent over the rationals.")


if __name__ == "__main__":
    check_translated_cube()
    check_steps()
