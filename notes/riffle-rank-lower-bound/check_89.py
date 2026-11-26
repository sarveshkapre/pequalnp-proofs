"""Exact rational checks for the obstruction at width 89. Python standard library only."""
from collections import Counter
from fractions import Fraction
from itertools import combinations
from math import comb


def dependent(a, b, c):
    """Gram determinant of three real Boolean column vectors, evaluated in integers."""
    aa, bb, cc = (v.bit_count() for v in (a, b, c))
    ab, ac, bc = ((x & y).bit_count() for x, y in ((a, b), (a, c), (b, c)))
    return aa*bb*cc + 2*ab*ac*bc - aa*bc*bc - bb*ac*ac - cc*ab*ab == 0


def quotient_triangles():
    columns = range(1, 64)
    degrees = Counter()
    total = 0
    for a, b, c in combinations(columns, 3):
        # Numeric order places the disjoint union after both its constituents.
        is_triangle = dependent(a, b, c)
        assert is_triangle == (a & b == 0 and a | b == c)
        if is_triangle:
            total += 1
            degrees.update((a, b, c))
    assert total == 301
    assert Counter(degrees.values()) == {31: 7, 16: 21, 10: 35}
    for s in columns:
        t = s.bit_count()
        assert degrees[s] == 2**(t-1) + 2**(6-t) - 2
    return total, degrees


def one_contraction_control(degrees):
    # The dictionary (1, signs) has seven independent targets at width 64.
    vertices = [tuple([1] + [1 if (mask >> j) & 1 else -1 for j in range(6)])
                for mask in range(64)]
    for b in range(7):
        flip = (1 << (b-1)) if b else 63
        pairs = [(x, x ^ flip) for x in range(64) if x < x ^ flip]
        assert len(pairs) == 32 and len({x for pair in pairs for x in pair}) == 64
        for x, y in pairs:
            sign = 1 if b == 0 else -1
            result = tuple(a + sign*c for a, c in zip(vertices[x], vertices[y]))
            assert abs(result[b]) == 2 and sum(a != 0 for a in result) == 1
    flags = set()
    for x, v in enumerate(vertices):
        images = []
        for y, w in enumerate(vertices):
            if x == y:
                continue
            # Quotient by v using the first coordinate; common diagonal basis change.
            scaled = tuple((vi - wi) * vi for vi, wi in zip(v[1:], w[1:]))
            assert all(z in (0, 2) for z in scaled)
            mask = sum(1 << i for i, z in enumerate(scaled) if z)
            images.append(mask)
            if degrees[mask] == 31:
                flags.add((x,y))
        assert sorted(images) == list(range(1,64))
    assert len(flags) == 64*7 and all((y,x) in flags for x,y in flags)


def main():
    total, degrees = quotient_triangles()
    print(f"All {comb(63,3)} Boolean column triples checked by integer Gram determinant.")
    print(f"{total} dependent triples. Point degrees: {dict(sorted(Counter(degrees.values()).items()))}.")
    one_contraction_control(degrees)
    print("Positive control: 7 targets, 32 disjoint recoveries each; all 64 one-column quotients verified.")
    incidences = comb(65,2) * sum(v == 31 for v in degrees.values())
    assert incidences == 14560 and incidences % 3 == 1
    count = Fraction(comb(69,6)*total, comb(9,6))
    assert count == Fraction(1288682824,3)
    print(f"Pair contraction would give {incidences} flags, remainder {incidences % 3} modulo 3.")
    print(f"Six contractions would give {count} nine-element dependent sets.")


if __name__ == "__main__":
    main()
