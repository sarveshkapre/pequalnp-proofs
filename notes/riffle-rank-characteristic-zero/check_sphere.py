"""Expand every entry of three sphere decompositions over the rationals."""
from collections import defaultdict
from fractions import Fraction
from functools import cache
from itertools import product
from math import prod


def largest_layer(vectors, score):
    by_score = defaultdict(list)
    for v in vectors:
        by_score[score(v)].append(v)
    return max(by_score.values(), key=len)


@cache
def interpolation_coefficients(size, node):
    coefficients = [Fraction(1)]
    for j in range(size):
        if j == node:
            continue
        old = coefficients
        coefficients = [Fraction(0)] * (len(old) + 1)
        for k, value in enumerate(old):
            coefficients[k] -= j * value / (node - j)
            coefficients[k + 1] += value / (node - j)
    return coefficients


def sphere_construction(s, dimension, n):
    cube = list(product(range(s), repeat=dimension))
    symbols = largest_layer(cube, lambda a: sum(z*z for z in a))[:n]
    assert len(symbols) == n
    side = 2*s - 1
    samples = list(product(range(side), repeat=dimension))

    @cache
    def monomial(a):
        return [prod(z**k for z, k in zip(node, a)) for node in samples]

    @cache
    def decoder(exponents):
        return [prod(interpolation_coefficients(side, z)[k]
                     for z, k in zip(node, exponents)) for node in samples]

    for b in symbols:
        tails = largest_layer(cube, lambda u: sum(x*y for x, y in zip(b, u)))[:n]
        assert len(tails) == n
        for a, t, u in product(symbols, tails, tails):
            target = tuple(x+y for x, y in zip(b, u))
            value = sum(x*y*w for x, y, w in zip(monomial(a), monomial(t), decoder(target)))
            assert value == int(a == b and t == u)
    return len(samples), n**4


if __name__ == "__main__":
    for s, d, n in [(2, 3, 3), (2, 4, 6), (3, 2, 2)]:
        width, entries = sphere_construction(s, d, n)
        print(f"Sphere s={s}, d={d}, n={n}: {width} terms, {entries} actual rational sums agree")
