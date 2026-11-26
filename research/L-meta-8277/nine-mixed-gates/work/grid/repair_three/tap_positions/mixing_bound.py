"""Check the five-mixed-gate obstruction on all physical row triples."""
from collections import Counter
from functools import cache
from itertools import combinations, permutations, product

from split import project


INPUTS = tuple(sum(1 << word for word in range(64) if word & (1 << bit))
               for bit in range(6))


@cache
def mixed_trees(leaves):
    """All truth tables of binary trees with each leaf once and every gate mixed."""
    if leaves.bit_count() == 1:
        return {INPUTS[leaves.bit_length() - 1]}
    if not (leaves & 7 and leaves & 56):
        return set()
    tables = set()
    left = (leaves - 1) & leaves
    while left:
        right = leaves ^ left
        if left < right:  # AND and OR are commutative.
            for a, b in product(mixed_trees(left), mixed_trees(right)):
                tables.update((a & b, a | b))
        left = (left - 1) & leaves
    return tables


def antichains(width):
    return [triple for triple in combinations(range(1 << width), 3)
            if all((a & b) not in (a, b) for a, b in combinations(triple, 2))]


def value(table, point, line):
    return (table >> (point | (line << 3))) & 1


def check(membership, tables):
    matches = Counter()
    for table in tables:
        for p_flip, l_flip in product((0, 7), repeat=2):
            points = [0] + [p_flip ^ (1 << i) for i in range(3)]
            private_lines = [0] + [l_flip ^ (1 << i) for i in range(3)]
            if any(value(table, pt, ln) != (i == j and i > 0)
                   for i, pt in enumerate(points) for j, ln in enumerate(private_lines)):
                continue
            codes = {m: set() for m in membership}
            for code in range(8):
                if value(table, 0, code):
                    continue
                m = sum(value(table, points[i + 1], code) << i for i in range(3))
                if m in codes:
                    codes[m].add(code)
            if not all(codes.values()):
                continue
            # Every singleton line is forced to its incidence mask.
            assert all(codes[m] == {m} for m in membership)
            matches[p_flip, l_flip] += 1
    return matches


def main():
    assert antichains(2) == []
    assert antichains(3) == [(1, 2, 4), (3, 5, 6)]
    physical = Counter()
    for rows in permutations(range(6), 3):
        _, targets, lines = project(rows, 'universal')
        membership = frozenset(sum(((target >> col) & 1) << i
                                   for i, target in enumerate(targets))
                               for col in range(len(lines)))
        assert {1, 2, 4} <= membership
        physical[membership] += 1
    common, triangle = frozenset((1, 2, 4, 7)), frozenset((1, 2, 4, 3, 5, 6))
    assert physical == {common: 12, triangle: 108}
    tables = mixed_trees(63)
    assert len(tables) == 3086
    for name, masks, expected in [('common', common, {(0, 0): 1}),
                                  ('triangle', triangle, {(0, 0): 1, (7, 0): 1})]:
        matches = check(masks, tables)
        assert matches == expected
        print(name, physical[masks], 'physical orders;', len(tables),
              'tables;', sum(matches.values()), 'normalized solutions; line masks forced')


if __name__ == '__main__':
    main()
