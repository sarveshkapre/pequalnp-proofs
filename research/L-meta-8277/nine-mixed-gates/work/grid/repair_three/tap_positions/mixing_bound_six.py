"""Test the six-mixed-gate suffix against the certified row-mask lower bound."""
from collections import Counter
from functools import cache
from itertools import combinations, combinations_with_replacement, permutations, product


def point_signatures(width):
    """Relabel boundary wires and the three singleton points for each representative."""
    permutations_of_rows = tuple(permutations(range(3)))

    def relabel(mask, perm):
        return sum(((mask >> i) & 1) << j for i, j in enumerate(perm))

    for masks in combinations_with_replacement(range(8), width):
        codes = [sum(((mask >> row) & 1) << j for j, mask in enumerate(masks))
                 for row in range(3)]
        if any((a & b) in (a, b) for a, b in combinations(codes, 2)):
            continue
        if any(tuple(sorted(relabel(m, perm) for m in masks)) < masks
               for perm in permutations_of_rows):
            continue
        yield masks


def input_tables(point_masks, line_width):
    """Four point samples (zero, then the three singletons) times all line codes."""
    codes = 1 << line_width
    full = (1 << codes) - 1
    points = [sum(full << ((row + 1) * codes) for row in range(3) if mask >> row & 1)
              for mask in point_masks]
    lines = [sum(1 << code for code in range(codes) if code >> j & 1)
             for j in range(line_width)]
    repeated = [sum(line << (row * codes) for row in range(4)) for line in lines]
    return points + repeated


def make_tree_enumerator(inputs, point_set, line_set):
    """Cache truth tables for trees on a subset of the named input occurrences."""
    @cache
    def trees(subset):
        if subset.bit_count() == 1:
            return {inputs[subset.bit_length() - 1]}
        if not (subset & point_set and subset & line_set):
            return set()
        tables = set()
        left = (subset - 1) & subset
        while left:
            right = subset ^ left
            if left < right:
                for a, b in product(trees(left), trees(right)):
                    tables.update((a & b, a | b))
            left = (left - 1) & subset
        return tables

    return trees


def six_gate_tables(point_masks, line_width):
    inputs = input_tables(point_masks, line_width)
    point_set = (1 << len(point_masks)) - 1
    all_leaves = (1 << len(inputs)) - 1
    line_set = all_leaves ^ point_set
    trees = make_tree_enumerator(inputs, point_set, line_set)
    if len(inputs) == 7:
        return trees(all_leaves)

    assert len(inputs) == 6
    tables = set()
    for shared in range(1, all_leaves + 1):
        # Exactly one node is read twice. Everything feeding that node is a tree.
        other = [i for i in range(len(inputs)) if not shared >> i & 1]
        first_copy = len(other)
        outside_points = sum(1 << i for i, source in enumerate(other) if point_set >> source & 1)
        outside_lines = ((1 << first_copy) - 1) ^ outside_points
        if shared & point_set:
            outside_points |= 3 << first_copy
        if shared & line_set:
            outside_lines |= 3 << first_copy
        for value in trees(shared):
            # Both copies have the same truth table and each is used once in the top tree.
            copies = [inputs[i] for i in other] + [value, value]
            upper = make_tree_enumerator(copies, outside_points, outside_lines)
            tables.update(upper((1 << len(copies)) - 1))
            upper.cache_clear()
    return tables


def row_profiles(table, line_width, required):
    """Keep the zero code and every code that could be a kept physical singleton."""
    codes = 1 << line_width
    full = (1 << codes) - 1
    if any(table >> (row * codes) & 1 for row in range(4)):
        return None  # all outputs must be off with no line
    possible = full & ~table  # row zero is the block for no points
    profiles = [(table >> (row * codes)) & full for row in range(1, 4)]
    accepted_codes = 1
    for membership in required:
        matching = possible
        for j, profile in enumerate(profiles):
            matching &= profile if membership >> j & 1 else ~profile
        if not matching:
            return None
        accepted_codes |= matching
    return accepted_codes, tuple(x & accepted_codes for x in profiles)


@cache
def build_row_masks(line_width, domain, goals):
    """Return an actual list of at most three gates for all three restricted rows."""
    sources = tuple(sum(1 << code for code in range(1 << line_width) if code >> i & 1)
                    & domain for i in range(line_width)) + (0,)

    def search(wires, remaining):
        missing = set(goals) - set(wires)
        if not missing:
            return ()
        if len(missing) > remaining:
            return None
        options = {}
        for i, j in combinations(range(len(wires)), 2):
            for op, value in (('and', wires[i] & wires[j]), ('or', wires[i] | wires[j])):
                if value not in wires:
                    options[value] = (op, i, j)
        for value, gate in options.items():
            if value not in missing and len(missing) == remaining:
                continue
            rest = search(wires + (value,), remaining - 1)
            if rest is not None:
                return (gate,) + rest
        return None

    witness = search(sources, 3)
    assert witness is not None
    # Independent bit-by-bit replay of the reconstruction on every admissible code.
    for code in range(1 << line_width):
        if not (domain >> code & 1):
            continue
        wires = [bool(code >> j & 1) for j in range(line_width)] + [False]
        for op, left, right in witness:
            wires.append((wires[left] and wires[right]) if op == 'and'
                         else (wires[left] or wires[right]))
        # Match wire indexes across all assignments, rather than choosing per code.
        if code == 0:
            replay = [0 for _ in wires]
        for j, value in enumerate(wires):
            replay[j] |= int(value) << code
    assert set(goals) <= set(replay)
    return len(witness)


def main():
    shapes = {'common': (1, 2, 4, 7), 'triangle': (1, 2, 4, 3, 5, 6)}
    for points, lines in [(3, 3), (3, 4), (4, 3)]:
        signatures = list(point_signatures(points))
        assert len(signatures) == (2 if points == 3 else 9)
        successes = Counter()
        for bits in signatures:
            for table in six_gate_tables(bits, lines):
                for shape, required in shapes.items():
                    data = row_profiles(table, lines, required)
                    if data is not None:
                        build_row_masks(lines, *data)
                        successes[shape] += 1
        print(f'{points} point and {lines} line wires: {dict(successes)}')
        assert all(successes[s] > 0 for s in shapes)
    print('Every admissible profile has a jointly replayed reconstruction with at most 3 line gates.')


if __name__ == '__main__':
    main()
