"""Reconstruct the three line masks for every feasible seven-mixed-gate suffix."""
from collections import Counter
from functools import cache
from itertools import combinations

from mixing_bound_six import input_tables, make_tree_enumerator, point_signatures, row_profiles


def dag_tables(leaves, surplus):
    """surplus = #gates + 1 - #input occurrences; zero describes a tree."""
    size = len(leaves)
    point_set = sum(1 << i for i, (_, point, _) in enumerate(leaves) if point)
    line_set = sum(1 << i for i, (_, _, line) in enumerate(leaves) if line)
    all_leaves = (1 << size) - 1
    trees = make_tree_enumerator([value for value, _, _ in leaves], point_set, line_set)
    if surplus == 0:
        return trees(all_leaves)

    # Take a node read at least twice and closest to the inputs among such nodes.
    # Its entire cone is a tree, and no earlier node in it feeds the outside.
    tables = set()
    for shared in range(1, all_leaves + 1):
        remaining = tuple(leaf for i, leaf in enumerate(leaves) if not shared >> i & 1)
        for value in trees(shared):
            leaf = (value, bool(shared & point_set), bool(shared & line_set))
            for uses in range(2, surplus + 2):
                tables.update(dag_tables(remaining + (leaf,) * uses, surplus - (uses - 1)))
    return tables


@cache
def find_reconstruction(line_width, domain, goals, budget):
    """Produce a single straight-line program for all three restricted rows."""
    sources = tuple(sum(1 << code for code in range(1 << line_width) if code >> i & 1)
                    & domain for i in range(line_width)) + (0,)

    @cache
    def search(wires, remaining):
        missing = set(goals) - wires
        if not missing:
            return ()
        if len(missing) > remaining:
            return None
        options = {}
        for left, right in combinations(sorted(wires), 2):
            for op, value in (('and', left & right), ('or', left | right)):
                if value not in wires:
                    options[value] = (op, left, right)
        # A missing target available in one gate can always be built immediately.
        ready = missing & options.keys()
        candidates = sorted(ready)[:1] if ready else sorted(options)
        if not ready and len(missing) == remaining:
            return None
        for value in candidates:
            rest = search(wires | {value}, remaining - 1)
            if rest is not None:
                return (options[value],) + rest
        return None

    plan = search(frozenset(sources), budget)
    if plan is None:
        return None
    # Resolve persistent source indexes once, and replay with scalar Booleans.
    names = list(sources)
    gates = []
    for op, left, right in plan:
        gates.append((op, names.index(left), names.index(right)))
        names.append(left & right if op == 'and' else left | right)
    taps = [names.index(target) for target in goals]
    assert len(gates) <= budget
    for code in range(1 << line_width):
        if domain >> code & 1:
            values = [bool(code >> j & 1) for j in range(line_width)] + [False]
            for op, left, right in gates:
                values.append((values[left] and values[right]) if op == 'and'
                              else (values[left] or values[right]))
            assert [values[tap] for tap in taps] == [bool(target >> code & 1) for target in goals]
    return len(plan)


def recover(line_width, domain, goals, budget):
    length = find_reconstruction(line_width, domain, goals, budget)
    assert length is not None
    return length


def check_widths(points, lines):
    shapes = {'common': (1, 2, 4, 7), 'triangle': (1, 2, 4, 3, 5, 6)}
    signatures = list(point_signatures(points))
    assert len(signatures) == {3: 2, 4: 9, 5: 30}[points]
    successes = Counter()
    for masks in signatures:
        inputs = input_tables(masks, lines)
        leaves = tuple((value, i < points, i >= points) for i, value in enumerate(inputs))
        tables = dag_tables(leaves, 8 - len(inputs))
        # Only singleton point masks are primary. A mask covering all three needs two gates.
        point_gates = max(len(set(masks) - {0, 1, 2, 4}), 2 if 7 in masks else 0)
        for table in tables:
            for shape, required in shapes.items():
                data = row_profiles(table, lines, required)
                if data is not None:
                    recover(lines, *data, budget=4 + point_gates)
                    successes[shape] += 1
    print(points, lines, successes['common'], successes['triangle'], flush=True)
    assert all(successes[shape] > 0 for shape in shapes)
    return successes


def main():
    total = Counter()
    for count in (8, 7, 6):
        for points in range(3, count - 2):
            total.update(check_widths(points, count - points))
    assert total == {'common': 16956, 'triangle': 21390}
    print('Total surviving profiles with a replayed reconstruction:', dict(total))


if __name__ == '__main__':
    main()
