"""Replay the explicit family and check optimal formula sizes on the two smallest squares."""

from itertools import product
from pathlib import Path
import json


def inputs(rows, cols):
    return [sum(1 << (i * cols + j) for j in range(cols)) for i in range(rows)] + [
        sum(1 << (i * cols + j) for i in range(rows)) for j in range(cols)
    ]


def square(k):
    n = k + 2
    return sum(1 << (n * r + c) for r, c in product(range(n), repeat=2)
               if (r <= k and c <= k and (r < k or c < k)) or r == c == k + 1)


def build_square(k):
    n = k + 2
    wires = inputs(n, n)
    # Unfolding a circuit into a formula adds the leaf counts at every binary gate.
    leaves = [1] * len(wires)

    def gate(op, a, b):
        wires.append(wires[a] & wires[b] if op == "and" else wires[a] | wires[b])
        leaves.append(leaves[a] + leaves[b])
        return len(wires) - 1

    def group(start):
        out = start
        for j in range(1, k):
            out = gate("or", out, start + j)
        return out

    rows, cols = group(0), group(n)
    wide_cols = gate("or", cols, n + k)
    first = gate("and", rows, wide_cols)
    second = gate("and", k, cols)
    block = gate("or", first, second)
    isolated = gate("and", k + 1, n + k + 1)
    result = gate("or", block, isolated)
    return wires[result], len(wires) - 2 * n, leaves[result] - 1


def minimum_formula(rows, cols, target, max_gates):
    # Split a tree at its root. For either child a cheapest equivalent tree suffices.
    levels = [set(inputs(rows, cols))]
    seen = levels[0].copy()
    if target in seen:
        return 0
    for size in range(1, max_gates + 1):
        new = set()
        for i in range((size - 1) // 2 + 1):
            for a in levels[i]:
                for b in levels[size - 1 - i]:
                    new.add(a & b)
                    new.add(a | b)
        new.difference_update(seen)
        if target in new:
            return size
        seen.update(new)
        levels.append(new)
    return None


def corner_centres(mask, rows, cols):
    def edge(r, c):
        return (mask >> (r * cols + c)) & 1

    return {(r, c) for r, c in product(range(rows), range(cols)) if edge(r, c)
            and any(edge(r, d) and edge(s, c) and not edge(s, d)
                    for s, d in product(range(rows), range(cols)))}


def main():
    for k in range(1, 33):
        mask, circuit, formula = build_square(k)
        assert (mask, circuit, formula) == (square(k), 2 * k + 4, 3 * k + 3)
        n = k + 2
        for i in range(k):
            # These k middle cells have distinct rows and columns and the same missing corner.
            assert all((mask >> (r * n + c)) & 1 for r, c in [(i, i), (k, i), (i, k)])
        assert not (mask >> (k * n + k)) & 1
    for k in (1, 2):
        assert minimum_formula(k + 2, k + 2, square(k), 3 * k + 3) == 3 * k + 3

    targets = {34262, 39902, 47574, 48094, 105720}
    cases = json.loads((Path(__file__).resolve().parents[1] / "data" / "square-controls.json").read_text())["rows"]
    cases = [case for case in cases if case["mask"] in targets]
    assert {case["mask"] for case in cases} == targets
    for case in cases:
        centres = corner_centres(case["mask"], 4, 5)
        assert any(r != s and c != d for (r, c), (s, d) in product(centres, repeat=2))
    print("32 square constructions checked on all promised inputs, including their gate and leaf counts.")
    print("Independent formula enumeration confirmed 6 gates for 3×3 and 9 gates for 4×4.")
    print("Two disjoint corner conflicts found in each of the five 4×5 desk tables.")


if __name__ == "__main__":
    main()
