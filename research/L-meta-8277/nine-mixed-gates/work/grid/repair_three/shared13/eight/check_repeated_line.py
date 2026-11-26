"""Plant a circuit that reads a pure line wire twice, then find its profile in the search."""
import argparse
from collections import Counter
from itertools import combinations
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / "fan"))
from classify import SHAPES, normalize

sys.path.insert(0, str(HERE.parents[1]))
from pair_prune import ROWS, cases, layout, lines, traces


def check_circuit(active, tests):
    fixed, _, _ = layout(active)
    fixed_outputs = [30 + i for i, (op, _, _) in enumerate(fixed) if op == "and"]
    gates = fixed.copy()

    def add(op, left, right):
        gates.append((op, left, right))
        return 29 + len(gates)

    def row_signal(row):
        raw = [6 + j for j in lines(row)]
        wire = raw[0]
        for leaf in raw[1:]:
            wire = add("or", wire, leaf)
        return wire

    a, b, c = active
    ra, rb, rc = map(row_signal, active)
    shared = add("or", ra, rb)
    outside = next(j for j in range(11) if not (ROWS[c] >> j) & 1)
    extra = add("or", rc, 6 + outside)
    start = 30 + len(gates)
    terms = [add("and", add("and", p, row), guard)
             for p, row, guard in ((a, ra, shared), (b, rb, shared), (c, rc, extra))]
    out = add("or", add("or", terms[0], terms[1]), terms[2])
    mixed = gates[start - 30:]
    reads = Counter(w for _, left, right in mixed for w in (left, right))
    assert len(mixed) == 8 and out == start + 7
    assert set(w for w in reads if w < start) == {*active, ra, rb, rc, shared, extra}
    assert reads[shared] == 2 and all(n == 1 for w, n in reads.items() if w != shared)
    for f in fixed_outputs:
        out = add("or", out, f)
    expected = sum(label << k for k, (_, _, label) in enumerate(tests))
    assert traces(gates, tests)[out] == expected and len(gates) - 15 == 19

    # Evaluate this same mixed section with the five line signals independently set.
    shape = "012" if ROWS[a] & ROWS[b] & ROWS[c] else "013"
    by_kind = [0] * 8
    for code in range(32):
        rows_on = 0
        for index, point in enumerate((None, *active)):
            values = {w: w == point for w in active}
            for i, w in enumerate((ra, rb, rc, shared, extra)):
                values[w] = bool(code & (1 << i))
            for w, (op, left, right) in enumerate(mixed, start):
                values[w] = (values[left] and values[right] if op == "and"
                             else values[left] or values[right])
            if index == 0:
                assert not values[start + 7]
            elif values[start + 7]:
                rows_on |= 1 << (index - 1)
        if rows_on in SHAPES[shape]:
            by_kind[rows_on] |= 1 << code
    return shape, normalize(tuple(by_kind), 5, shape)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("enumeration", type=Path, help="fan/enumerate.cpp output at width five")
    args = parser.parse_args()
    tests = cases()
    assert len(tests) == 177
    searched = set()
    for line in args.enumeration.read_text().splitlines():
        shape, _, _, _, *bits = line.split("\t")
        searched.add((shape, normalize(tuple(map(int, bits)), 5, shape)))
    for active in combinations(range(6), 3):
        assert check_circuit(active, tests) in searched, active
    print("20 larger controls with a repeated pure line passed all 177 grid tests.")
    print("The eight-gate enumeration contained their profiles in both shapes.")
