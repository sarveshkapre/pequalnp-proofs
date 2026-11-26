"""Independent finite checks for the copy theorem and its desk applications."""

from itertools import combinations
import json
from pathlib import Path


def inputs(rows, cols):
    return [sum(1 << (r * cols + c) for c in range(cols)) for r in range(rows)] + [
        sum(1 << (r * cols + c) for r in range(rows)) for c in range(cols)
    ]


def circuit_costs(rows, cols):
    """Breadth-first search over sets of all available wires, allowing reuse."""
    full = (1 << (rows * cols)) - 1
    raw = frozenset(inputs(rows, cols))
    cost = dict.fromkeys(raw, 0)
    states = {raw}
    gates = 0
    # For a nonconstant output, AND/OR with a constant never adds a new signal.
    while len(cost) != full - 1:
        gates += 1
        following = set()
        for available in states:
            signals = {z for x, y in combinations(available, 2) for z in (x & y, x | y)}
            for z in signals.difference(available, {0, full}):
                cost.setdefault(z, gates)
                following.add(available | {z})
        assert following
        states = following
    return cost


def check_single_copies():
    base = circuit_costs(2, 2)
    checks = 0
    for row_copy in (True, False):
        actual = circuit_costs(3, 2) if row_copy else circuit_costs(2, 3)
        for mask, optimum in base.items():
            def cell(r, c):
                return (mask >> (2 * r + c)) & 1

            for u in range(2):
                eligible = any(cell(u, i) and not cell(1-u, i) for i in range(2)) if row_copy else any(
                    cell(i, u) and not cell(i, 1-u) for i in range(2)
                )
                if not eligible:
                    continue
                rr, cc = ([0, 1, u], [0, 1]) if row_copy else ([0, 1], [0, 1, u])
                copied = sum(cell(r, c) << (i * len(cc) + j)
                             for i, r in enumerate(rr) for j, c in enumerate(cc))
                assert actual[copied] == optimum + 1
                checks += 1
    # An output that only reads the first column has cost zero on both tables.
    assert base[5] == circuit_costs(3, 2)[21] == 0
    return checks


def verify_desk():
    rows = json.loads((Path(__file__).resolve().parents[1] / "data" / "desk-statements.json").read_text())["records"]
    assert len(rows) == len({r["id"] for r in rows}) == len({(r["rows"], r["cols"], r["mask"]) for r in rows})
    for rec in rows:
        R, C, m = rec["rows"], rec["cols"], rec["mask"]
        rr, cc = rec["row_labels"], rec["col_labels"]
        flipped = rec["shape"] == "transposed"
        seed = [3, 1, 4] if rec["shape"] == "corner" else [8, 5, 3]
        assert set(rr) == set(range(3))
        assert set(cc) == set(range(3 if rec["shape"] == "corner" else 4))
        assert (len(rr), len(cc)) == ((C, R) if flipped else (R, C))
        bits = (lambda i, j: (seed[rr[j]] >> cc[i]) & 1) if flipped else (
            lambda i, j: (seed[rr[i]] >> cc[j]) & 1)
        assert sum(bits(i, j) << (i*C+j) for i in range(R) for j in range(C)) == m
        binders = [f"(u : Fin {R}) (v : Fin {C})"]
        if R == C:
            binders.append(f"u v : Fin {R}")
        assert rec["statement"] in [
            f"PEqualNP.Represents.RepSizeAtMost (fun {bind} => ({m} : ℕ).testBit ({C} * u.val + v.val)) {R+C-1}"
            for bind in binders
        ]
    return len(rows)


if __name__ == "__main__":
    print(f"{check_single_copies()} single-copy circuit costs independently reproduced.")
    print(f"{verify_desk()} distinct desk masks and exact statements independently reconstructed.")
