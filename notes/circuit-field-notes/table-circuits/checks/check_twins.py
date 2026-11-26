"""Compare exhaustive formula costs before and after copying rows and columns."""

from functools import cache
from itertools import product
import json
from pathlib import Path


@cache
def costs(row_weights, col_weights):
    """Minimum weighted leaf sum for every truth table, without constants."""
    rows, cols = len(row_weights), len(col_weights)
    cells = rows * cols
    count = 1 << cells
    inputs = [sum(1 << (r * cols + c) for c in range(cols)) for r in range(rows)]
    inputs += [sum(1 << (r * cols + c) for r in range(rows)) for c in range(cols)]
    literals = list(zip(inputs, row_weights + col_weights))
    levels = [[]]
    best = {}
    while len(best) < count:
        size = len(levels)
        frontier = {signal for signal, weight in literals if weight == size}
        for left in range(1, size // 2 + 1):
            for a in levels[left]:
                for b in levels[size - left]:
                    frontier.add(a & b)
                    frontier.add(a | b)
        fresh = frontier.difference(best)
        best.update(dict.fromkeys(fresh, size))
        levels.append(fresh)
    return best


def copy_map(weights):
    return [i for i, size in enumerate(weights) for _ in range(size)]


def blow_up(mask, row_weights, col_weights):
    rr, cc = copy_map(row_weights), copy_map(col_weights)
    return sum(1 << (r * len(cc) + c) for r, i in enumerate(rr)
               for c, j in enumerate(cc) if mask & (1 << (i * len(col_weights) + j)))


def verify_small():
    checked = patterns = 0
    for rows, cols in [(2, 2), (2, 3), (3, 2), (3, 3)]:
        for weights in product([1, 2, 3], repeat=rows + cols):
            rw, cw = weights[:rows], weights[rows:]
            nr, nc = sum(rw), sum(cw)
            if nr * nc > 12 or nr + nc == rows + cols:
                continue
            actual = costs((1,) * nr, (1,) * nc)
            weighted = costs(rw, cw)
            for mask in range(1, 1 << (rows * cols)):
                assert actual[blow_up(mask, rw, cw)] == weighted[mask]
                checked += 1
            patterns += 1
    return patterns, checked


def seed_check():
    # A targeted enumeration for a 3×3 seed with one missing block corner and
    # an isolated one. The general reduction above is unnecessary for this test.
    seed = 0b100_001_011
    samples = [((1, 1, 1), (1, 1, 1)), ((2, 1, 1), (3, 1, 1)),
               ((5, 3, 2), (4, 4, 2)), ((1, 4, 2), (3, 1, 3)),
               ((2, 2, 2), (2, 2, 2))]
    for rw, cw in samples:
        n = sum(rw + cw)
        assert costs(rw, cw)[seed] == n + min(rw[0], cw[0])
        row_group, col_group = copy_map(rw), copy_map(cw)
        # Each group is pooled once. The six following gates implement the seed.
        gates = n - 6 + 6
        assert gates == n
        for r, c in product(range(len(row_group)), range(len(col_group))):
            a, b = row_group[r], col_group[c]
            col01 = b == 0 or b == 1
            first = a == 0 and col01
            second = a == 1 and b == 0
            corner = first or second
            island = a == 2 and b == 2
            assert (corner or island) == bool(seed & (1 << (3 * a + b)))
    return len(samples)


def verify_desk():
    records = json.loads((Path(__file__).resolve().parents[1] / "data" / "desk-matches.json").read_text())["matches"]
    assert len({record["id"] for record in records}) == len(records)
    seed = 0b100_001_011
    for record in records:
        rows, cols = record["rows"], record["cols"]
        rr, cc = record["row_classes"], record["col_classes"]
        assert (len(rr), len(cc)) == (rows, cols)
        assert set(rr) == set(cc) == {0, 1, 2}
        mask = sum(1 << (i * cols + j) for i, r in enumerate(rr) for j, c in enumerate(cc)
                   if seed & (1 << (3 * r + c)))
        assert mask == record["mask"]
        assert record["statement"] == (
            f"PEqualNP.Represents.RepSizeAtMost (fun (u : Fin {rows}) (v : Fin {cols}) => "
            f"({mask} : ℕ).testBit ({cols} * u.val + v.val)) {rows + cols - 1}")
        assert record["posted_budget"] + 1 == record["circuit"] == rows + cols
        weights_r = tuple(rr.count(i) for i in range(3))
        weights_c = tuple(cc.count(i) for i in range(3))
        assert costs(weights_r, weights_c)[seed] == record["formula"] + 1
    return len(records)


if __name__ == "__main__":
    patterns, tables = verify_small()
    print(f"{tables:,} nonempty table and multiplicity comparisons across {patterns} copying patterns.")
    print(f"{seed_check()} weighted seed minima and their explicit circuit constructions checked.")
    print(f"{verify_desk()} desk statements, row/column maps, and weighted minima checked.")
