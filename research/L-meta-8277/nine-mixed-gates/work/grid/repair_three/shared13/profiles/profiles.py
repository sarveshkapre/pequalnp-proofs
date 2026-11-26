"""Group mixed suffixes by the singleton line codes their pure inputs must supply."""
import argparse
from collections import Counter
from functools import cache
from itertools import permutations
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1] / "tap_positions"))
from mixing_bound_six import input_tables, point_signatures, row_profiles, six_gate_tables
from mixing_bound_seven import dag_tables, find_reconstruction

SHAPES = {"012": (1, 2, 4, 7), "013": (1, 2, 4, 3, 5, 6)}


def permute(value, order):
    return sum(((value >> old) & 1) << new for new, old in enumerate(order))


@cache
def canonical(shape, width, data):
    domain, outputs = data
    types = SHAPES[shape]
    by_type = {m: [] for m in types}
    for code in range(1, 1 << width):
        if domain >> code & 1:
            member = sum(((output >> code) & 1) << i for i, output in enumerate(outputs))
            by_type[member].append(code)
    assert all(by_type.values())
    keys = []
    for line_order in permutations(range(width)):
        permuted = {m: tuple(sorted(permute(c, line_order) for c in codes))
                    for m, codes in by_type.items()}
        for row_order in permutations(range(3)):
            keys.append(tuple(permuted[permute(m, row_order)] for m in types))
    return min(keys)


def enumerate_suffixes(mixed):
    counts = Counter()
    remainder = Counter()
    for width in range(6, mixed + 2):
        for points in range(3, width - 2):
            lines = width - points
            for masks in point_signatures(points):
                q = max(len(set(masks) - {0, 1, 2, 4}), 2 if 7 in masks else 0)
                inputs = input_tables(masks, lines)
                if mixed == 6:
                    tables = six_gate_tables(masks, lines)
                else:
                    leaves = tuple((value, i < points, i >= points) for i, value in enumerate(inputs))
                    tables = dag_tables(leaves, mixed + 1 - width)
                for table in tables:
                    for shape, types in SHAPES.items():
                        data = row_profiles(table, lines, types)
                        if data is None:
                            continue
                        counts[shape] += 1
                        # Nine pure line gates are necessary to prepare the three row masks.
                        # After pure-point and mixed gates, at most K-mixed-q pure line gates remain.
                        for total in (12, 13):
                            allowed = 8 - (total - mixed - q)
                            if find_reconstruction(lines, *data, budget=allowed) is None:
                                key = shape, total, total - mixed - q, lines, canonical(shape, lines, data)
                                remainder[key] += 1
    expected = {6: (330, 552), 7: (16956, 21390)}
    assert tuple(counts[s] for s in SHAPES) == expected[mixed]
    return counts, remainder


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mixed", type=int, choices=(6, 7))
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    counts, remaining = enumerate_suffixes(args.mixed)
    records = [dict(shape=s, total=k, line_gates=budget, boundary=lines,
                    codes=codes, profiles=n)
               for (s, k, budget, lines, codes), n in sorted(remaining.items())]
    args.output.write_text(json.dumps(dict(mixed=args.mixed, counts=dict(counts), remaining=records), indent=2) + "\n")
    for shape in SHAPES:
        for total in (12, 13):
            subset = [r for r in records if r["shape"] == shape and r["total"] == total]
            print(shape, total, "mixed", args.mixed, "profiles", counts[shape],
                  "remaining", sum(r["profiles"] for r in subset), "classes", len(subset))


if __name__ == "__main__":
    main()
