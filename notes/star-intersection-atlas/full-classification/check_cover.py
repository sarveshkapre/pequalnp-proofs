"""Replay a constructive cover of every 5 x 6 matrix except the quadrangle orbit.

Python 3, standard library only. Complements are used throughout: an input is
a rectangle, a binary union costs one, and intersections are free.
"""
from itertools import combinations_with_replacement, permutations
from math import comb, factorial

# Each row's six bits specify its memberships in the six rectangle row sides.
ROW_ASSIGNMENTS = (
    (23, 27, 47, 53, 62), (21, 27, 39, 45, 62), (23, 29, 43, 47, 62),
    (21, 27, 39, 43, 62), (23, 27, 39, 61, 62), (21, 26, 47, 54, 57),
    (23, 29, 47, 59, 62), (21, 27, 43, 54, 61), (21, 27, 47, 57, 62),
    (21, 27, 47, 55, 62), (23, 27, 29, 39, 46), (23, 27, 47, 61, 62),
)
QUADRANGLE_EDGE_ROWS = (49, 42, 22, 13, 3)


def output_column(rows, column):
    """Evaluate (A ∪ B) ∩ (C ∪ D) ∩ (E ∪ F), one row at a time."""
    result = 0
    for i, row in enumerate(rows):
        leaf = [bool(row & column & (1 << j)) for j in range(6)]
        if (leaf[0] or leaf[1]) and (leaf[2] or leaf[3]) and (leaf[4] or leaf[5]):
            result |= 1 << i
    return result


def column_options():
    # Bit j marks one common row assignment. Its six column codes can be
    # picked independently, since the column side of each rectangle is arbitrary.
    assignments = sorted({p for seed in ROW_ASSIGNMENTS for p in permutations(seed)})
    options = [0] * 32
    for i, rows in enumerate(assignments):
        for column in {output_column(rows, code) for code in range(64)}:
            options[column] |= 1 << i
    return options


def quadrangle_orbit():
    orbit = set()
    for rows in permutations(QUADRANGLE_EDGE_ROWS):
        columns = [sum((1 - ((r >> j) & 1)) << i for i, r in enumerate(rows))
                   for j in range(6)]
        orbit.add(tuple(sorted(columns)))
    return orbit


def main():
    options = column_options()
    excluded = set()
    count = 0
    for columns in combinations_with_replacement(range(32), 6):
        a, b, c, d, e, f = columns
        if not (options[a] & options[b] & options[c] & options[d] & options[e] & options[f]):
            excluded.add(columns)
        count += 1
    exceptions = quadrangle_orbit()
    if count != comb(37, 6) or len(exceptions) != 15 or excluded != exceptions:
        raise ValueError(f"Cover mismatch: {count} multisets, {len(excluded)} uncovered")
    if any(len(set(cols)) != 6 for cols in exceptions):
        raise ValueError("Expected distinct columns in each exceptional matrix")
    print(f"{count:,} unordered column multisets checked, including every repetition.")
    print(f"{count-len(excluded):,} have explicit three-operation formulas.")
    print(f"The other {len(excluded)} are exactly the row relabelings of pjscruggs's quadrangle.")
    print(f"{len(excluded)*factorial(6):,} exceptional labeled matrices out of {32**6:,}.")


if __name__ == "__main__":
    main()
