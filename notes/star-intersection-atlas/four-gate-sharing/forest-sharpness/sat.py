"""Independently encode one manually listed four-union shape as DIMACS on stdout."""
import argparse
import json
from pathlib import Path

# Coordinates are the independent rectangle memberships at a cell.
FORMS = (
    (7, lambda a,b,c,d,e,f,g: (((a|b) & (c|d)) | e) & (f|g)),
    (8, lambda a,b,c,d,e,f,g,h: (a|b) & (c|d) & (e|f) & (g|h)),
    (7, lambda a,b,c,d,e,f,g: (a|b) & (c|d) & (e|f|g)),
    (6, lambda a,b,c,d,e,f: (a|b) & (c|d|e|f)),
    (6, lambda a,b,c,d,e,f: (a|b|c) & (d|e|f)),
    (6, lambda a,b,c,d,e,f: ((a|b) & (c|d)) | e | f),
    (7, lambda a,b,c,d,e,f,g: ((a|b) & (c|d) & (e|f)) | g),
    (6, lambda a,b,c,d,e,f: ((a|b) & (c|d|e)) | f),
    (5, lambda a,b,c,d,e: a|b|c|d|e),
)


def bits(x):
    while x:
        bit = x & -x
        yield bit.bit_length() - 1
        x ^= bit


def encode(neighbors, n, shape):
    width, evaluate = FORMS[shape]
    full = (1 << width) - 1
    table = [evaluate(*((x >> b) & 1 for b in range(width))) for x in range(full + 1)]
    minimal_true = [x for x in range(full + 1) if table[x] and
                    all(not table[x ^ (1 << b)] for b in bits(x))]
    maximal_false = [x for x in range(full + 1) if not table[x] and
                     all(table[x | (1 << b)] for b in bits(full ^ x))]
    rows = len(neighbors)
    variables = (rows + n) * width
    clauses = []

    def var(vertex, bit):
        return 1 + vertex * width + bit

    def fresh():
        nonlocal variables
        variables += 1
        return variables

    for i, adjacent in enumerate(neighbors):
        for j in range(n):
            if j in adjacent:
                # A zero value excludes every minimal true set.
                for mask in minimal_true:
                    clauses.append([-var(v, b) for b in bits(mask) for v in (i, rows+j)])
            else:
                # A true value requires a joint bit outside each maximal false set.
                joint = [fresh() for _ in range(width)]
                for b, both in enumerate(joint):
                    clauses.extend([[-both, var(i, b)], [-both, var(rows+j, b)]])
                for mask in maximal_false:
                    clauses.append([joint[b] for b in bits(full ^ mask)])

    # Adjacent interchangeable coordinates can be sorted by their row-membership
    # vectors. A prefix flag must stay true while both vectors agree.
    for b in range(width - 1):
        swap = 3 << b
        if any(table[x] != table[x ^ swap] for x in range(full + 1) if x & swap == 1 << b):
            continue
        prefix = []
        for i in range(rows):
            a, c = var(i, b), var(i, b+1)
            clauses.append(prefix + [-a, c])
            equal = fresh()
            clauses.extend([prefix + [a, c, equal], prefix + [-a, -c, equal]])
            prefix = [-equal]
    return variables, clauses


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("shape", type=int, choices=range(9))
    args = parser.parse_args()
    data = json.loads(Path(__file__).with_name("witness.json").read_text())
    count, clauses = encode(data["neighbors"], 10, args.shape)
    print("p cnf", count, len(clauses))
    for clause in clauses:
        print(*clause, 0)
