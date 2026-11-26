"""Test whether the shared three-intersection form separates on C4-free graphs."""
from collections import Counter
from functools import lru_cache


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def shared_edge(row, col):
    a, b, c, d, e, f = ((row & col) >> j & 1 for j in range(6))
    h = a or b
    return not ((c or (d and h)) and (e or (f and h)))


def representatives():
    profiles = {}
    for r in range(64):
        key = tuple(shared_edge(r, c) for c in range(64))
        profiles.setdefault(key, r)
    return list(profiles.values())


PROFILES = representatives()
EDGES = [sum(1 << j for j, c in enumerate(PROFILES) if shared_edge(r, c))
         for r in PROFILES]
FULL = (1 << len(EDGES)) - 1


def reduce_side(rows, cols):
    """An all-edge row can be restored by leaving it out of every zero rectangle."""
    seen = {cols}
    keep = 0
    for r in bits(rows):
        key = EDGES[r] & cols
        if key not in seen:
            keep |= 1 << r
            seen.add(key)
    return keep


def normalize(rows, cols):
    while True:
        new_rows = reduce_side(rows, cols)
        new_cols = reduce_side(cols, new_rows)
        if (new_rows, new_cols) == (rows, cols):
            return (rows, cols) if rows <= cols else (cols, rows)
        rows, cols = new_rows, new_cols


def branch_pair(rows, cols):
    # Choose a pair with a large common neighborhood. Keeping both vertices
    # then bounds the opposite side by deleting all but one common neighbor.
    best = (1, 0, 0, 0)
    for r in bits(rows):
        row = EDGES[r] & cols
        remainder = rows >> (r + 1) << (r + 1)
        for s in bits(remainder):
            common = row & EDGES[s]
            size = common.bit_count()
            if size > best[0]:
                best = size, r, s, common
    return best


def packed(rows, cols):
    return tuple(sum(1 << j for j,c in enumerate(bits(cols)) if EDGES[r] & (1 << c))
                 for r in bits(rows))


class FoundWitness(Exception):
    pass


def run(find=False):
    stats = Counter()
    terminal_sizes = Counter()

    def visit(rows, cols):
        return search(*normalize(rows, cols))

    @lru_cache(maxsize=None)
    def search(rows, cols):
        if min(rows.bit_count(), cols.bit_count()) <= 4:
            stats['four or fewer'] += 1
            return
        pair = branch_pair(rows, cols)
        transposed_pair = branch_pair(cols, rows)
        if transposed_pair[0] > pair[0]:
            rows, cols, pair = cols, rows, transposed_pair
        n, r, s, common = pair
        if n == 1:
            stats['C4-free'] += 1
            size = rows.bit_count(), cols.bit_count()
            terminal_sizes[size] += 1
            if find and min(size) >= 10:
                # Prioritize large patterns, then shrink any witness separately.
                from formulas import fit
                target = packed(rows, cols)
                if all(fit(target, size[1], s)[0] is None for s in (2, 1, 0, 3)):
                    raise FoundWitness(rows, cols)
            return
        stats['split'] += 1
        visit(rows ^ (1 << r), cols)
        visit(rows ^ (1 << s), cols)
        outside = cols ^ common
        for c in bits(common):
            visit(rows, outside | (1 << c))
    try:
        visit(FULL, FULL)
    except FoundWitness as found:
        rows, cols = found.args
        print('First counterexample:', rows.bit_count(), 'by', cols.bit_count())
        print('Row profile representatives:', [PROFILES[i] for i in bits(rows)])
        print('Column profile representatives:', [PROFILES[i] for i in bits(cols)])
        print('Edge row masks:', packed(rows, cols))
        return
    print('Profiles:', len(PROFILES))
    print('States:', sorted(stats.items()))
    print('C4-free terminal dimensions:', sorted(terminal_sizes.items()))


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--find', action='store_true', help='stop at the first large witness')
    run(find=parser.parse_args().find)
