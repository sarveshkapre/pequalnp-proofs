"""Replay the C4-free witness, its exact formula exclusion and the deletion tests."""
from itertools import combinations
from check import PROFILES, shared_edge
from formulas import fit, zero

ROW_CODES = (27, 29, 30, 45, 46, 47, 53)
COL_CODES = (31, 47, 54, 55, 58, 59, 61)
EDGES = (14, 18, 2, 21, 65, 1, 48)
SHAPES = ('four rectangles', 'three and two', 'three pairs', 'one outside')


def verify_assignment(rows, ncols, s, witness):
    row_codes, col_codes = witness[:len(rows)], witness[len(rows):]
    assert len(col_codes) == ncols
    for i, row in enumerate(row_codes):
        for j, col in enumerate(col_codes):
            assert zero(s, row & col) != bool(rows[i] & (1 << j))


def formula_exists(rows, ncols):
    for s in range(4):
        assignment, _ = fit(rows, ncols, s)
        if assignment is not None:
            verify_assignment(rows, ncols, s, assignment)
            return True
    return False


def main():
    assert len(PROFILES) == 26
    assert set(ROW_CODES + COL_CODES) <= set(PROFILES)
    generated = tuple(sum(int(shared_edge(row, col)) << j for j, col in enumerate(COL_CODES))
                      for row in ROW_CODES)
    assert generated == EDGES
    common = [(r & s).bit_count() for r, s in combinations(EDGES, 2)]
    assert max(common) == 1
    print('26 universal profiles. The chosen 7 by 7 submatrix has 14 edges.')
    assert sum(x.bit_count() for x in EDGES) == 14
    print('Maximum common neighbors of two distinct rows:', max(common))
    # Connectivity + V = E gives one cycle. Its six vertices are shown below.
    reached_rows, reached_cols = {0}, set()
    for _ in range(14):
        reached_cols.update(j for i in reached_rows for j in range(7) if EDGES[i] >> j & 1)
        reached_rows.update(i for j in reached_cols for i in range(7) if EDGES[i] >> j & 1)
    assert len(reached_rows) == len(reached_cols) == 7
    assert all(EDGES[i] >> j & 1 for i, j in [(0,2),(3,2),(3,4),(1,4),(1,1),(0,1)])
    print('Connected. The unique cycle has length six.')
    for s, name in enumerate(SHAPES):
        control = tuple(sum((not zero(s, r & c)) << j for j,c in enumerate((63,0,5,10,21,36,51)))
                        for r in (0,63,3,12,17,34,56))
        assert 0 < sum(row.bit_count() for row in control) < 49
        witness, _ = fit(control, 7, s)
        assert witness is not None
        verify_assignment(control, 7, s, witness)
        assignment, visits = fit(EDGES, 7, s)
        assert assignment is None
        print(f'{name}: excluded ({visits} search nodes); positive control passed.')
    for i in range(7):
        assert formula_exists(EDGES[:i] + EDGES[i+1:], 7)
    for j in range(7):
        before = (1 << j) - 1
        remove = tuple((r & before) | ((r >> (j+1)) << j) for r in EDGES)
        assert formula_exists(remove, 6)
    print('Explicit formula witnesses checked for all 14 single-vertex deletions.')


if __name__ == '__main__':
    main()
