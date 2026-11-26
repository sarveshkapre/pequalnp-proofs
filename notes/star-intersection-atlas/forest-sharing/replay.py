"""Replay the tree and all gate claims using only Python 3.10+ and formulas.py."""
from collections import deque
from formulas import fit, zero

# Bit j of row i is the presence of edge (i,j).
EDGES = (10, 18, 21, 65, 1, 48, 8)
ROW_SIDES = (121, 87, 62, 95, 99, 124)
COLUMN_SIDES = (63, 106, 79, 119, 125, 126)
SHAPES = ('four rectangles', 'three and two', 'three pairs', 'one outside')


def verify_tree():
    neighbors = [set() for _ in range(14)]
    for i, mask in enumerate(EDGES):
        for j in range(7):
            if mask >> j & 1:
                neighbors[i].add(7 + j)
                neighbors[7 + j].add(i)
    queue = deque([0]); seen = {0}
    while queue:
        u = queue.popleft()
        for v in neighbors[u] - seen:
            seen.add(v)
            queue.append(v)
    assert len(seen) == 14 and sum(map(len, neighbors)) == 26
    print('Connected on 14 vertices, with 13 edges: a tree.')


def verify_circuit():
    for i, mask in enumerate(EDGES):
        for j in range(7):
            # Each signal is the complement of one rectangle, a free union of stars.
            a, b, c, d, e, f = [not ((r >> i & 1) and (k >> j & 1))
                                for r, k in zip(ROW_SIDES, COLUMN_SIDES)]
            shared = a and b
            left = c and (d or shared)
            right = e and (f or shared)
            assert (left or right) == bool(mask >> j & 1)
    print('Explicit three-intersection circuit agrees on all 49 cells.')


def check_assignment(rows, ncols, shape, assignment):
    assert len(assignment) == len(rows) + ncols
    for i, row_code in enumerate(assignment[:len(rows)]):
        for j, col_code in enumerate(assignment[len(rows):]):
            assert zero(shape, row_code & col_code) != bool(rows[i] >> j & 1)


def check_deletion(rows, ncols):
    for shape in range(4):
        assignment, _ = fit(rows, ncols, shape)
        if assignment is not None:
            check_assignment(rows, ncols, shape, assignment)
            return
    raise AssertionError('no formula witness for single-vertex deletion')


def main():
    verify_tree()
    verify_circuit()
    for shape, name in enumerate(SHAPES):
        control = tuple(sum((not zero(shape, r & c)) << j
                            for j, c in enumerate((63, 0, 5, 10, 21, 36, 51)))
                        for r in (0, 63, 3, 12, 17, 34, 56))
        assert 0 < sum(r.bit_count() for r in control) < 49
        witness, _ = fit(control, 7, shape)
        assert witness is not None
        check_assignment(control, 7, shape, witness)
        witness, nodes = fit(EDGES, 7, shape)
        assert witness is None
        print(f'{name}: excluded in {nodes} search nodes; positive control passed.')
    for i in range(7):
        check_deletion(EDGES[:i] + EDGES[i + 1:], 7)
    for j in range(7):
        below = (1 << j) - 1
        check_deletion(tuple((r & below) | ((r >> (j + 1)) << j) for r in EDGES), 6)
    print('Explicit formula witnesses checked for all 14 single-vertex deletions.')


if __name__ == '__main__':
    main()
