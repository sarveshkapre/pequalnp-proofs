"""Finite controls for sparse label formulas and rectangle certificates (standard library)."""
from collections import deque
from functools import lru_cache
from itertools import product
from math import ceil, log2
from random import Random


def bit(i):
    return 1 << i


class Grid:
    def __init__(self, rows, cols):
        self.rows, self.cols = rows, cols
        self.row = [sum(bit(i*cols+j) for j in range(cols)) for i in range(rows)]
        self.col = [sum(bit(i*cols+j) for i in range(rows)) for j in range(cols)]
        self.all = bit(rows*cols)-1

    def rect(self, cells):
        rows = [i for i, mask in enumerate(self.row) if mask & cells]
        cols = [j for j, mask in enumerate(self.col) if mask & cells]
        return sum(bit(i*self.cols+j) for i in rows for j in cols) == cells


def star_layers(grid, graph):
    """Peel spanning forests; orient each rooted tree by parity."""
    pending = {(i, j+grid.rows) for i in range(grid.rows) for j in range(grid.cols)
               if bit(i*grid.cols+j) & graph}
    layers = []
    while pending:
        adjacent = [[] for _ in range(grid.rows+grid.cols)]
        for u, v in sorted(pending):
            adjacent[u].append(v)
            adjacent[v].append(u)
        edges = [dict(), dict()]
        visited = set()
        for root in range(len(adjacent)):
            if root in visited:
                continue
            visited.add(root)
            queue = deque([root])
            while queue:
                u = queue.popleft()
                for v in adjacent[u]:
                    if v in visited:
                        continue
                    visited.add(v)
                    queue.append(v)
                    group = edges[int(u >= grid.rows)].setdefault(u, [])
                    group.append(v)
                    pending.remove(tuple(sorted((u, v))))
        layers.extend(e for e in edges if e)
    return layers


def compile_layer(grid, layer, depth):
    """Evaluate physical disjoint-union and binary-intersection formulas on all cells."""
    groups = list(layer.items())
    width = min(2**(depth-1), max(1, ceil(log2(len(groups)+1))))
    base = 1
    while base**width < len(groups):
        base += 1
    row_id, col_id = {}, {}
    for label, (center, children) in enumerate(groups):
        for vertex in [center, *children]:
            dest = row_id if vertex < grid.rows else col_id
            index = vertex if vertex < grid.rows else vertex-grid.rows
            assert index not in dest
            dest[index] = label
    words = []
    for pos in range(width):
        digit_word = 0
        for value in range(base):
            rows = sum(grid.row[i] for i, label in row_id.items() if label//base**pos % base == value)
            cols = sum(grid.col[j] for j, label in col_id.items() if label//base**pos % base == value)
            digit_word |= rows & cols
        words.append((digit_word, 1, base))
    while len(words) > 1:
        next_words = []
        pairs = len(words)//2
        for i in range(pairs):
            x, dx, kx = words[2*i]
            y, dy, ky = words[2*i+1]
            next_words.append((x & y, 1+max(dx, dy), 1+kx+ky))
        if len(words) % 2:
            next_words.append(words[-1])
        words = next_words
    return words[0]


def max_matching(grid, graph):
    @lru_cache(None)
    def best(i, used):
        if i == grid.rows:
            return 0
        choices = [best(i+1, used)]
        for j in range(grid.cols):
            if graph & bit(i*grid.cols+j) and not used & bit(j):
                choices.append(1+best(i+1, used | bit(j)))
        return max(choices)
    return best(0, 0)


def graph_controls(grid):
    forests = 0
    for graph in range(grid.all+1):
        groups = star_layers(grid, graph)
        matching = max_matching(grid, graph)
        assert all(len(group) <= matching for group in groups)
        # Direct cycle check independent of root parity.
        parent = list(range(grid.rows+grid.cols))
        def root(v):
            while parent[v] != v:
                v = parent[v]
            return v
        forest = True
        for i, j in product(range(grid.rows), range(grid.cols)):
            if graph & bit(i*grid.cols+j):
                u, v = root(i), root(grid.rows+j)
                if u == v:
                    forest = False
                parent[u] = v
        if forest:
            assert len(groups) <= 2
            forests += 1
        for depth in (1, 2, 3):
            result = 0
            for layer in groups:
                word, actual_depth, gates = compile_layer(grid, layer, depth)
                assert actual_depth <= depth
                assert gates >= 1
                result |= word
            assert result == graph
    return forests


def certificate_controls():
    """Reconstruct the rectangular witnesses for reused wires from cell truth values."""
    rng = Random(20261126)
    g = Grid(6, 7)
    successes = 0
    sizes = set()
    for trial in range(400):
        bank, masks, witnesses, levels = [], [], [], []
        def atom(mask):
            bank.append(mask)
            assert g.rect(mask)
            return len(bank)-1
        def raw(masks):
            return sum(v for v in masks if rng.randrange(5) == 0)
        for i in range(1+trial % 15):
            # Circuit evaluator uses bitwise operations on the full grid.
            deps = [[j for j in range(i) if rng.randrange(4) == 0] for _ in range(2)]
            operands = [(raw(g.row), raw(g.col)) for _ in range(2)]
            values = []
            for (r, c), prior in zip(operands, deps):
                value = r | c
                for j in prior:
                    value |= masks[j]
                values.append(value)
            mask = values[0] & values[1]
            slots = [[atom(z) for z in arm] for arm in operands]
            pairs = {(s, t): atom(operands[0][s] & operands[1][t]) for s, t in product(range(2), repeat=2)}
            depth = 1 + max([levels[j] for arm in deps for j in arm], default=0)
            accepted = {}
            for index in range(g.rows*g.cols):
                cell = bit(index)
                if not (mask & cell):
                    continue
                selected = [next((s for s, term in enumerate(arm) if term & cell), None) for arm in operands]
                if None not in selected:
                    cert = {pairs[tuple(selected)]}
                else:
                    cert = set()
                    for e, s in enumerate(selected):
                        if s is not None:
                            cert.add(slots[e][s])
                        else:
                            prev = next(j for j in deps[e] if masks[j] & cell)
                            cert.update(witnesses[prev][index])
                rectangle = g.all
                for z in cert:
                    rectangle &= bank[z]
                assert g.rect(rectangle) and cell & rectangle and not rectangle & ~mask
                assert len(cert) <= 2**(depth-1)
                accepted[index] = cert
                successes += 1
                sizes.add(len(cert))
            masks.append(mask)
            witnesses.append(accepted)
            levels.append(depth)
        assert len(bank) == 8*len(masks)
    return successes, sorted(sizes)


if __name__ == '__main__':
    for r, c in ((3, 3), (3, 4), (4, 3)):
        n = graph_controls(Grid(r,c))
        print(f'{r} by {c}: {2**(r*c)} graphs, {n} forests, depths 1/2/3')
    print('Accepted gate/cell certificates and observed lengths:', certificate_controls())
