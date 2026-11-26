"""Independent finite checks for the symbolic formula construction. Python 3.10+."""
from collections import deque
from itertools import product


def forest_layers(rows, cols):
    """Root every component. Return its two star-forest layers, or None on a cycle."""
    m = len(rows)
    graph = [[] for _ in range(m + cols)]
    for r, neighbors in enumerate(rows):
        for c in range(cols):
            if (neighbors >> c) & 1:
                graph[r].append(m + c)
                graph[m + c].append(r)
    parent = {}
    for start in range(len(graph)):
        if start in parent:
            continue
        parent[start] = None
        queue = deque([start])
        while queue:
            v = queue.popleft()
            for w in graph[v]:
                if w not in parent:
                    parent[w] = v
                    queue.append(w)
                elif w != parent[v] and v != parent[w]:
                    return None
    return [(list(range(m)), [parent[m + c] for c in range(cols)]),
            ([parent[r] for r in range(m)], list(range(m, m + cols)))]


def validate(rows, n, layers):
    # These synthetic codes identify distinct full rows. In the theorem the
    # supplied circuit determines the tests, without access to a decomposition.
    names = {mask: i for i, mask in enumerate(sorted(set(rows)))}
    signature = [names[mask] for mask in rows]
    bits = max(1, (len(names) - 1).bit_length())
    rep = {s: signature.index(s) for s in set(signature)}
    all_cells = {(r, c) for r in range(len(rows)) for c in range(n)}
    zeros = set(all_cells)
    for left, right in layers:
        labels = [left[rep[s]] for s in signature]
        codes = {lab: signature[r] for r, lab in enumerate(labels) if lab is not None}
        lcodes = [codes.get(label) for label in labels]
        rcodes = [codes.get(label) for label in right]
        layer_zeros = set()
        for bit, value in product(range(bits), (0, 1)):
            rowset = [r for r, s in enumerate(lcodes) if s is None or (s >> bit) & 1 == value]
            colset = [c for c, s in enumerate(rcodes) if s is None or (s >> bit) & 1 != value]
            layer_zeros.update(product(rowset, colset))
        zeros.intersection_update(layer_zeros)
    assert zeros == {(r, c) for r, c in all_cells if not (rows[r] >> c) & 1}


def main():
    # Equal global rows can have different labels in *every* original layer.
    validate([3, 3], 2, [([0, 1], [0, 1]), ([1, 0], [0, 1])])
    for m, n in [(3, 3), (3, 4), (4, 3)]:
        forests = 0
        for rows in product(range(1 << n), repeat=m):
            layers = forest_layers(rows, n)
            if layers is not None:
                validate(rows, n, layers)
                forests += 1
        print(f"{m} by {n}: verified all {forests} labelled forests")
    zeros = [117, 109, 106, 62, 126, 79, 119]
    rows = [127 ^ mask for mask in zeros]
    layers = forest_layers(rows, 7)
    assert layers is not None
    validate(rows, 7, layers)
    print("Published 7 by 7 tree and duplicate-row control passed")


if __name__ == "__main__":
    main()
