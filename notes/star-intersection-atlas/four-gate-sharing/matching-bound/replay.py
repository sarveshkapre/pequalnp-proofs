"""Finite checks for the matching-number bound and the doubled-tree obstruction."""
from collections import deque
from itertools import combinations, product
import json
from math import comb
from pathlib import Path

HERE = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def matching_size(rows):
    """Exact dynamic program over occupied columns, independently of the rooting."""
    masks = {0}
    for neighbors in rows:
        masks |= {used | (1 << j) for used in masks for j in neighbors if not used >> j & 1}
    return max(x.bit_count() for x in masks)


def layers(rows, n):
    m = len(rows)
    graph = [set(m+j for j in adj) for adj in rows]
    graph += [{i for i, adj in enumerate(rows) if j in adj} for j in range(n)]
    parent = {}
    for start in range(m+n):
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
                elif parent[v] != w and parent[w] != v:
                    return None
    return [(list(range(m)), [parent[m+j] for j in range(n)]),
            ([parent[i] for i in range(m)], list(range(m, m+n)))]


def reconstruct(rows, n, parts):
    matching = matching_size(rows)
    d = 2
    while comb(d, d//2) < matching:
        d += 1
    codes = [sum(1 << i for i in subset) for subset in combinations(range(d), d//2)]
    output = [set() for _ in rows]
    full = (1 << d)-1
    for left, right in parts:
        groups = sorted((set(left) & set(right)) - {None})
        require(len(groups) <= matching, "component count exceeds matching")
        code = dict(zip(groups, codes))
        for i, name in enumerate(left):
            row_word = code.get(name, full)
            for j, tag in enumerate(right):
                col_word = full ^ code[tag] if tag in code else full
                if row_word & col_word == 0:
                    output[i].add(j)
    require(output == list(map(set, rows)), "forest reconstruction")


def four_gate_tables():
    """All ordered circuits, including unused gates and every subset of output taps."""
    universe = (1 << 256)-1
    bits = [sum(1 << x for x in range(256) if x >> i & 1) for i in range(8)]
    tables = set()
    count = 0

    def enumerate_gates(i, meets):
        nonlocal count
        if i == 4:
            tables.update(meets)
            count += len(meets)
            return
        for left, right in product(meets, repeat=2):
            gate = (bits[2*i] & left) | (bits[2*i+1] & right)
            enumerate_gates(i+1, meets + [prior & gate for prior in meets])
    enumerate_gates(0, [universe])
    require(count == 65536 and len(tables) == 572, "wiring or table count")
    return tables


def matching_bound(table_bits):
    """Largest normalized induced matching of size at least two (smaller counts immaterial)."""
    zero = [bool(table_bits >> word & 1) for word in range(256)]
    pairs = []
    for shared in range(256):
        if zero[shared] or any(not zero[shared | (1 << b)] for b in range(8) if not shared >> b & 1):
            continue
        free = 255 ^ shared
        split = free
        while True:
            row, col = shared | split, 255 ^ split
            if zero[row] and zero[col]:
                pairs.append((row, col))
            if not split:
                break
            split = (split-1) & free
    compatible = [sum(1 << j for j, (x,y) in enumerate(pairs) if zero[r & y] and zero[x & c])
                  for r,c in pairs]
    best = 0

    def search(remaining, size):
        nonlocal best
        best = max(best, size)
        while size + remaining.bit_count() > best:
            item = remaining & -remaining
            remaining ^= item
            search(remaining & compatible[item.bit_length()-1], size+1)
    search((1 << len(pairs))-1, 0)
    return best


def double_tree():
    tree = json.loads((HERE.parent / "forest-sharpness/witness.json").read_text())["neighbors"]
    data = json.loads((HERE / "double-tree.json").read_text())
    rows, cols = data["row_words"], data["column_words"]
    require(len(rows) == len(cols) == 20 and all(0 <= w < 128 for w in rows+cols), "seven-bit words")
    edges = {(i,j) for i in range(20) for j in range(20)
             if i//10 == j//10 and j%10 in tree[i%10]}
    require(edges == {(i,j) for i,x in enumerate(rows) for j,y in enumerate(cols) if not x & y},
            "double-tree formula cells")
    selected = [(r+10*t,c+10*t) for t in range(2) for r,c in data["matching_in_one_copy"]]
    require(len(selected) == 12 and all(((r,c) in edges) == (i==j)
            for i,(r,_) in enumerate(selected) for j,(_,c) in enumerate(selected)), "induced matching")
    return len(edges)


def main():
    count = 0
    for m,n in ((3,3), (3,4), (4,3)):
        subsets = [[j for j in range(n) if mask >> j & 1] for mask in range(1 << n)]
        for rows in product(subsets, repeat=m):
            parts = layers(rows, n)
            if parts is not None:
                reconstruct(rows, n, parts)
                count += 1
    print(f"All {count} labelled forests in 3×3, 3×4 and 4×3 passed.")
    # Includes duplicate leaves, isolated vertices, the empty graph and both root orientations.
    print(f"Doubled tree: 400/400 cells, {double_tree()} edges, twelve-edge induced matching.")
    capacities = [matching_bound(table) for table in four_gate_tables()]
    require(max(capacities) == 10, "four-gate matching bound")
    require(sum(v == 10 for v in capacities) == 66, "extremal truth tables")
    # The two-element subsets of five bits and their complements realize the extremal matching.
    words = [sum(1 << i for i in s) for s in combinations(range(5), 2)]
    require(all((not (x & (31^y))) == (x == y) for x,y in product(words, repeat=2)), "ten pairs")
    print("65,536 wirings/output choices, 572 distinct tables. Maximum induced matching = 10.")
    print("Two copies therefore have circuit cost at least five and formula cost at most six.")


if __name__ == "__main__":
    main()
