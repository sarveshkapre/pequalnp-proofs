"""Bipartite forests up to component permutation and a simultaneous shore swap."""
import itertools
import re
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = HERE.parent / 'tree-bound'
TREE = runpy.run_path(str(BASE / 'trees.py'))


def colors(adj):
    side = [-1] * len(adj)
    for start in range(len(adj)):
        if side[start] != -1:
            continue
        side[start] = 0
        stack = [start]
        while stack:
            v = stack.pop()
            for w in adj[v]:
                if side[w] == -1:
                    side[w] = 1 - side[v]
                    stack.append(w)
                assert side[w] != side[v]
    return side


def pieces(adj, vertices):
    remaining = set(vertices)
    while remaining:
        start = min(remaining)
        component, stack = {start}, [start]
        while stack:
            for w in adj[stack.pop()]:
                if w not in component:
                    component.add(w)
                    stack.append(w)
        yield component
        remaining -= component


def key(adj, side):
    def rooted(v, parent):
        children = sorted(rooted(w, v) for w in adj[v] if w != parent)
        return '(' + ''.join(children) + ')'

    orientations = [[], []]
    for component in pieces(adj, (i for i, ns in enumerate(adj) if ns)):
        centers = set(component)
        while len(centers) > 2:
            leaves = {v for v in centers if sum(w in centers for w in adj[v]) == 1}
            assert leaves
            centers -= leaves
        roots = [(side[v], rooted(v, -1)) for v in centers]
        for flip in (0, 1):
            orientations[flip].append(min(str(s ^ flip) + word for s, word in roots))
    return min(''.join(sorted(words)) for words in orientations)


def decode(code):
    adj, sides, components = [], [], []
    records = re.findall(r'([01])([()]+)', code)
    assert ''.join(sign + word for sign, word in records) == code
    for sign, word in records:
        part = TREE['adjacency'](word)
        offset = len(adj)
        adj.extend([[offset + j for j in ns] for ns in part])
        sides.extend(int(sign) ^ s for s in colors(part))
        components.append(list(range(offset, len(adj))))
    return adj, sides, components


def matrix(code):
    adj, sides, _ = decode(code)
    columns = {v: j for j, v in enumerate(i for i, s in enumerate(sides) if s)}
    rows = [sum(1 << columns[j] for j in ns) for i, ns in enumerate(adj) if not sides[i]]
    return rows, len(columns)


def reduced(adj):
    supports = [ns[0] for ns in adj if len(ns) == 1]
    return len(supports) == len(set(supports))


def punctures(tree):
    """Delete one nonleaf; retain only reduced forests without new isolates."""
    adj = TREE['adjacency'](tree)
    sides = colors(adj)
    for v, neighbors in enumerate(adj):
        if len(neighbors) < 2 or any(len(adj[w]) == 1 for w in neighbors):
            continue
        adj[v] = []
        for w in neighbors:
            adj[w].remove(v)
        if reduced(adj):
            yield key(adj, sides)
        for w in neighbors:
            adj[w].append(v)
        adj[v] = neighbors


def extension(code, exceptional):
    """Return a certified supertree, or exhaust the choices on both shores."""
    adj, sides, components = decode(code)
    new = len(adj)
    adj.append([])
    for side in (0, 1):
        options = [[v for v in comp if sides[v] == side] for comp in components]
        for neighbors in itertools.product(*options):
            adj[new] = list(neighbors)
            for w in neighbors:
                adj[w].append(new)
            tree = TREE['canonical'](adj)
            if tree not in exceptional:
                return tree
            for w in neighbors:
                adj[w].pop()
    return None
