"""Enumerate reduced unlabelled trees and identify the restrictions of positive examples."""
from functools import lru_cache
from itertools import combinations_with_replacement, product


def partitions(total, largest):
    if total == 0:
        yield ()
    for k in range(min(total, largest), 0, -1):
        for rest in partitions(total-k, k):
            yield (k,) + rest


@lru_cache(None)
def planted(order):
    return ('()',) if order == 1 else tuple(assemble(order, order-1))


def assemble(order, largest_branch):
    for sizes in partitions(order-1, largest_branch):
        if sizes.count(1) > 1:
            continue
        multiplicities = [(s, sizes.count(s)) for s in sorted(set(sizes), reverse=True)]
        choices = [combinations_with_replacement(planted(s), count)
                   for s, count in multiplicities]
        for groups in product(*choices):
            yield '(' + ''.join(child for group in groups for child in group) + ')'


def adjacency(code):
    adj, stack = [], []
    for ch in code:
        if ch == ')':
            stack.pop()
        else:
            assert ch == '('
            vertex = len(adj)
            adj.append([])
            if stack:
                adj[vertex].append(stack[-1])
                adj[stack[-1]].append(vertex)
            stack.append(vertex)
    assert not stack
    return adj


def matrix(code):
    stack, rows, n = [], [], 0
    for ch in code:
        if ch == ')':
            stack.pop()
            continue
        if len(stack) % 2:
            vertex = n
            n += 1
            rows[stack[-1]] |= 1 << vertex
        else:
            vertex = len(rows)
            rows.append(1 << stack[-1] if stack else 0)
        stack.append(vertex)
    return rows, n


def canonical(adj):
    """Allow a deleted leaf to remain as an isolated placeholder in adj."""
    active = {i for i, ns in enumerate(adj) if ns}
    degree = list(map(len, adj))
    while len(active) > 2:
        leaves = {i for i in active if degree[i] == 1}
        assert leaves
        for i in leaves:
            for j in adj[i]:
                degree[j] -= 1
        active -= leaves

    def rooted(i, parent):
        children = sorted(rooted(j, i) for j in adj[i] if j != parent)
        return '(' + ''.join(children) + ')'
    return min(rooted(center, -1) for center in active)


def reduced_parents(code):
    adj = adjacency(code)
    for i, neighbors in enumerate(adj):
        if len(neighbors) != 1:
            continue
        v = neighbors[0]
        if len(adj[v]) == 2:
            w = next(x for x in adj[v] if x != i)
            if any(x != v and len(adj[x]) == 1 for x in adj[w]):
                continue
        adj[v].remove(i)
        adj[i] = []
        yield canonical(adj)
        adj[i] = [v]
        adj[v].append(i)


def has_positive_extension(code, exceptional):
    adj = adjacency(code)
    leaf = len(adj)
    adj.append([])
    for i in range(leaf):
        if len(adj[i]) > 1 and any(len(adj[x]) == 1 for x in adj[i]):
            continue
        adj[i].append(leaf)
        adj[leaf] = [i]
        if canonical(adj) not in exceptional:
            return True
        adj[i].pop()
        adj[leaf] = []
    return False


def exceptional_parents(exceptional):
    candidates = {p for child in exceptional for p in reduced_parents(child)}
    return {p for p in candidates if not has_positive_extension(p, exceptional)}
