"""Exercise the weighted ordering and the separator used for general formulas."""
from collections import deque
from heapq import heapify, heappop, heappush
from itertools import product
from math import ceil, log2
from random import Random


def tree_from_word(word):
    n = len(word) + 2
    graph = [set() for _ in range(n)]
    degree = [1] * n
    for vertex in word:
        degree[vertex] += 1
    leaves = [v for v, d in enumerate(degree) if d == 1]
    heapify(leaves)
    for v in word:
        w = heappop(leaves)
        graph[v].add(w)
        graph[w].add(v)
        degree[v] -= 1
        if degree[v] == 1:
            heappush(leaves, v)
    u, v = leaves
    graph[u].add(v)
    graph[v].add(u)
    return graph


def component(graph, start, allowed):
    found = {start}
    stack = [start]
    while stack:
        for w in (graph[stack.pop()] & allowed) - found:
            found.add(w)
            stack.append(w)
    return found


def pieces(graph, vertices):
    unseen = set(vertices)
    while unseen:
        block = component(graph, min(unseen), unseen)
        unseen -= block
        yield block


def order_graph(graph, inside):
    out = []
    def visit(vertices):
        for block in pieces(graph, vertices):
            def maximum_branch(v):
                return max((len(part) for part in pieces(graph, block-{v})), default=0)
            center = min(block, key=lambda v: (maximum_branch(v),v))
            assert 2*maximum_branch(center) <= len(block)
            out.append(center)
            visit(block-{center})
    visit(inside)
    return out


def verify(graph, roots):
    children = [set() for _ in graph]
    todo = deque((r,None) for r in roots)
    while todo:
        v, p = todo.popleft()
        children[v] = graph[v]-{p}
        todo.extend((w,v) for w in children[v])
    internal = {v for v,ch in enumerate(children) if ch}
    order = [v for v in roots if not children[v]]
    for v in order_graph(graph, internal):
        order.append(v)
        order.extend(sorted(children[v]-internal))
    assert sorted(order) == list(range(len(graph)))
    t = len(internal)
    limit = ceil(log2(t+1))+1
    frontiers = []
    for pos in range(len(order)+1):
        earlier, later = set(order[:pos]), set(order[pos:])
        frontier = {v for v in earlier if graph[v] & later}
        assert len(frontier) <= limit
        frontiers.append(frontier)
    # Rational weight 3/4 for internal vertices, 1 for leaves; multiplying by
    # four makes cut placement and all size checks exact integer arithmetic.
    weights = [3 if v in internal else 4 for v in order]
    total = sum(weights)
    cum = [0]
    for w in weights:
        cum.append(cum[-1]+w)
    for m in (2,4,8):
        cuts = [next(i for i,x in enumerate(cum) if x*m >= total*j) for j in range(1,m)]
        sep = set().union(*(frontiers[i] for i in cuts))
        labels = {}
        for z,(i,j) in enumerate(zip([0]+cuts,cuts+[len(order)])):
            V = set(order[i:j])-sep
            for v in V:
                labels[v] = z
            local = {v for v in V if children[v] & V}
            assert len(internal & V) - len(local) <= len(sep)
            assert (4*len(V)-len(local))*m <= total + 4*m + len(sep)*m
        assert all(labels[v] == labels[w] for v in labels for w in graph[v] if w in labels)


if __name__ == '__main__':
    runs = 0
    for n in range(2,7):
        for word in product(range(n),repeat=n-2):
            graph = tree_from_word(word)
            for r in range(n):
                verify(graph,[r])
                runs += 1
    rng = Random(858993)
    for n in (10,24,56):
        for trial in range(20):
            graph = tree_from_word([rng.randrange(n) for _ in range(n-2)])
            for v in range(n):
                if rng.randrange(7) == 0 and graph[v]:
                    w = min(graph[v])
                    graph[v].remove(w)
                    graph[w].remove(v)
            verify(graph, [min(block) for block in pieces(graph,range(n))])
            runs += 1
    print(f'{runs} rooted forests checked at 2, 4 and 8 blocks; frontier, weights, and cut-edge assertions passed')
