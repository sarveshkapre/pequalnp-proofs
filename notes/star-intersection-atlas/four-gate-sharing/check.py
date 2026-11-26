"""Replay the four-join classification with standard Python, including tree controls."""
from collections import Counter
from itertools import product
from pathlib import Path
import argparse
import json

HERE = Path(__file__).resolve().parent
ALL = (1 << 256) - 1
LETTERS = [sum(1 << x for x in range(256) if x >> i & 1) for i in range(8)]
# The masks are pairs of earlier-gate subsets in chronological order.
REP = {
    1: ((0, 0), (0, 0), (0, 3), (1, 2)),
    2: ((0, 0), (0, 0), (1, 2), (1, 2)),
    3: ((0, 0), (0, 1), (0, 2), (0, 3)),
    4: ((0, 0), (0, 1), (0, 3), (1, 2)),
    5: ((0, 0), (0, 1), (1, 2), (1, 2)),
}

def meet(terms):
    result = ALL
    for term in terms:
        result &= term
    return result

def circuit(arms, taps, variables):
    gates = []
    def earlier(mask):
        return meet(value for i, value in enumerate(gates) if mask >> i & 1)
    for i, (left, right) in enumerate(arms):
        gates.append((variables[2*i] & earlier(left)) |
                     (variables[2*i+1] & earlier(right)))
    return earlier(taps)

def formula(source):
    # Parse a tree with repetitions charged separately. It has no gate references.
    stream = iter(source)
    def parse(token):
        if token in 'abcdefgh':
            return LETTERS[ord(token)-ord('a')], 0
        if token in ('T', 'F'):
            return (ALL if token == 'T' else 0), 0
        assert token in ('(', '[')
        last = ')' if token == '(' else ']'
        operands = []
        for char in stream:
            if char == last:
                break
            operands.append(parse(char))
        else:
            raise ValueError('unterminated node')
        assert len(operands) >= 2
        cost = sum(k for _, k in operands)
        if token == '(':
            return meet(v for v, _ in operands), cost
        value = 0
        for v, _ in operands:
            value |= v
        return value, cost + len(operands) - 1
    result = parse(next(stream))
    assert next(stream, None) is None
    return result

def wiring_keys():
    # Independently enumerate ordered circuits and all nonempty output masks.
    # Walk back from the output, then forget the order of the two arms.
    seen = set()
    pairs = [list(product(range(1 << i), repeat=2)) for i in range(4)]
    for wiring in product(*pairs):
        for taps in range(1, 16):
            reached = {i for i in range(4) if taps >> i & 1}
            for i in (3, 2, 1, 0):
                if i in reached:
                    reached.update(j for j in range(i)
                                   if any(mask >> j & 1 for mask in wiring[i]))
            if len(reached) == 4:
                seen.add((tuple(tuple(sorted(p)) for p in wiring), taps))
    return seen

def boundary(value):
    positive, negative = [], []
    for x in range(256):
        result = value >> x & 1
        flipped = (x ^ (1 << i) for i in range(8) if (x >> i & 1) == result)
        if all((value >> y & 1) != result for y in flipped):
            if result:
                positive.append(x)
            else:
                negative.append(x)
    return positive, negative

def check_witnesses():
    missing = wiring_keys()
    costs, exceptions = Counter(), Counter()
    for row in (HERE/'witnesses.txt').read_text().splitlines():
        *digits, perm, expression = row.split()
        *arms, taps, label = map(int, digits)
        wiring = tuple(zip(arms[::2], arms[1::2], strict=True))
        missing.remove((wiring, taps))
        expected = circuit(wiring, taps, LETTERS)
        actual, cost = formula(expression)
        assert actual == expected and cost <= 6
        costs[cost] += 1
        if cost <= 5:
            assert label == -1 and perm == '-'
        else:
            assert sorted(perm) == list('01234567')
            assert expected == circuit(REP[label], 12, [LETTERS[int(j)] for j in perm])
            exceptions[label] += 1
    assert not missing
    assert costs == {4: 5811, 5: 1186, 6: 40}
    assert exceptions == {1: 10, 2: 5, 3: 10, 4: 10, 5: 5}
    # The five histograms differ, hence no two representatives are renamings.
    signatures = set()
    for wiring in REP.values():
        pos, _ = boundary(circuit(wiring, 12, LETTERS))
        signatures.add(tuple(sorted(sum(x >> i & 1 for x in pos) for i in range(8))))
    assert len(signatures) == len(REP)
    print('7037 live wirings; 6997 witnesses of cost <=5; 40 of cost 6 in 5 classes.')

def check_hosts():
    for case, wiring in REP.items():
        value = circuit(wiring, 12, LETTERS)
        # The host edge at (r,c) is the complement of the circuit's zero-cell output.
        rows = [sum((1 ^ (value >> (r & c) & 1)) << c for c in range(256))
                for r in range(256)]
        labels = sorted(set(rows))
        # Match strict inclusions between left and right copies of the row types.
        neighbors = [[j for j, b in enumerate(labels) if a != b and a & b == a]
                     for a in labels]
        predecessor = {}
        def augment(x, visited):
            for y in neighbors[x]:
                if y in visited:
                    continue
                visited.add(y)
                if y not in predecessor or augment(predecessor[y], visited):
                    predecessor[y] = x
                    return True
            return False
        for x in range(len(labels)):
            augment(x, set())
        successor = {x:y for y,x in predecessor.items()}
        chains = []
        for x in range(len(labels)):
            if x in predecessor:
                continue
            chain = [labels[x]]
            while x in successor:
                x = successor[x]
                chain.append(labels[x])
            assert all(a != b and a & b == a for a,b in zip(chain, chain[1:]))
            chains.append(chain)
        assert sorted(v for chain in chains for v in chain) == labels
        # An explicit chain partition alone certifies the upper bound used by the proof.
        count, ceiling = (70,26) if case in (1,2,3) else (74,28)
        assert (len(labels), len(chains)) == (count,ceiling)
        print(f"Class {case}: {count} host types, {ceiling} inclusion chains, "
              f"at most {2*ceiling} vertices per side in a twin-reduced tree.")

def tree_controls():
    controls = json.loads((HERE/'trees.json').read_text())
    assert sorted(case['class'] for case in controls) == sorted(REP)
    for case in controls:
        rows, cols, graph = case['rows'], case['cols'], case['edges']
        assert len(graph) == len(rows) and all(0 <= x < 256 for x in rows + cols)
        assert all(0 <= x < (1 << len(cols)) for x in graph)
        size = len(rows) + len(cols)
        parent = list(range(size))
        def root(v):
            while parent[v] != v:
                v = parent[v]
            return v
        edges = 0
        truth = circuit(REP[case['class']], 12, LETTERS)
        for i, r in enumerate(rows):
            for j, col_label in enumerate(cols):
                wanted = graph[i] >> j & 1
                assert (1 ^ (truth >> (r & col_label) & 1)) == wanted
                a,b,c,d,e,f,g,h,k = [
                    bool((row_mask >> i & 1) and (col_mask >> j & 1))
                    for row_mask,col_mask in case['rectangles']
                ]
                zero = (((a or b) and (c or d)) or e) and (f or g) and (h or k)
                assert (not zero) == wanted
                if wanted:
                    u,v = root(i), root(len(rows)+j)
                    assert u != v
                    parent[u] = v
                    edges += 1
        assert edges == size-1 and len({root(v) for v in range(size)}) == 1
        print(f"Class {case['class']}: {len(rows)}x{len(cols)} tree, {edges} edges, five-gate witness.")

if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError("This checker requires Python assertions to be enabled.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--boundary', action='store_true', help='emit input for exact.cpp')
    if parser.parse_args().boundary:
        for i, wiring in REP.items():
            positive, negative = boundary(circuit(wiring, 12, LETTERS))
            print(i, len(positive), len(negative), *positive, *negative)
    else:
        check_witnesses()
        check_hosts()
        tree_controls()
