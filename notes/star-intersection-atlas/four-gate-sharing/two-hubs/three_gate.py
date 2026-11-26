"""Decide the three-gate lower bound by embedding into the scalar wiring hosts."""
from functools import lru_cache
from itertools import combinations_with_replacement, product


def members(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def hosts():
    universe = (1 << 64) - 1
    inputs = [sum(1 << word for word in range(64) if word >> i & 1) for i in range(6)]
    choices = [list(combinations_with_replacement(range(1 << i), 2)) for i in range(3)]
    seen = set()
    for arms in product(*choices):
        gates = []

        def meet(mask):
            result = universe
            for k in members(mask):
                result &= gates[k]
            return result

        for i, (left, right) in enumerate(arms):
            gates.append((inputs[2*i] & meet(left)) | (inputs[2*i+1] & meet(right)))
        for taps in range(4, 8):
            truth = meet(taps)
            if truth in seen:
                continue
            seen.add(truth)
            types = {}
            for r in range(64):
                signature = tuple((truth >> (r & c)) & 1 for c in range(64))
                types.setdefault(signature, r)
            yield tuple(sum((1 - ((truth >> (r & c)) & 1)) << j
                            for j, c in enumerate(types.values())) for r in types.values())


def fits(host, target):
    """Exact cell constraints. Each row or column may use any host type."""
    n = len(target)
    full = (1 << len(host)) - 1
    neighbors = list(target) + [sum(((target[r] >> c) & 1) << r for r in range(n))
                                for c in range(n)]

    @lru_cache(maxsize=4096)
    def support(domain, edge):
        word = 0
        for i in members(domain):
            word |= host[i] if edge else full ^ host[i]
        return word

    def visit(domains, changed):
        while changed:
            i = changed.pop()
            offset = n if i < n else 0
            allowed = (support(domains[i], False), support(domains[i], True))
            for j in range(n):
                neighbor = offset + j
                new = domains[neighbor] & allowed[(neighbors[i] >> j) & 1]
                if not new:
                    return False
                if new != domains[neighbor]:
                    domains[neighbor] = new
                    changed.add(neighbor)
        undecided = [i for i, d in enumerate(domains) if d & (d - 1)]
        if not undecided:
            return True
        i = min(undecided, key=lambda j: domains[j].bit_count())
        for value in members(domains[i]):
            trial = domains.copy()
            trial[i] = 1 << value
            if visit(trial, {i}):
                return True
        return False

    return visit([full] * (2*n), set(range(2*n)))


def verify(rows):
    graphs = set(hosts())
    assert len(graphs) == 14
    for graph in graphs:
        k = min(5, len(graph))
        assert fits(graph, [r & ((1 << k) - 1) for r in graph[:k]])
        assert not fits(graph, rows)
    assert any(fits(graph, [1 << i for i in range(6)]) for graph in graphs)
    print('16-vertex tree: all three-gate hosts excluded; positive controls passed.')
