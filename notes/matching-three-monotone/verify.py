"""Gate-elimination proof for the 3-by-3 monotone Boolean permanent. Python 3.9+."""
from functools import lru_cache
from itertools import combinations, permutations, product


def variables(f):
    return sorted(set().union(*f))


def restrict(f, edge, value):
    if not value:
        return frozenset(t for t in f if edge not in t)
    terms = {t - {edge} for t in f}
    return frozenset(t for t in terms if not any(u < t for u in terms))


def minterms():
    return frozenset(frozenset(3*i+j for i, j in enumerate(cols))
                     for cols in permutations(range(3)))


SYMMETRIES = []
for row in permutations(range(3)):
    for col in permutations(range(3)):
        for transpose in (False, True):
            SYMMETRIES.append(tuple(3*col[e%3]+row[e//3] if transpose
                                    else 3*row[e//3]+col[e%3] for e in range(9)))


@lru_cache(None)
def canonical(f):
    return min(tuple(sorted(sum(1 << perm[e] for e in t) for t in f))
               for perm in SYMMETRIES)


def restrictions_by_size(root):
    todo = [root]
    classes = {}
    while todo:
        f = todo.pop()
        key = canonical(f)
        if key in classes:
            continue
        classes[key] = f
        for e in variables(f):
            todo.extend(restrict(f, e, v) for v in (0, 1))
    return sorted(classes.values(), key=lambda f: (len(variables(f)), canonical(f)))


class Verifier:
    def __init__(self, f, prior):
        edges = variables(f)
        self.n = len(edges)
        inputs = range(1 << self.n)
        self.full = (1 << len(inputs)) - 1
        self.raw = tuple(sum(1 << x for x in inputs if x >> i & 1)
                         for i in range(self.n))
        self.pos = [sum(1 << edges.index(e) for e in t) for t in f]
        negative = {x for x in inputs if not any(x & t == t for t in self.pos)}
        self.neg = sorted(x for x in negative if all((x | (1 << j)) not in negative
                          for j in range(self.n) if not x >> j & 1))
        self.all_pairs = (1 << (len(self.pos) * len(self.neg))) - 1
        self.target = self.full ^ sum(1 << x for x in negative)
        self.conditions = []
        self.cover_cache = {}
        for k in (1, 2):
            for indices in combinations(range(self.n), k):
                for values in product((0, 1), repeat=k):
                    mask = self.full
                    g = f
                    for i, value in zip(indices, values):
                        mask &= self.raw[i] if value else self.full ^ self.raw[i]
                        g = restrict(g, edges[i], value)
                    if variables(g):
                        self.conditions.append((prior[canonical(g)], mask))
        self.conditions.sort(reverse=True)

    def separates(self, wire):
        if wire not in self.cover_cache:
            self.cover_cache[wire] = sum(1 << (i * len(self.neg) + j)
                for i, positive in enumerate(self.pos) if wire >> positive & 1
                for j, negative in enumerate(self.neg) if not wire >> negative & 1)
        return self.cover_cache[wire]

    def excludes_prefix(self, wires, sinks, goal):
        covers = [self.separates(wire) for wire in wires]
        for lower_bound, mask in self.conditions:
            retained = {0, mask}
            erased = forced = free_pairs = 0
            optional = []
            for i, wire in enumerate(wires):
                value = wire & mask
                if i >= self.n and value in retained:
                    erased += 1
                retained.add(value)
                if value in (0, mask) and i not in sinks:
                    optional.append(covers[i])
                else:
                    free_pairs |= covers[i]
                    if value in (0, mask):
                        forced += 1
            needed = goal - lower_bound - erased - forced
            if needed <= 0:
                return True
            if needed > len(optional):
                continue
            missing = self.all_pairs & ~free_pairs
            # A smaller choice can always be extended to exactly needed - 1.
            for chosen in combinations(optional, needed - 1):
                uncovered = missing
                for pairs in chosen:
                    uncovered &= ~pairs
                if not uncovered:
                    break
            else:
                return True
        return False

    def establishes(self, goal, depth):
        def visit(wires, sinks):
            length = len(wires) - self.n
            if self.target in wires:
                return length >= goal
            if self.excludes_prefix(wires, sinks, goal):
                return True
            if length == depth:
                return False
            for i, j in combinations(range(len(wires)), 2):
                for output in (wires[i] & wires[j], wires[i] | wires[j]):
                    if output in wires or output in (0, self.full):
                        continue
                    if not visit(wires + (output,), (sinks - {i, j}) | {len(wires)}):
                        return False
            return True
        return visit(self.raw, set())


def upper_witness(mask):
    # Expand the permanent along the first row. Count every binary gate.
    gates = []
    def add(op, i, j):
        gates.append((op, i, j))
        return 8 + len(gates)
    pieces = []
    for first in range(3):
        j, k = (c for c in range(3) if c != first)
        p = add('and', 3+j, 6+k)
        q = add('and', 3+k, 6+j)
        minor = add('or', p, q)
        pieces.append(add('and', first, minor))
    out = add('or', add('or', pieces[0], pieces[1]), pieces[2])
    wires = [bool(mask >> i & 1) for i in range(9)]
    for op, i, j in gates:
        wires.append((wires[i] and wires[j]) if op == 'and' else (wires[i] or wires[j]))
    return len(gates), wires[out]


def main():
    root = minterms()
    prior = {}
    classes = restrictions_by_size(root)
    for f in classes:
        lower = max(0, len(variables(f)) - 1)
        if len(variables(f)) >= 3:
            checker = Verifier(f, prior)
            while lower < 14 and checker.establishes(lower + 1, 4):
                lower += 1
        prior[canonical(f)] = lower
    for mask in range(512):
        gates, value = upper_witness(mask)
        expected = any(all(mask >> e & 1 for e in t) for t in root)
        if gates != 14 or value != expected:
            raise ValueError('Upper witness failed on input ' + str(mask))
    print('Restriction classes:', len(classes))
    print('Input edge fixed absent:', prior[canonical(restrict(root, 0, 0))])
    print('Input edge fixed present:', prior[canonical(restrict(root, 0, 1))])
    print('Unrestricted monotone DAG lower bound:', prior[canonical(root)])
    print('Known 14-gate upper witness: 512/512 inputs passed')
    if prior[canonical(root)] != 14:
        raise ValueError('The lower bound did not reach fourteen')


if __name__ == '__main__':
    main()
