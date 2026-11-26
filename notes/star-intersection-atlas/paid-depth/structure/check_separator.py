"""Compare the separator construction with direct evaluation of every cell."""
from itertools import product
from math import prod
from random import Random


def split_masks(mask, width):
    return [index for index in range(width) if mask & (1 << index)]


def compare(gates, groups, outputs, row_masks, col_masks, out_row, out_col, blocks, side=None):
    k = len(gates)
    if side is None:
        side = 1 << (2 * k)
    full = (1 << side) - 1
    sep = [i for i in range(k) if groups[i] == -1]
    interiors = [[i for i in range(k) if groups[i] == z] for z in range(blocks)]
    for i, arms in enumerate(gates):
        for deps in arms:
            if any(groups[j] != groups[i] and -1 not in (groups[i], groups[j]) for j in deps):
                return False

    # Evaluate source on each row as a bit set of columns.
    desired = []
    for x in range(side):
        values = []
        for i, arms in enumerate(gates):
            hits = []
            for e, deps in enumerate(arms):
                value = full if row_masks[2*i+e] >> x & 1 else col_masks[2*i+e]
                for j in deps:
                    value |= values[j]
                hits.append(value)
            values.append(hits[0] & hits[1])
        result = full if out_row >> x & 1 else out_col
        for j in outputs:
            result |= values[j]
        desired.append(full ^ result)

    actual = [0] * side
    for states in product((-1, 0, 1), repeat=len(sep)):
        sig = dict(zip(sep, states))
        seeds = set(outputs)
        raw_row, raw_col = out_row, out_col
        for i, e in sig.items():
            if e >= 0:
                seeds.update(gates[i][e])
                raw_row |= row_masks[2*i+e]
                raw_col |= col_masks[2*i+e]
        if any(sig[i] < 0 for i in seeds.intersection(sep)):
            continue
        combined = [full] * side
        for nodes in interiors:
            union = [0] * side
            for bits in product((0, 1), repeat=len(nodes)):
                row, col = raw_row, raw_col
                demand = seeds.copy()
                for i, e in reversed(tuple(zip(nodes, bits))):
                    if i in demand:
                        row |= row_masks[2*i+e]
                        col |= col_masks[2*i+e]
                        demand.update(gates[i][e])
                if any(sig[i] < 0 for i in demand.intersection(sep)):
                    continue
                for x in split_masks(full ^ row, side):
                    union[x] |= full ^ col
            combined = [left & right for left, right in zip(combined, union)]
        actual = [left | right for left, right in zip(actual, combined)]
    assert actual == desired, (gates, groups, outputs)
    return True


def raw_masks(k):
    side = 1 << (2*k)
    return [sum(1 << x for x in range(side) if x >> i & 1) for i in range(2*k)]


def exhaust():
    k = 3
    masks = raw_masks(k)
    full = (1 << (1 << (2*k))) - 1
    count = 0
    for shape in product(*(range(1 << i) for i in range(k) for _ in range(2))):
        gates = [tuple(split_masks(shape[2*i+e], i) for e in (0, 1)) for i in range(k)]
        for groups in product((-1,0,1), repeat=k):
            for out in range(1 << k):
                count += compare(gates, groups, split_masks(out,k), masks, masks,
                                 1 if out % 2 else 0, full >> 3 if out % 3 else 0, 2)
    print(f'{count} admissible three-gate DAG, partition and output cases on the full 64 by 64 raw grid')
    return count


def formula_controls():
    checked = 0
    traced = 0
    # For each paid node choose the output or one arm of exactly one later parent.
    for k in range(8):
        for assignments in product(*(range(1+2*(k-1-i)) for i in range(k))):
            arms = [[[],[]] for _ in range(k)]
            roots = []
            for i, code in enumerate(assignments):
                if code == 0:
                    roots.append(i)
                else:
                    parent = i + 1 + (code-1)//2
                    arms[parent][(code-1)%2].append(i)
            sizes = []
            for a,b in arms:
                sizes.append(prod(sizes[j] for j in a) + prod(sizes[j] for j in b))
            certificates = prod(sizes[j] for j in roots)
            nonleaves = sum(bool(a or b) for a,b in arms)
            assert certificates * 4**nonleaves <= (2**k)*3**nonleaves
            if k <= 5:
                records = set()
                for word in product((0,1),repeat=k):
                    live = set(roots)
                    for i in reversed(range(k)):
                        if i in live:
                            live.update(arms[i][word[i]])
                    records.add(tuple(word[i] if i in live else -1 for i in range(k)))
                assert len(records) == certificates
                traced += 1
            checked += 1
    print(f'{checked} ordered formula wirings through seven gates satisfied the integer certificate bound')
    print(f'{traced} formulas through five gates also matched independent backward trace enumeration')


def larger_controls():
    rng = Random(636294)
    tested = 0
    for trial in range(1400):
        k = rng.randrange(11)
        blocks = 1 + trial % 4
        side = 9
        groups = [rng.randrange(-1,blocks) for _ in range(k)]
        gates = []
        for i in range(k):
            neighbors = [j for j in range(i) if groups[i]==groups[j] or -1 in (groups[i],groups[j])]
            gates.append([tuple(j for j in neighbors if rng.randrange(3)==0) for _ in (0,1)])
        def raw():
            return 0 if rng.randrange(2) else rng.getrandbits(side)
        rows = [raw() for _ in range(2*k)]
        cols = [raw() for _ in range(2*k)]
        outputs = [j for j in range(k) if rng.randrange(3)==0]
        assert compare(gates,groups,outputs,rows,cols,raw(),raw(),blocks,side)
        tested += 1
    assert not compare([((),()),((0,),())],[0,1],[1],[0]*4,[0]*4,0,0,2,1)
    print(f'{tested} arbitrary interleaved sources through ten gates and four blocks matched direct evaluation')


if __name__ == '__main__':
    assert exhaust() > 0
    formula_controls()
    larger_controls()
