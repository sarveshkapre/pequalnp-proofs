"""Independent finite controls for the shared-bank and tensor arguments."""
from functools import lru_cache
from itertools import combinations, product
from random import Random


def cell_set(words, predicate):
    return sum(1 << (i * len(words) + j) for i, x in enumerate(words)
               for j, y in enumerate(words) if predicate(x, y))


def join(values):
    value = 0
    for piece in values:
        value |= piece
    return value


def popcount(value):
    return bin(value).count("1")


def exact_cover(sets, target):
    maximal = sorted(set(sets) - {0}, key=popcount, reverse=True)
    keep = []
    for candidate in maximal:
        if all(candidate & ~other for other in keep):
            keep.append(candidate)
    support = {1 << i: [a for a in keep if a & (1 << i)]
               for i in range(target.bit_length()) if target & (1 << i)}

    @lru_cache(None)
    def opt(left):
        if not left:
            return 0
        choices = min((items for cell, items in support.items() if left & cell), key=len)
        return 1 + min(opt(left & ~a) for a in choices)

    return opt(target)


def depth_one():
    words = list(product(range(2), repeat=2))
    strips = [[cell_set(words, lambda x, y: (mask >> words.index(pair(x, y))) & 1)
               for mask in range(1 << len(words))]
              for pair in (lambda x, y: x, lambda x, y: y)]
    arms = {a | b for a in strips[0] for b in strips[1]}
    gates = {a & b for a in arms for b in arms}
    targets = [cell_set(words, lambda x, y: all(x[i] == y[i] for i in range(2) if q >> i & 1))
               for q in (1, 2, 3)]
    for family in range(8):
        active = [(j, t) for j, t in enumerate(targets) if family >> j & 1]
        all_cells = join(t << (16*j) for j, t in active)
        contributions = [join(gate << (16*j) for j, t in active if not gate & ~t)
                         for gate in gates]
        expected = sum(((1 << popcount(j+1)) + 1) // 2 for j, _ in active)
        assert exact_cover(contributions, all_cells) == expected
    print(f"Depth one: all {len(gates)} distinct gates on the 4x4 grid; exact optima for eight families.")


def shared_circuits():
    rng = Random(9917)
    words = list(range(4))
    full = (1 << 16) - 1
    for _ in range(128):
        wires, depths, bank = [], [], {full}
        for i in range(6):
            arm_values, raw_strips, dependencies = [], [], []
            for _arm in range(2):
                row, col = rng.randrange(16), rng.randrange(16)
                strips = [cell_set(words, lambda x, y: row >> x & 1),
                          cell_set(words, lambda x, y: col >> y & 1)]
                deps = [j for j in range(i) if rng.randrange(4) == 0]
                arm_values.append(join(strips + [wires[j] for j in deps]))
                raw_strips.append(strips)
                dependencies.extend(deps)
            bank.update(raw_strips[0] + raw_strips[1])
            bank.update(a & b for a in raw_strips[0] for b in raw_strips[1])
            wires.append(arm_values[0] & arm_values[1])
            depths.append(1 + max((depths[j] for j in dependencies), default=0))
        assert len(bank) <= 8*len(wires)+1
        for _layer in range(1, max(depths)):
            bank = {a & b for a in bank for b in bank}
        for mask in range(1 << len(wires)):
            target = join(w for j, w in enumerate(wires) if mask >> j & 1)
            assert join(tile for tile in bank if not tile & ~target) == target
    print("Common bank: 128 shared circuits, all 64 gate-tap selections in each.")


def blocks(g, n, m):
    u, r = divmod(g, m)
    base = 1
    while base**m < n:
        base += 1
    for j in range(m):
        whole = [(i, 0, n) for i in range(j*u, (j+1)*u)]
        digits = [(m*u+i, base**j, base) for i in range(r)]
        yield whole + digits


def project(word, part):
    return tuple(-1 if word[i] == -1 else word[i] if divisor == 0
                 else (word[i] // divisor) % radix for i, divisor, radix in part)


def block_controls():
    cells = 0
    for g, n, m in [(2, 2, 1), (3, 3, 2), (2, 4, 2), (2, 5, 4), (1, 3, 4)]:
        words = list(product(range(n), repeat=g))
        wild = list(product(range(-1, n), repeat=g))
        parts = list(blocks(g, n, m))
        for q in range(1 << g):
            encoded = []
            for part in parts:
                selected = [item for item in part if q >> item[0] & 1]
                codes = [project(w, selected) for w in words]
                encoded.append(join(cell_set(list(range(len(words))),
                                             lambda x, y: codes[x] == z == codes[y])
                                    for z in set(codes)))
            result = (1 << len(words)**2) - 1
            for block in encoded:
                result &= block
            expected = cell_set(words, lambda x, y: all(x[i] == y[i] for i in range(g) if q >> i & 1))
            assert result == expected
            cells += len(words)**2
        result = (1 << len(wild)**2) - 1
        for part in parts:
            codes = [project(w, part) for w in wild]
            bank = []
            for completion in product(*(range(item[2]) for item in part)):
                shore = [all(a == -1 or a == b for a, b in zip(code, completion)) for code in codes]
                bank.append(cell_set(list(range(len(wild))), lambda x, y: shore[x] and shore[y]))
            result &= join(bank)
        assert result == cell_set(wild, lambda x, y: all(a == -1 or b == -1 or a == b for a,b in zip(x,y)))
        cells += len(wild)**2
    print(f"Balanced constructors: {cells} selected-mask and independently wildcarded cells, including unused codes.")


def crown():
    labels = list(range(4))
    target = cell_set(labels, lambda x, y: x != y)
    rects = {cell_set(labels, lambda x, y: (a >> x & 1) and (b >> y & 1))
             for a in range(16) for b in range(16) if not a & b}
    assert max(popcount(r) for r in rects) == 4
    assert exact_cover(rects, target) == 4
    cuts = list(combinations(labels, 2))
    for g in (1, 2):
        words = list(product(labels, repeat=g))
        cover = [cell_set(words, lambda x, y: all(x[i] in cut and y[i] not in cut
                                                  for i, cut in enumerate(box)))
                 for box in product(cuts, repeat=g)]
        for j, (x,y) in enumerate(product(words, repeat=2)):
            assert sum(r >> j & 1 for r in cover) == (2**g if all(a != b for a,b in zip(x,y)) else 0)
        assert len(cover) == 6**g
    print("Four-label disequality: integral optimum 4, fractional certificates 3 and 9 on one and two copies.")


if __name__ == "__main__":
    depth_one()
    shared_circuits()
    block_controls()
    crown()
