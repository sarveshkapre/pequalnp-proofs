"""Independent replay of the anchor compiler and reverse-greedy estimate."""
from itertools import product
from random import Random


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask -= bit


def graph(k, pairs, labels):
    arms = [[0, 0] for _ in range(k)]
    for (j, i), label in zip(pairs, labels):
        for e in (0, 1):
            if label & (1 << e):
                arms[i][e] |= 1 << j
    return arms


def forward(gates):
    out = [0] * len(gates)
    for i, (left, right) in enumerate(gates):
        for j in bits((left | right) & ((1 << i) - 1)):
            out[j] |= 1 << i
    return out


def neighbors(mask, out):
    result = 0
    for i in bits(mask):
        result |= out[i]
    return result


def signal(mask, gates):
    value = 0
    for i in bits(mask):
        value |= gates[i]
    return value


def raw_masks(k, words):
    return [[sum(1 << r for r, w in enumerate(words) if w >> (2*i+e) & 1)
             for e in (0, 1)] for i in range(k)]


def grid(k, rows, cols):
    def rectangle(row, col):
        return sum(col << (len(cols)*r) for r in bits(row))
    raw_r, raw_c = raw_masks(k, rows), raw_masks(k, cols)
    R, C = (1 << len(rows)) - 1, (1 << len(cols)) - 1
    raw = [[rectangle(raw_r[i][e], C) | rectangle(R, raw_c[i][e])
            for e in (0, 1)] for i in range(k)]
    return raw_r, raw_c, raw, R, C, rectangle


def solve(raw, gates, full, anchor=None):
    state = [0]*len(gates)
    for _ in gates:
        following = []
        for i, deps in enumerate(gates):
            arm = [raw[i][e] | signal(deps[e], state) for e in (0, 1)]
            if anchor is None:
                value = arm[0] & arm[1]
            elif anchor >> i & 1:
                value = full
            else:
                value = (arm[1] if deps[0] & anchor else 0) | (arm[0] if deps[1] & anchor else 0)
            following.append(value)
        state = following
    return state


def replay(gates, guaranteed, masks):
    k = len(gates)
    raw_r, raw_c, raw, R, C, rectangle = masks
    full = rectangle(R, C)
    direct = solve(raw, gates, full)
    compiled = [0] * (1 << k)
    for anchor in range(1 << k):
        touched = neighbors(anchor, guaranteed)
        if anchor & touched:
            continue
        rr = solve(raw_r, gates, R, anchor)
        cc = solve(raw_c, gates, C, anchor)
        check = full
        for i, deps in enumerate(gates):
            if (anchor >> i & 1) or (deps[0] | deps[1]) & anchor:
                continue
            terms = []
            for e in (0, 1):
                rows = R ^ (raw_r[i][e] | signal(deps[e], rr))
                cols = C ^ (raw_c[i][e] | signal(deps[e], cc))
                terms.append(rectangle(rows, cols))
            check &= terms[0] | terms[1]
        for need in range(1 << k):
            compiled[need] |= check & rectangle(R ^ signal(need, rr), C ^ signal(need, cc))
    assert all(value == full ^ signal(need, direct) for need, value in enumerate(compiled))


def greedy_estimate():
    k = 6
    pairs = [(j, i) for i in range(k) for j in range(i)]
    for number in range(1 << len(pairs)):
        out = [0] * k
        for index in bits(number):
            j, i = pairs[index]
            out[j] |= 1 << i
        alpha = lhs = rhs = 0
        for mask in range(1 << k):
            touched = neighbors(mask, out)
            if not mask & touched:
                alpha = max(alpha, mask.bit_count())
                h = (mask | touched).bit_count()
                lhs += 2**h * 3**(k-h)
            chosen = 0
            for i in reversed(range(k)):
                if mask >> i & 1 and not chosen & out[i]:
                    chosen |= 1 << i
            rhs += 2**(k-mask.bit_count()) * 3**chosen.bit_count()
        # Both expectations multiplied by 3^k at sample probability 1/3.
        assert lhs <= rhs <= 3**(k+alpha)
    print("Weighted independent-set sum and reverse-greedy estimate hold on all 32768 ordered six-vertex graphs, using integer arithmetic.")


def main():
    for k, loops in [(2, True), (3, False)]:
        pairs = [(j, i) for i in range(k) for j in range(k) if loops or j != i]
        words = list(range(1 << (2*k)))
        masks = grid(k, words, words)
        for labels in product(range(4), repeat=len(pairs)):
            g = graph(k, pairs, labels)
            replay(g, forward(g), masks)
        print(f"Anchor compiler matched least-fixed-point evaluation on {4**len(pairs)} wirings, {2**k} output sets and {len(words)**2} cells per wiring.")
    rng = Random(41671)
    for k in range(3, 9):
        pairs = [(j, i) for i in range(k) for j in range(k)]
        masks = grid(k, [rng.randrange(1 << (2*k)) for _ in range(8)],
                     [rng.randrange(1 << (2*k)) for _ in range(11)])
        for _ in range(20):
            guaranteed = [rng.choice([0, 0, 1, 2]) if j < i else 0 for j, i in pairs]
            actual = [v | rng.choice([0, 0, 1, 2, 3]) for v in guaranteed]
            replay(graph(k, pairs, actual), forward(graph(k, pairs, guaranteed)), masks)
    print("120 larger diagrams passed after extra forward wires, reverse wires and self-loops were added.")
    greedy_estimate()


if __name__ == '__main__':
    main()
