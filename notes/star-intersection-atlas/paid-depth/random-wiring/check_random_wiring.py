"""Replay support compilation, its monotonicity, and the exact wiring expectation."""
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import prod
from random import Random


def gate_diagram(k, pairs, labels):
    gates = [[0, 0] for _ in range(k)]
    for (source, dest), label in zip(pairs, labels):
        for arm in range(2):
            if label & (1 << arm):
                gates[dest][arm] |= 1 << source
    return gates


def legal_choices(gates, possible):
    result = []
    for i, (left, right) in enumerate(gates):
        if possible >> i & 1:
            result.append(0)  # no test at this gate
        else:
            choices = int(not (left & possible)) + 2 * int(not (right & possible))
            if choices == 0:
                return None
            result.append(choices)
    return tuple(result)


def raw_grid(k, rows, cols):
    side = len(cols)
    universe = (1 << (len(rows) * side)) - 1
    row_masks, col_masks = [], []
    for arm in range(2 * k):
        row_mask = sum(1 << i for i, word in enumerate(rows) if not word >> arm & 1)
        col_mask = sum(1 << i for i, word in enumerate(cols) if not word >> arm & 1)
        row_masks.append(row_mask)
        col_masks.append(col_mask)

    def rectangle(row, col):
        return sum(col << (side * r) for r in range(len(rows)) if row >> r & 1)

    @lru_cache(maxsize=None)
    def compiled(legal):
        if legal is None:
            return 0
        flexible = [i for i, mask in enumerate(legal) if mask == 3]
        groups = [[], []]
        for i, mask in enumerate(legal):
            if mask:
                group = int(mask == 3 and flexible.index(i) >= len(flexible) // 2)
                groups[group].append([2 * i + arm for arm in range(2) if mask >> arm & 1])
        output = universe
        for group in groups:
            union = 0
            for arms in product(*group):
                rm, cm = (1 << len(rows)) - 1, (1 << len(cols)) - 1
                for a in arms:
                    rm &= row_masks[a]
                    cm &= col_masks[a]
                union |= rectangle(rm, cm)
            output &= union
        return output

    signals = [universe ^ rectangle(rm, cm) for rm, cm in zip(row_masks, col_masks)]
    return universe, compiled, signals


def check_semantics(gates, grid):
    k = len(gates)
    universe, compiled, signals = grid
    state = [0] * k
    # All cells evaluated together from the empty state, including feedback loops.
    for _ in range(k):
        following = []
        for i, deps in enumerate(gates):
            arms = []
            for e, mask in enumerate(deps):
                value = signals[2 * i + e]
                for j in range(k):
                    if mask >> j & 1:
                        value |= state[j]
                arms.append(value)
            following.append(arms[0] & arms[1])
        state = following

    # Subset transform unions all witnesses with possible & output == 0.
    table = [compiled(legal_choices(gates, possible)) for possible in range(1 << k)]
    for i in range(k):
        for mask in range(1 << k):
            if mask >> i & 1:
                table[mask] |= table[mask ^ (1 << i)]
    all_gates = (1 << k) - 1
    for need in range(1 << k):
        actual = 0
        for i, value in enumerate(state):
            if need >> i & 1:
                actual |= value
        assert table[all_gates ^ need] == universe ^ actual


def add_polynomial(dest, source, multiplier, degree):
    for i, v in enumerate(source):
        if v:
            dest[i + degree] += v * multiplier


def exact_expectation(k, mass):
    """Coefficients of E[sum a^h] as rational numbers, using the true-count recurrence."""
    total = sum(mass)
    neither = Fraction(mass[0], total)
    miss_left = Fraction(mass[0] + mass[2], total)
    miss_right = Fraction(mass[0] + mass[1], total)
    hist = {0: [1] + [0] * k}
    for _ in range(k):
        after = {}
        for s, poly in hist.items():
            after.setdefault(s, [0] * (k + 1))
            after.setdefault(s + 1, [0] * (k + 1))
            both_clear = neither**s
            one_clear = miss_left**s + miss_right**s - 2 * both_clear
            add_polynomial(after[s], poly, one_clear, 0)
            add_polynomial(after[s], poly, both_clear, 1)
            add_polynomial(after[s + 1], poly, 1, 0)
        hist = after
    return [sum(poly[i] for poly in hist.values()) for i in range(k + 1)]


def direct_histogram(gates):
    hist = [0] * (len(gates) + 1)
    for possible in range(1 << len(gates)):
        legal = legal_choices(gates, possible)
        if legal is not None:
            hist[legal.count(3)] += 1
    return hist


def expectations():
    k = 4
    pairs = [(j, i) for i in range(k) for j in range(i)]
    # Empty, one-arm-only, independent, identical, and asymmetric arm laws.
    laws = [(1, 0, 0, 0), (2, 1, 1, 0), (1, 1, 1, 1), (1, 0, 0, 1), (1, 1, 2, 1)]
    counts = [[0] * (k + 1) for _ in laws]
    for labels in product(range(4), repeat=len(pairs)):
        hist = direct_histogram(gate_diagram(k, pairs, labels))
        for total, mass in zip(counts, laws):
            add_polynomial(total, hist, prod(mass[l] for l in labels), 0)
    for total, mass in zip(counts, laws):
        denominator = sum(mass)**len(pairs)
        assert [Fraction(v, denominator) for v in total] == exact_expectation(k, mass)
    print("All five expectation coefficients matched on all 4096 ordered four-gate wirings for each of five probability laws.")


def main():
    for k, loops in [(2, True), (3, False)]:
        pairs = [(j, i) for i in range(k) for j in range(k) if loops or j != i]
        words = list(range(1 << (2 * k)))
        grid = raw_grid(k, words, words)
        for labels in product(range(4), repeat=len(pairs)):
            check_semantics(gate_diagram(k, pairs, labels), grid)
        print(f"{4**len(pairs)} wirings, all {2**k} output sets, all {len(words)**2} row-column pairs, k={k}, self-loops={loops}.")
    rng = Random(20261126)
    checks = 0
    for k in range(3, 10):
        pairs = [(j, i) for i in range(k) for j in range(k)]
        grid = raw_grid(k, [rng.randrange(1 << (2*k)) for _ in range(12)],
                        [rng.randrange(1 << (2*k)) for _ in range(16)])
        for _ in range(28):
            lower = [rng.choice([0, 0, 0, 1, 2]) if j < i else 0 for j, i in pairs]
            upper = [label | rng.choice([0, 0, 1, 2, 3]) for label in lower]
            src = gate_diagram(k, pairs, lower)
            dst = gate_diagram(k, pairs, upper)
            for possible in range(1 << k):
                before, after = legal_choices(src, possible), legal_choices(dst, possible)
                if after is not None:
                    assert before is not None
                    assert all(a & b == b for a, b in zip(before, after))
                checks += 1
            check_semantics(dst, grid)
    print(f"196 larger feedback completions and {checks} individual support comparisons passed.")
    expectations()


if __name__ == '__main__':
    main()
