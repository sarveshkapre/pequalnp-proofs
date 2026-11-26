"""Exact finite controls for the arbitrary-budget proof. Python 3, standard library."""
from itertools import product

BASE = [(61, 46), (57, 62), (59, 54), (27, 47),
        (62, 45), (58, 61), (47, 30), (53, 57)]


def circuit(word, k):
    shared = bool(word & 3)
    for gate in range(1, k):
        pair = (word >> (2 * gate)) & 3
        if not (pair & 1 or (shared and pair & 2)):
            return False
    return True


def formula(word, k):
    pairs = [(word >> (2 * gate)) & 3 for gate in range(1, k)]
    return all(pair & 1 for pair in pairs) or (bool(word & 3) and all(pairs))


def active_witness(k):
    full = (1 << (2 * k)) - 1
    tail = full ^ 63
    pairs = [(r | tail, c | tail) for r, c in BASE]
    for gate in range(3, k):
        u = full ^ (1 << (2 * gate))
        v = full ^ (2 << (2 * gate))
        pairs.extend([(u, v), (v, u)])
    assert len(pairs) == len(set(pairs)) == 2 * k + 2
    for i, (row, col) in enumerate(pairs):
        assert circuit(row, k) and circuit(col, k)
        assert not circuit(row & col, k)
        for other_row, other_col in pairs[:i]:
            assert circuit(row & other_col, k) or circuit(other_row & col, k)
    return len(pairs)


def coefficients(values):
    """Boolean-lattice inversion, evaluated independently of the closed polynomial."""
    result = list(map(int, values))
    stride = 1
    while stride < len(result):
        for start in range(0, len(result), 2 * stride):
            for low in range(start, start + stride):
                result[low + stride] -= result[low]
        stride *= 2
    return result


def binary_rank(rows):
    """Exact GF(2) elimination. Independence here implies real independence for these integer minors."""
    basis = {}
    for row in rows:
        while row:
            pivot = row.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = row
                break
            row ^= basis[pivot]
    return len(basis)


def max_formula(k):
    """All binary formula shapes, allowing arbitrary free meets; rectangle clips cannot increase term counts.

    Collapsing a free meet with a zero-cost subtree leaves its bound unchanged.
    The recursion records the maximal counts for all shapes and for nested shapes.
    """
    maximum, nested = [1], [0]
    for cost in range(1, k + 1):
        all_candidates, nested_candidates = [], [0]
        for i in range(cost):
            j = cost - 1 - i
            x, y = maximum[i], maximum[j]
            terms = x + y + x * y
            all_candidates.append(terms)
            if i or j:
                nested_candidates.append(terms)
        for i in range(1, cost):
            j = cost - i
            all_candidates.append(maximum[i] * maximum[j])
            nested_candidates.append(nested[i] * maximum[j])
        maximum.append(max(all_candidates))
        nested.append(max(nested_candidates))
    return maximum, nested


def normalized_controls(k):
    """Enumerate every normalized dependency pattern through three paid gates on independent raw coordinates."""
    words = 1 << (2*k)
    universe = (1 << words) - 1
    bits = [sum(1 << w for w in range(words) if w & (1 << i)) for i in range(2*k)]
    tested = 0
    best_nonflat = 0
    def visit(wires, flat):
        nonlocal tested, best_nonflat
        i = len(wires)
        ports = [universe]
        for previous in wires:
            ports += [entry & previous for entry in ports]
        if i == k:
            for output in ports:
                poly = coefficients([(output >> w) & 1 for w in range(words)])
                rank = sum(v != 0 for v in poly)
                assert rank <= 3**k
                if output != flat:
                    assert rank <= 3**k - 2
                    best_nonflat = max(best_nonflat, rank)
                tested += 1
            return
        a, b = bits[2*i:2*i+2]
        for l, r in product(ports, repeat=2):
            visit(wires+[(l & a) | (r & b)], flat & (a | b))
    visit([], universe)
    return tested, best_nonflat


def main():
    if not __debug__:
        raise RuntimeError("Run with assertions enabled.")
    for k in range(1, 4):
        total, maximum = normalized_controls(k)
        print(f"Normalized circuits k={k}: {total} wirings and output selections, largest non-flat rank {maximum}.")
    all_bounds, nested = max_formula(32)
    for k in range(2, 33):
        assert all_bounds[k] == 3**k and nested[k] == 7*3**(k-2)
    print("All formula term-count optima through cost 32 match the flat and nested bounds.")
    for k in range(3, 9):
        size = 1 << (2*k)
        values = [circuit(w, k) for w in range(size)]
        assert all(value == formula(w, k) for w, value in enumerate(values))
        support = sum(x != 0 for x in coefficients(values))
        assert support == 3**k - 2
        if k <= 5:
            rank = binary_rank(sum(1 << c for c in range(size) if values[r & c]) for r in range(size))
            assert rank == support
        print(f"k={k}: {support} nonzero coefficients on {size} input words; {active_witness(k)} fooling edges.")
    for k in (9, 16, 32, 64):
        active_witness(k)
    print("Fooling sets also verified at k=9,16,32,64; direct GF(2) matrix ranks at k=3,4,5.")


if __name__ == "__main__":
    main()
