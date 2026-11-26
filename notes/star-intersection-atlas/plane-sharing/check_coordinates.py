"""Independent finite controls for the coordinate-circuit cost argument. Standard library only."""
from itertools import combinations, product


def reciprocal_mod(value, prime, bits):
    """One multiplication by a fixed reciprocal and one correction."""
    assert 0 <= value < 1 << bits
    estimate = (value * ((1 << bits) // prime)) >> bits
    residue = value - estimate * prime
    assert 0 <= residue < 2 * prime
    return residue - prime if residue >= prime else residue


def convolution(left, right, prime, bits):
    def pack(coefficients):
        return sum(value << (bits * i) for i, value in enumerate(coefficients))

    packed = pack(left) * pack(right)
    mask = (1 << bits) - 1
    return [reciprocal_mod((packed >> (bits * i)) & mask, prime, bits)
            for i in range(len(left) + len(right) - 1)]


def reciprocal_polynomial(modulus, prime):
    degree = len(modulus) - 1
    reverse = modulus[::-1]
    assert reverse[0] == 1
    inverse = [1]
    for j in range(1, degree):
        inverse.append(-sum(reverse[i] * inverse[j-i] for i in range(1, j+1)) % prime)
    return inverse


def fast_remainder(raw, modulus, inverse, prime, bits):
    degree = len(modulus) - 1
    padded = list(raw) + [0] * (2 * degree - len(raw))
    high = padded[::-1][:degree]
    quotient = convolution(high, inverse, prime, bits)[:degree][::-1]
    multiple = convolution(quotient, modulus, prime, bits)
    difference = [(a-b) % prime for a, b in zip(padded, multiple)]
    assert all(value == 0 for value in difference[degree:])
    return tuple(difference[:degree])


def schoolbook(left, right, modulus, prime):
    degree = len(modulus) - 1
    work = [0] * (2 * degree - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            work[i+j] += a*b
    for i in range(len(work)-1, degree-1, -1):
        factor = work[i] % prime
        for j, coefficient in enumerate(modulus):
            work[i-degree+j] -= factor * coefficient
    return tuple(value % prime for value in work[:degree])


def run_plane(prime, modulus):
    degree = len(modulus) - 1
    order = prime ** degree
    bits = (8*(degree+1)*prime**2).bit_length()
    inverse = reciprocal_polynomial(modulus, prime)
    elements = list(product(range(prime), repeat=degree))
    index = {a: i for i, a in enumerate(elements)}
    zero = (0,) * degree
    one = (1,) + zero[1:]
    # Exercise even inputs with the largest degree allowed by the reversal formula.
    for i in range(2 * degree):
        raw = [0] * (2 * degree)
        raw[i] = 1
        rem = fast_remainder(raw, modulus, inverse, prime, bits)
        for j in range(2*degree-1, degree-1, -1):
            factor = raw[j] % prime
            for h, value in enumerate(modulus):
                raw[j-degree+h] -= factor*value
        assert rem == tuple(v % prime for v in raw[:degree])
    conv, times, plus = {}, {}, {}
    for i, a in enumerate(elements):
        for j, b in enumerate(elements):
            conv[i,j] = convolution(a, b, prime, bits)
            slow = schoolbook(a, b, modulus, prime)
            assert fast_remainder(conv[i,j], modulus, inverse, prime, bits) == slow
            times[i,j] = index[slow]
            plus[i,j] = index[tuple((u+v) % prime for u, v in zip(a, b))]
        if a != zero:
            assert len({times[i,j] for j in range(order)}) == order
    o, u = index[zero], index[one]
    vectors = ([(u,a,b) for a in range(order) for b in range(order)]
               + [(o,u,a) for a in range(order)] + [(o,o,u)])
    rows = []
    for point in vectors:
        support = set()
        for j, line in enumerate(vectors):
            pairs = list(zip(point, line))
            raw = [sum(values) % prime for values in zip(*(conv[pair] for pair in pairs))]
            fast = fast_remainder(raw, modulus, inverse, prime, bits) == zero
            a,b,c = [times[pair] for pair in pairs]
            slow = plus[plus[a,b],c] == o
            assert fast == slow
            if fast:
                support.add(j)
        assert len(support) == order+1
        rows.append(support)
    assert len(rows) == order*order + order + 1
    assert all(sum(i in row for row in rows) == order+1 for i in range(len(rows)))
    assert all(len(a & b) == 1 for a,b in combinations(rows, 2))
    print(f"q={order}: all {len(rows)**2} incidences, all scalar products and Gram entries passed")
    return len(rows)**2


if __name__ == "__main__":
    # Coefficients in ascending order. The independent permutation check above
    # certifies that each quotient really is a field for these finite controls.
    fields = [(2,[0,1]), (3,[0,1]), (2,[1,1,1]), (5,[0,1]), (7,[0,1]),
              (2,[1,1,0,1]), (3,[1,0,1]), (11,[0,1]), (13,[0,1]), (2,[1,1,0,0,1])]
    for p in (2,3,5,7,11,13):
        for b in (8,12):
            assert all(reciprocal_mod(c,p,b) == c % p for c in range(1 << b))
    total = sum(run_plane(p,g) for p,g in fields)
    print(f"Passed {total} point-line pairs across {len(fields)} fields.")
