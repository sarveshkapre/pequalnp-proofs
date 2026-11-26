"""Exercise a bounded-depth, bit-level affine subspace membership circuit.

Inputs from either side may be preprocessed freely. Every AND, OR and XOR in
the arithmetic below is implemented with binary gates and complemented wires.
Every comparison in this control retains the two wire polarities.
"""
from itertools import product
from random import Random


def conjunction(x, y):
    return (x[0] and y[0], 1 + max(x[1], y[1]))


def disjunction(x, y):
    return (x[0] or y[0], 1 + max(x[1], y[1]))


def opposite(x):
    return (not x[0], x[1])


def xor(x, y):
    return disjunction(conjunction(x, opposite(y)), conjunction(opposite(x), y))


def balanced(words, merge):
    while len(words) > 1:
        next_words = [merge(words[i], words[i+1]) for i in range(0, len(words)-1, 2)]
        if len(words) % 2:
            next_words.append(words[-1])
        words = next_words
    return words[0]


def add_three(a, b, c):
    assert len(a) == len(b) == len(c)
    first = [xor(x,y) for x,y in zip(a,b)]
    total = [xor(v,z) for v,z in zip(first,c)]
    carry = [disjunction(conjunction(x,y), conjunction(v,z)) for x,y,v,z in zip(a,b,first,c)]
    return total, [(False,0)] + carry[:-1]


def compare_sum(a, b, target):
    # Compare the two-word sum using a parallel prefix circuit for the carries.
    gen = [conjunction(x,y) for x,y in zip(a,b)]
    prop = [xor(x,y) for x,y in zip(a,b)]
    step = 1
    prefixes = list(zip(gen, prop))
    while step < len(a):
        old = prefixes
        prefixes = list(old)
        for i in range(step, len(a)):
            hi, lo = old[i], old[i-step]
            prefixes[i] = (disjunction(hi[0], conjunction(hi[1],lo[0])),
                           conjunction(hi[1],lo[1]))
        step *= 2
    carry = [(False,0)] + [v[0] for v in prefixes[:-1]]
    bits = [xor(v,w) for v,w in zip(prop,carry)]
    matches = [v if (target >> i) & 1 else opposite(v) for i,v in enumerate(bits)]
    return balanced(matches, conjunction)


def equation(p, point, coeff, offset):
    b = (p-1).bit_length()
    terms = []
    # The line supplies the bits of -offset modulo p.
    for i in range(b):
        terms.append((bool((-offset % p >> i) & 1), 0, 2**i % p))
    for x, a in zip(point, coeff):
        for i, j in product(range(b), repeat=2):
            value, depth = conjunction((bool(x >> i & 1), 0),(bool(a >> j & 1), 0))
            terms.append((value, depth, 2**(i+j) % p))
    bound = sum(v for _,_,v in terms)
    width = max(1,bound.bit_length())
    zero = [(False,0)]*width
    words = [[(v,d) if (weight >> i) & 1 else (False,0) for i in range(width)]
             for v,d,weight in terms]
    while len(words) > 2:
        new = []
        i = 0
        while i+2 < len(words):
            new.extend(add_three(*words[i:i+3]))
            i += 3
        words = new + words[i:]
    if len(words) == 1:
        words.append(zero)
    checks = [compare_sum(*words, v) for v in range(0,bound+1,p)]
    # The outer equations are intersected, so conservatively maintain both rails.
    return balanced(checks, disjunction)


if __name__ == '__main__':
    rng = Random(729)
    for p, dimension, trials in [(2,2,256),(3,2,300),(5,3,180),(7,4,120),(17,2,75)]:
        peak = passes = 0
        for trial in range(trials):
            point = [rng.randrange(p) for _ in range(2*dimension)]
            matrix = [[rng.randrange(p) for _ in point] for _ in range(dimension)]
            values = [sum(x*a for x,a in zip(point,row)) % p for row in matrix]
            levels = list(values)
            if trial % 2:
                j = rng.randrange(dimension)
                levels[j] = (levels[j]+1) % p
            got, depth = balanced([equation(p,point,row,offset) for row,offset in zip(matrix,levels)],
                                  conjunction)
            assert got == (levels == values)
            passes += got
            peak = max(peak,depth)
        print(f'prime {p}, codimension {dimension}: {trials} cases, {passes} positive, depth {peak}')
