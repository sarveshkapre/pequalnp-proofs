"""Finite truth-table checks of the two reductions, including least fixed points."""
from itertools import combinations, product
from random import Random


def vertices(mask, k):
    return [i for i in range(k) if mask & (1 << i)]


def join(values):
    result = 0
    for v in values:
        result |= v
    return result


def populations(k):
    n = 1 << (2*k)
    return (1 << n)-1, [[sum(1 << c for c in range(n) if c >> (2*i+e) & 1)
                          for e in range(2)] for i in range(k)]


def evaluate(deps, raw, full, *, forced=0, off=0, anchored=0, raw_only=False):
    """Least solution; a selected source supplies one arm of each touched reader."""
    k = len(deps)
    old = [0]*k
    for _ in range(k+1):
        new = []
        for i, pair in enumerate(deps):
            bit = 1 << i
            hit = [bool(m & anchored) for m in pair]
            arms = [raw[i][e] | join(old[j] for j in vertices(pair[e], k)) for e in (0,1)]
            if bit & forced:
                value = full
            elif bit & off:
                value = 0
            elif any(hit):
                value = join(arms[1-e] for e in (0,1) if hit[e])
            elif raw_only:
                value = raw[i][0] & raw[i][1]
            else:
                value = arms[0] & arms[1]
            new.append(value)
        if new == old:
            return new
        old = new
    raise AssertionError("finite monotone iteration did not stabilize")


def direct(deps, raw, full):
    """Independent column-by-column event propagation on the original circuit."""
    k = len(deps)
    result = [0]*k
    for cell in range(full.bit_length()):
        on = 0
        while True:
            before = on
            for i, pair in enumerate(deps):
                if all((raw[i][e] >> cell & 1) or (pair[e] & on) for e in (0,1)):
                    on |= 1 << i
            if on == before:
                break
        for i in vertices(on, k):
            result[i] |= 1 << cell
    return result


def rejection(wires, need, full):
    return full ^ join(wires[i] for i in vertices(need, len(wires)))


def private_representative(W, readers, k):
    return all(any(pair & W == 1 << v for pair in readers) for v in vertices(W,k))


def feedback_controls(deps, raw, full):
    k = len(deps)
    expected = direct(deps, raw, full)
    readers = [p | q for p,q in deps]
    answers = [0]*(1 << k)
    for W in range(1 << k):
        if not private_representative(W, readers, k):
            continue
        wires = evaluate(deps,raw,full,forced=W,anchored=W,raw_only=True)
        forbidden = join(mask for i,mask in enumerate(readers) if not ((1 << i) & W or mask & W))
        guard = rejection(wires,forbidden,full)
        for need in range(1 << k):
            answers[need] |= guard & rejection(wires,need,full)
    assert answers == [rejection(expected,need,full) for need in range(1 << k)]


def cut_controls(deps, raw, full, n):
    k = len(deps)
    early = (1 << n)-1
    assert all(not ((a|b) & ~early) for a,b in deps[:n])
    expected = direct(deps,raw,full)
    small, large = [], []
    for T in range(1 << n):
        # Prefix is a closed overestimate. Every signal outside T must stay false.
        guard = full
        for i in vertices(early ^ T,k):
            a,b = (full if deps[i][e] & T else raw[i][e] for e in (0,1))
            guard &= full ^ (a & b)
        suffix = evaluate(deps,raw,full,forced=T,off=early ^ T)
        small.append([guard & rejection(suffix,need,full) for need in range(1 << k)])
        clamped = evaluate(deps,raw,full,forced=T,anchored=T)
        large.append([rejection(clamped,need,full) for need in range(1 << k)])
    for r in range(n+2):
        branches = [row for t,row in enumerate(small) if bin(t).count("1") < r]
        branches += [row for w,row in enumerate(large) if bin(w).count("1") == r]
        for need in range(1 << k):
            assert join(row[need] for row in branches) == rejection(expected,need,full)


def exhaustive():
    k = 2
    full,raw = populations(k)
    for arms in product(range(4),repeat=4):
        feedback_controls([arms[:2],arms[2:]],raw,full)
    k = 3
    full,raw = populations(k)
    count = 0
    for first,second,third,fourth in product(range(2),range(2),range(4),range(4)):
        deps = [(0,0),(first,second),(third,fourth)]
        feedback_controls(deps,raw,full)
        for n in range(4):
            cut_controls(deps,raw,full,n)
        count += 1
    print(f"All 256 two-gate feedback wirings and {count} three-gate acyclic wirings; all raw settings and taps.")


def random_checks():
    rng = Random(19729)
    full,raw = populations(4)
    for _ in range(128):
        n = rng.randrange(1,4)
        deps = [tuple(rng.randrange(1 << (n if i<n else 4)) for e in (0,1)) for i in range(4)]
        cut_controls(deps,raw,full,n)
        feedback_controls(deps,raw,full)
    print("128 four-gate wirings with feedback inside the cut parts, all 256 raw settings and 16 outputs.")
    # Both alternatives of the first gate are true; the second copies it on one arm.
    deps = [(0,0),(1,0)]
    raw = [(1,1),(0,1)]
    bad = evaluate(deps,raw,1,raw_only=True)
    assert rejection(bad,2,1) == 1 and rejection(direct(deps,raw,1),2,1) == 0
    feedback_controls(deps,raw,1)
    print("Two-gate counterexample: omitting the guard accepts a firing output.")


def matching_controls():
    k = 3
    for rows in product(range(1 << k),repeat=k):
        private = max(bin(W).count("1") for W in range(1 << k) if private_representative(W,rows,k))
        actual = 0
        for size in range(1,k+1):
            for cols in combinations(range(k),size):
                mask = sum(1 << j for j in cols)
                for selected in combinations(rows,size):
                    restriction = [v & mask for v in selected]
                    if sorted(restriction) == [1 << j for j in cols]:
                        actual = max(actual,size)
        assert actual == private
    print("All 512 binary 3x3 reader relations: largest irredundant generator equals largest induced matching.")


def balanced_banks():
    rng = Random(8001)
    size = 8
    full = (1 << (size*size))-1
    def rectangle(rows, cols):
        return sum(1 << (size*x+y) for x in vertices(rows,size) for y in vertices(cols,size))

    cases = 0
    for _ in range(32):
        k,n = 5,rng.randrange(2,5)
        deps = [tuple(rng.randrange(1 << i) for _arm in (0,1)) for i in range(k)]
        shores = [[(rng.randrange(256),rng.randrange(256)) for _arm in (0,1)] for i in range(k)]
        raw = [[rectangle(a,255) | rectangle(255,b) for a,b in pair] for pair in shores]
        for T in range(1 << n):
            untreated = [i for i in range(n,k) if not ((deps[i][0] | deps[i][1]) & T)]
            prefix = [i for i in range(n) if not (1 << i) & T]
            operands = [[0 if deps[i][e] & T else full ^ raw[i][e] for e in (0,1)] for i in prefix]
            u,v = len(prefix),len(untreated)
            split = (u-v)//2 if u >= v else 0

            def expand(terms, starting):
                entries = starting
                for a,b in terms:
                    entries = [prior & piece for prior in entries for piece in (a,b)]
                return entries

            exact = evaluate(deps,raw,full,forced=T,off=((1 << n)-1)^T)
            guard = full
            for a,b in operands:
                guard &= a | b
            for need in range(1 << k):
                suffix_bank = []
                for choices in product((0,1),repeat=v):
                    orient = dict(zip(untreated,choices))
                    demand, rows, cols = need, 255, 255
                    for i in range(k-1,n-1,-1):
                        if not demand & (1 << i):
                            continue
                        if i in orient:
                            e = orient[i]
                        else:
                            e = 1 if deps[i][0] & T else 0
                        demand |= deps[i][e]
                        a,b = shores[i][e]
                        rows &= ~a
                        cols &= ~b
                    suffix_bank.append(0 if demand & T else rectangle(rows,cols))
                first = expand(operands[:split],suffix_bank)
                second = expand(operands[split:],[full])
                assert (join(first) & join(second)) == (guard & rejection(exact,need,full))
                largest = max(v,(u+v+1)//2)
                assert max(len(first),len(second)) <= 1 << largest
                cases += 1
    print(f"Two explicit banks: {cases} prefix-guess/output combinations, each on 64 cells; sizes checked.")


if __name__ == "__main__":
    exhaustive()
    random_checks()
    matching_controls()
    balanced_banks()
