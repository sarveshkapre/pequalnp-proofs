"""Exact finite controls for the leaf compression, star moments and density bound."""
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, product
from math import comb, factorial


def output_table(arms, output, atoms, universe):
    """Evaluate all assignments of the raw arms at once, including feedback."""
    state = [0] * len(arms)
    while True:
        nxt = []
        for i, pair in enumerate(arms):
            values = []
            for e, deps in enumerate(pair):
                value = atoms[2 * i + e]
                for j in deps:
                    value |= state[j]
                values.append(value)
            nxt.append(values[0] & values[1])
        if nxt == state:
            break
        state = nxt
    accept = 0
    for i in output:
        accept |= state[i]
    return universe ^ accept


def leaf_pairs(arms):
    candidates = {}
    for v, pair in enumerate(arms):
        if pair[0] or pair[1]:
            continue
        reads = [(i, e) for i, both in enumerate(arms) for e in range(2) if v in both[e]]
        if len(reads) == 1:
            p, side = reads[0]
            candidates.setdefault(p, (v, side))
    return candidates


def compressed_masks(arms, output, pairs):
    leaf_set = {v for v, _ in pairs.values()}
    peeled = output & leaf_set
    active = {p: (v, side) for p, (v, side) in pairs.items() if v not in peeled}
    normal = sorted(set(range(len(arms))) - leaf_set - set(active))
    core_masks = set()
    for choices in product(range(2), repeat=len(normal)):
        for digits in product(range(3), repeat=len(active)):
            arm = dict(zip(normal, choices))
            for (p, (v, side)), trit in zip(active.items(), digits):
                arm[p] = side if trit else 1 - side
                arm[v] = int(trit == 2)
            demand = list(output - peeled)
            seen = set()
            while demand:
                i = demand.pop()
                if i not in seen:
                    seen.add(i)
                    demand.extend(arms[i][arm[i]] - peeled)
            core_masks.add(sum(1 << (2 * i + arm[i]) for i in seen))
    assert len(core_masks) <= 2 ** len(normal) * 3 ** len(active)
    masks = core_masks
    for v in sorted(peeled):
        masks = {q | (1 << (2 * v + side)) for q in masks for side in range(2)}
    return masks


@lru_cache(maxsize=None)
def tables(k):
    cases = 1 << (2 * k)
    universe = (1 << cases) - 1
    atoms = [sum(1 << s for s in range(cases) if s & (1 << b)) for b in range(2 * k)]
    @lru_cache(maxsize=None)
    def rectangle(mask):
        value = universe
        for b, atom in enumerate(atoms):
            if mask & (1 << b):
                value &= universe ^ atom
        return value
    return atoms, universe, rectangle


def check_wiring(arms):
    k = len(arms)
    atoms, universe, rectangle = tables(k)
    pairs = leaf_pairs(arms)
    for word in range(1 << k):
        output = {i for i in range(k) if word & (1 << i)}
        value = 0
        for mask in compressed_masks(arms, output, pairs):
            value |= rectangle(mask)
        assert value == output_table(arms, output, atoms, universe)
    return bool(pairs)


def check_circuits():
    k = 4
    edges = list(combinations(range(k), 2))
    protected = 0
    for choices in product(range(4), repeat=len(edges)):
        arms = [(set(), set()) for _ in range(k)]
        for (j, i), word in zip(edges, choices):
            for side in range(2):
                if word & (1 << side):
                    arms[i][side].add(j)
        protected += check_wiring(arms)
    # Two private leaves, arbitrary cross-dependencies and self-feedback in the core.
    for word in range(256):
        arms = [(set(), set()), (set(), set()), ({0}, set()), (set(), {1})]
        for d in range(8):
            if word & (1 << d):
                arms[2 + d // 4][(d // 2) % 2].add(2 + d % 2)
        assert check_wiring(arms)
    print(f"4,096 ordered wirings ({protected} with a private pair), 256 feedback wirings;"
          " every output and all 256 raw assignments passed.")


def check_large_component():
    # The three readers form a directed cycle. Each has a separate private input.
    arms = [(set(), set()) for _ in range(3)] + [
        ({0}, {5}), ({1}, {3}), ({2}, {4})
    ]
    assert check_wiring(arms)
    pairs = leaf_pairs(arms)
    readers = {3, 4, 5}
    assert len(compressed_masks(arms, readers, pairs)) == 3**3
    # Four further isolated gates make ten. Test every output of the six-gate
    # core, grouping its extracted unit factors together with the four outsiders.
    for word in range(64):
        peeled = (word & 7).bit_count()
        count = 2**peeled * 3**(3-peeled)
        core_weight = (count-1).bit_length()
        assert core_weight <= 5
        assert core_weight + peeled + 4 <= 10
    print("Six-gate component with four isolates: all 64 core outputs pass;"
          " 27 distinct traces when all readers are outputs; two bins of five suffice.")


def graphs(n):
    edges = list(combinations(range(n), 2))
    for mask in range(1 << len(edges)):
        adj = [set() for _ in range(n)]
        for d, (i, j) in enumerate(edges):
            if mask & (1 << d):
                adj[i].add(j)
                adj[j].add(i)
        yield adj


def component(adj, root):
    reached = {root}
    todo = [root]
    while todo:
        for j in adj[todo.pop()] - reached:
            reached.add(j)
            todo.append(j)
    return reached


def check_moments():
    n, cutoff = 6, 4
    sums = [0, 0]
    for adj in graphs(n):
        for v in range(n):
            if len(component(adj, v)) >= cutoff:
                a = sum(u < v and len(adj[u]) == 1 for u in adj[v])
                for r in (1, 2):
                    sums[r-1] += comb(a, r)
    for r, total in enumerate(sums, start=1):
        small = n-r
        success = sum(len(component(adj, 0)) >= cutoff-r for adj in graphs(small))
        remain_prob = Fraction(success, 2 ** comb(small, 2))
        excluded = r*(n-r-1) + comb(r, 2)
        prediction = comb(n, r+1) * Fraction(1, 2**(r+excluded)) * remain_prob
        assert prediction == Fraction(total, 2**comb(n, 2))
    print(f"All 32,768 simple six-vertex graphs: first two marked-star sums {sums}.")


def exp_bounds(x):
    degree = 12
    terms = [x**i / factorial(i) for i in range(degree+2)]
    lower = sum(terms[:-1])
    upper = lower + terms[-1] / (1-x/(degree+2))
    return lower, upper


def check_arm_laws():
    # Credit log2(4/3) on a single, one on an absence, zero on a double.
    # Conditional expected credit >= log2(4/3) iff 2^u >= (4/3)^(u+d)
    # after clearing the denominator of the absent and double masses.
    tested = 0
    for left in range(13):
        for right in range(13-left):
            for double in range((12-left-right)//2+1):
                for proposal in range(max(1, left+right+2*double), 13):
                    absent = proposal-left-right-double
                    assert absent >= double
                    assert 2**absent * 3**(absent+double) >= 4**(absent+double)
                    tested += 1
    print(f"{tested} exact two-arm law and envelope combinations passed.")


def check_density():
    lam, upper_rho, lower_b = Fraction(57, 40), Fraction(531, 1000), Fraction(34, 100)
    assert exp_bounds(lam/2)[0] > 2
    assert exp_bounds(lam*upper_rho)[1] < 1/(1-upper_rho)
    assert exp_bounds(lam)[1] < lam/lower_b
    assert lower_b/2 - lower_b**2/6 > Fraction(15, 100)
    assert Fraction(4, 3)**5 > 4
    effective = upper_rho * (1 - Fraction(2, 5)*Fraction(15, 100))
    assert effective == Fraction(24957, 50000) < Fraction(1, 2)
    print(f"Rational certificate at mean degree 57/40: effective giant fraction < {effective} < 1/2.")


if __name__ == '__main__':
    check_density()
    check_arm_laws()
    check_moments()
    check_circuits()
    check_large_component()
