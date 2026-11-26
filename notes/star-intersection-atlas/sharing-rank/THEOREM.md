# How close can sharing come to the maximum rank?

In the finite bipartite star model, raw row and column stars and their unions are free. Count binary intersections. A circuit can reuse an intermediate result. A formula pays for both occurrences. Write C(G) and F(G) for the two minimum costs, and Z for the real zero-cell matrix of G.

**Theorem.** For every integer k ≥ 3, the largest rank of Z among graphs with C(G) = k and F(G) > k is exactly **3^k − 2**. An explicit family attaining this rank has **F(G) = k + 1**. The saving proved here is one intersection at every budget. Whether the additive saving can grow is a separate question.

Pjscruggs proved the sharp general bound rank(Z) ≤ 3^k by reverse expansion, including circuits with reuse. The refinement below identifies exactly how close a circuit that needs sharing can come to this bound. The earlier three-gate shared expression provides the starting point for the construction. The rank identity for matrices of the form f(x AND y) is classical. [Pjscruggs’s rank bound](https://github.com/pjscruggs/pequalnp-proofs/blob/7da7d81614b93ea808c11ac27f27136942fec385/notes/star-intersection-atlas/larger-planes.md) · [Three-intersection sharing](https://github.com/open-goat/pequalnp-proofs/discussions/23239) · [Knop, Lovett, McGuire and Yuan, Claim 4.1](https://arxiv.org/abs/2010.08994)

## 1. The universal upper bound

Take complements throughout. A free union of raw stars becomes a rectangle, free composition becomes intersection and the paid operation becomes union. Order the paid gates from earliest to latest. Each input port of gate i is one freely chosen raw rectangle intersected with a selection of earlier gate outputs. The final output is another port. This normalization follows by flattening the free intersections between consecutive paid gates. It also allows unused gates and empty selections.

For a fixed normalized circuit and output port with raw rectangle T, define its **flat expression** as T intersected with every Aᵢ ∪ Bᵢ, where Aᵢ and Bᵢ are the two raw port rectangles at gate i. This expression always has a formula with at most k paid gates.

We prove two simultaneous bounds for every port after k gates. Its zero-cell matrix has rank at most 3^k. If the port differs from its flat expression, its rank plus two is at most 3^k. At k = 0 the port is a rectangle, has rank at most one and equals its flat expression.

Suppose there are k = h + 1 gates. If the output port omits the last gate, apply the ordinary bound at h. The inequality 3^h + 2 ≤ 3^(h+1) covers even a discrepancy with the flat expression. Otherwise write the output as X ∪ Y by distributing its other factors over the two inputs of the last gate. Each of X, Y and X ∩ Y is a legitimate port on the first h gates. Their zero-set indicators satisfy

    1[X ∪ Y] = 1[X] + 1[Y] − 1[X ∩ Y].

Rank subadditivity gives the ordinary bound. If X and Y both equal their flat expressions, their union equals the full flat expression by distributivity. Hence a discrepancy forces at least one of X and Y to lose two rank units by induction. The other two terms still satisfy the ordinary bound. This proves the stronger statement, regardless of repeated wires or cancellations. In particular, any graph with F(G) > k differs from the flat expression of every k-gate circuit for it.

## 2. A family at rank 3^k − 2

Put d = k − 1. Both vertex classes consist of the bit strings of length 2 + 2d. Label the coordinates a, b, c₁, e₁, …, c_d, e_d. Each coordinate below is tested on the bitwise AND of the row and column string, so its 1-set is a rectangle. Define the zero cells by

    S = a ∨ b
    f = ∧ᵢ (cᵢ ∨ (eᵢ ∧ S)).

Compute S once and reuse it at each of the d later gates. This gives C(G) ≤ d + 1. A formula uses at most d + 2 paid gates by the Boolean identity

    f = (∧ᵢ cᵢ) ∨ (S ∧ ∧ᵢ(cᵢ ∨ eᵢ)).

To compute the rank exactly, let P = ∏ᵢ cᵢ and Q = ∏ᵢ(cᵢ + eᵢ − cᵢeᵢ). The unique multilinear polynomial of f on the Boolean cube is

    P + (a + b − ab)(Q − P).

Q has 3^d distinct monomials with coefficients ±1. Exactly one is P. The three multipliers a, b, ab have different supports, disjoint from all coordinates in Q. Consequently the polynomial has 1 + 3(3^d − 1) = 3^k − 2 nonzero coefficients. For completeness, index rows and columns by all subsets of the coordinates, and let L[X,U] = 1 when U ⊆ X. Ordered by size, L is unit lower triangular. If c_U are the polynomial coefficients, the zero matrix is L diag(c_U) Lᵀ, because the monomial U at X ∩ Y is L[X,U]L[Y,U]. Its real rank is exactly the support count. This exceeds 3^(k−1), so the circuit cost is exactly k.

## 3. Why no other formula of cost k works

**Nested formulas.** For any zero-set formula, keep a signed sum of rectangle indicators. A raw rectangle uses one term. Intersecting expressions with x and y terms uses at most xy terms. Taking their union uses at most x + y + xy terms by inclusion–exclusion. Thus a formula with h paid gates uses at most 3^h terms, which also bounds its rank.

Flatten only the free intersections at the root. If a paid union lies below another paid union, one remaining top-level factor is a union whose children use i and j gates, at least one of i, j positive. Its term count divided by 3^(1+i+j) is at most (1 + 3^(−i) + 3^(−j))/3 ≤ 7/9. All other top-level factors obey the ordinary bound. Hence any such formula with k paid gates has rank at most **7·3^(k−2)**, strictly below 3^k − 2 for k ≥ 3. Formulas costing less than k are already excluded by the circuit bound.

**Flat formulas.** It remains to exclude a free intersection of k unions of two rectangles, possibly clipped by a raw rectangle. Restrict to the rows and columns v for which f(v) = 1. Each such vertex has a zero cell with the all-ones vertex on the other side. Therefore the target edge graph on this restriction has no full row or column, and any raw output rectangle must contain the whole restriction.

The complement of a union of two rectangles is the intersection of two unions of row and column stars. When expanded, it consists of some full rows, some full columns and two bicliques. Each factor's complement lies in the edge graph, so its full-row and full-column terms are empty on the restriction. A flat k-gate formula therefore covers the restricted edges with at most 2k bicliques. A fooling set consists of edges such that each pair has at least one crossed cell outside the edge graph. Every biclique in a cover contains at most one of those edges.

Here is a fooling set of **2k + 2** edges. For d = 2, encode the six bits a,b,c₁,e₁,c₂,e₂ from least to most significant. The following eight (row, column) pairs work.

    (61,46) (57,62) (59,54) (27,47)
    (62,45) (58,61) (47,30) (53,57)

Direct substitution gives f(r AND c) = 0 at each listed edge and f = 1 in at least one crossed cell for each of the 28 pairs. Every endpoint satisfies S = f = 1 on its own word. These facts are also checked by the replay.

For d > 2, append all ones to those eight pairs. For each extra coordinate pair i, take two words uᵢ and vᵢ that are all ones except on that pair, where they are (1,0) and (0,1). Add both oriented edges (uᵢ,vᵢ) and (vᵢ,uᵢ). Each diagonal intersection of the two words loses both bits at i and has f = 0. Crossing the orientations at the same i gives a word with f = 1. Crossing different i gives S = 1 and at least one surviving bit at every coordinate pair. Crossing an added edge with a base edge also gives f = 1 in both crossed cells, since the base endpoint has S = f = 1 and its extra bits are all ones. Thus all endpoints are active and the enlarged family remains a fooling set. Its size is 8 + 2(d−2) = 2k + 2, more than the flat formula can cover.

This excludes every formula at budget k and the explicit formula achieves k + 1. Together with the universal upper bound it gives the claimed extremum for every k ≥ 3.
