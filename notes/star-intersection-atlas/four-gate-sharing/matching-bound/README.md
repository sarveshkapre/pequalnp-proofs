# Matching number controls formula cost on forests

Let C and F count binary intersections in circuits and formulas built from row and column stars. Unions are free. Let ν be the maximum number of vertex-disjoint edges in a finite bipartite forest. Write d(s) for the least integer d ≥ 2 with binom(d, ⌊d/2⌋) ≥ s.

**Every such forest satisfies F ≤ 2(d(ν)−1).** Moreover ν ≤ 2^(C+1), so for circuit budget k the uniform bound is

    F ≤ 2(d(2^(k+1)) − 1) = 2k + log₂(k+1) + O(1).

The earlier general bound was 8k+2. The [exact result at budget four](../forest-sharpness/README.md) gives the stronger low-budget answer five. A forest with a maximum matching of size s ≥ 1 needs at least log₂(s)−1 circuit intersections and at most 2 log₂(s)+log₂ log₂(s)+O(1) formula intersections as s grows. The best leading constant and the possibility of an unbounded additive gap on forests remain open here. For bounded-degree trees the [hypercube construction](../cube-embedding/README.md) now gives leading constant one.

## The matching-number theorem

Root every nonempty component. Color each edge by the shore of its parent. Each color forms a collection of vertex-disjoint stars. Within one color a child has only one parent and a parent cannot be another star's child. Choose one edge from each nonempty star of that color. These edges form a matching, so there are at most ν stars of each color. This works for arbitrary degrees, duplicate leaves and isolated vertices.

Assign the stars of one color distinct h-element subsets of a d-element set, with 0 < h < d and binom(d,h) ≥ ν. Give each active row its star's subset S and each active column the complement of its star's subset T. Give an inactive vertex on either shore the full d-element set. For each coordinate take the free union of all row and column stars whose vertex label omits it. Intersect the d unions. A cell survives exactly when the two labels are disjoint. For active vertices this means S ⊆ T, hence S = T by equal cardinality. The labels of active vertices are nonempty and proper, so incidences with inactive vertices are rejected as well. The result is exactly that color's edges at cost d−1. Take the free union of the formulas for the two colors.

The Lean statement allows any h and d with these inequalities. It states the matching bound by quantifying over every pair of injective endpoint maps and counts intersections via the project's formula semantics. It reuses the rooting lemma from the earlier forest proof.

## From circuit cost to matching number

The [ordinary-to-parallel simulation](https://github.com/open-goat/pequalnp-proofs/discussions/19729#discussioncomment-19917939) gives a single layer with p ≤ 2^k−1 paid intersections for an ordinary acyclic k-gate circuit. In a parallel gate expand (row stars ∪ column stars) ∩ (row stars ∪ column stars). The two cross terms are positive rectangles. The other two terms consist of full rows or full columns. Collect all full rows of all gates and of the raw output into one further rectangle, and all full columns into a second. Thus all edges have a cover by at most 2p+2 ≤ 2^(k+1) all-positive rectangles. A rectangle in a forest cannot contain two vertex-disjoint edges, since its two cross entries would complete a four-cycle. This gives the bound on ν, including the case of free full stars. Stirling's estimate for the central binomial coefficient gives d(s) = log₂(s) + ½ log₂ log₂(s) + O(1). Substituting s = 2^(k+1) yields the stated asymptotic bound.

## What disjoint copies can amplify

Fix any nonempty finite bipartite graph H having an edge. Write tH for t disjoint copies and M_t for the t-edge matching. For either cost X = C or X = F,

    X(M_t) ≤ X(tH) ≤ X(M_t) + X(H) + 1.

Restricting tH to one edge per copy proves the first inequality. For the second, pull the graph H back along the maps forgetting copy indices, and pull M_t back along the maps retaining only those indices. A lifted input star is a free union of stars. Their intersection gives exactly tH, including the cross-copy nonedges. Consequently the additive gaps of tH and M_t differ by at most a constant depending only on H. An unbounded gap along copies of a fixed tree would already require an unbounded gap along matchings.

For t ≥ 2 a parallel realization of M_t has no full stars. It covers at most two matching edges per gate, giving t ≤ 2(2^k−1) for k = C(M_t). On the other hand the equal-weight code above gives F(M_t) ≤ d(t)−1 using one layer. For fixed H this yields

    0 ≤ F(tH) − C(tH) ≤ ½ log₂ log₂(t) + O_H(1).

Both costs divided by log₂(t) tend to one. Taking arbitrarily many disjoint copies cannot produce a linear-in-circuit-cost saving. These estimates leave open slower unbounded growth.

## The two-copy test

For the earlier 10×10 tree T, [seven-bit labels](double-tree.json) give a six-intersection formula for 2T. Intersection of the seven free unions tests disjointness. The 20×20 array has 38 edges, and it contains an induced matching of twelve edges. In the free-union star model a four-intersection circuit can realize an induced matching of size at most **ten**. Therefore 5 ≤ C(2T) ≤ F(2T) ≤ 6, ruling out a two-gate saving on this candidate. We have not determined the exact pair of costs from these inequalities.

For the ten-edge bound restrict the circuit to the matching; a star remains a star or becomes empty. For a matching of size at least two the final raw-star union must be empty. In the complement model each raw arm is a zero rectangle, a gate takes the union of two arms, and each arm meets its zero rectangle with any chosen earlier gates. Enumerate four ordered gates with both arms ordered, including unused gates, and all output tap subsets. There are 65,536 combinations and 572 distinct scalar zero functions f on eight bits. Each gives an edge when f(x & y) is false for the row and column words x,y.

For each selected diagonal pair, enlarge its common bits to an inclusion-maximal word w with f(w) false. Add those bits to both endpoints. Allocate each bit missing from both endpoints to just one until their union is full. Word enlargement preserves all positive values of f at cross pairs by monotonicity. Each endpoint evaluates true on its own word since it contains a true cross word. Thus every induced matching of size at least two can be represented by pairs with intersection a maximal false word, full union, and both endpoint values true. Enumerate these pairs. Two are compatible exactly when both cross words evaluate true. Cliques give actual matchings and every matching occurs after normalization. Across the 572 tables the largest clique has ten vertices. Five raw disjointness coordinates attain ten: use the ten two-subsets of five bits for the rows and their complements for the columns. The formula costs four intersections.

## Reproducibility and credit

The portable checker uses Python 3.10+. From this directory run

```sh
python3 -I -B replay.py
```

It reconstructs all 4,040 labelled forests of sizes 3×3, 3×4 and 4×3, calculates matching number independently of rooting, checks the 400 doubled-tree cells and twelve matching edges, and exhausts the four-gate matching calculation. From the repository root the standalone Mac verifier command is

```sh
node tools/check-lean.mjs lean/PEqualNP/SparseSharing/MatchingBound.lean notes/star-intersection-atlas/four-gate-sharing/matching-bound/MatchingBound.statement check
```

The official Mac verifier returned **ACCEPTED** for the uniform **matching-number-to-formula** implication. The kernel rechecked 1,904 constants with axioms Quot.sound, propext and Classical.choice. The [verifier receipt](verification.txt) includes the statement, toolchain and source hashes. The translation to k uses the separately published ordinary-to-parallel theorem. The asymptotics and copy inequalities are written deductions. The ten-edge capacity is a finite executable proof.

Pjscruggs developed the star-intersection atlas. The earlier [forest simulation](https://github.com/open-goat/pequalnp-proofs/discussions/23239#discussioncomment-19915151) supplied the rooted decomposition, and the [parallel simulation](https://github.com/open-goat/pequalnp-proofs/discussions/19729#discussioncomment-19917939) supplied the circuit bound. Equal-weight labels are the classical antichain construction for the complement of a matching, a crown graph. See de Caen, Gregory and Pullman, *The Boolean rank of zero-one matrices* (1981), cited as [reference 12 in the MFCS paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol241-mfcs2022/LIPIcs.MFCS.2022.56/LIPIcs.MFCS.2022.56.pdf) and the related [Sperner argument for larger planes](https://github.com/pjscruggs/pequalnp-proofs/blob/42423ae1a3fa6fcf725671b247fe7d18ab2b2d00/notes/star-intersection-atlas/larger-planes.md). The contributions here are the matching-sensitive forest bound and its consequences for circuit cost and disjoint repetition, together with the doubled-tree certificate and the four-gate matching calculation. Historical priority for the combined results is unestablished.
