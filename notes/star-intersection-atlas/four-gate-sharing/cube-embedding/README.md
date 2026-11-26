# For bounded-degree trees, the leading constant is one

Work in pjscruggs's bipartite grid model. Row and column stars are the inputs, unions are free, and a binary intersection costs one. Let C be minimum circuit cost, F minimum formula cost, and B the minimum number of rectangles covering exactly the nonedges. A cover by B rectangles gives a formula by complementing each rectangle to a free union of stars and intersecting the B factors. This flat formula costs B−1 for B ≥ 1.

**Theorem.** Fix maximum degree Δ and treewidth w. For an N-vertex bipartite graph with no isolated vertices and with these bounds, as N tends to infinity,

    log₂ N − O_Δ(1) ≤ C ≤ F ≤ B−1 ≤ log₂ N + O_{Δ,w}(log₂ log₂ N).

In particular, F/C tends to one uniformly on trees of bounded maximum degree. A two-intersection saving is still possible under this estimate. Whether any tree actually attains it is open here. A family with a circuit-to-formula ratio bounded away from one would need unbounded maximum degree on any subsequence realizing that ratio.

Even the additive order of the **flat** upper bound is best possible: B ≥ log₂ N + ½ log₂ log₂ N − O_Δ(1). The coefficient of the upper correction and the size of the saving F−C remain undetermined. Arbitrarily many isolated vertices can be added at a cost of at most two further intersections: extend the old labels to the new vertices by duplication, then intersect with the free union of the active rows and with the free union of the active columns. Thus one may count only nonisolated vertices in N. The edgeless graph itself costs zero.

## From short cube edges to nonedge rectangles

Suppose the vertices have distinct binary addresses in d bits and adjacent addresses differ in at most R coordinates. Write x for a row address, viewed as the subset of its one coordinates. For a column c let U be the union of the addresses of its row neighbors. Every neighbor y is contained in U and has at most b = 2RΔ missing coordinates from U. Indeed, for every other neighbor z, both y and z lie within distance R of c, so at most 2R elements of z are outside y. Summing over the neighbors proves the claim.

The first d tests require x ⊆ U. Each failed coordinate defines a zero rectangle. This test can admit extra rows. To distinguish them, color equal-weight d-bit words so that distinct words at Hamming distance at most 2b receive different colors within that weight. Greedy coloring needs at most

    M = Σ_{j=0}^{min(b,d)} binom(d,j)²

colors per weight: from a word of weight a, there are binom(a,j) binom(d−a,j) words obtained by exchanging j coordinates, and the j=0 term counts the original word. The tag of x is its weight and color, so the number T of possible tags is at most (d+1)M. For fixed b this is polynomial in d.

Accept x at c when x ⊆ U and its tag occurs among c's neighbors. To see that these two conditions suffice, let y be a neighbor with the same tag. Since x ⊆ U, at most b elements of x are outside y. Equal weights imply at most b elements of y are outside x as well. The two words are within distance 2b. Their equal colors now force equality, and the addresses are injective. An empty neighborhood has an empty tag dictionary and rejects every row.

It remains to implement tag membership while charging only O_Δ(log(T+1)) additional coordinates. Assign a binary code to each tag so that no code is contained in the union of the codes of at most Δ other tags. For a tag z and a set J of at most Δ other tags, one random coordinate with independent fair bits separates z from J with probability at least 2^(−Δ−1). There are at most T(T+1)^Δ pairs (z,J), using a padded ordered listing of J. Choosing more than 2^(Δ+1) ln(max(2,T(T+1)^Δ)) coordinates makes the expected number of missed pairs less than one. Hence a separating family exists; the empty dictionary is included. Such families are classical [superimposed codes](https://doi.org/10.1109/TIT.1964.1053689).

Give x the concatenation of its address and its tag code. Give c the concatenation of U and the union of the tag codes in its dictionary. Adjacency is exactly coordinatewise containment. Each of the d+q coordinates contributes one nonedge rectangle, consisting of rows with a one and columns with a zero in that position. Thus B ≤ d + O_{Δ,R}(log(d+1)).

## Substituting the embedding and proving the lower bounds

[Heun and Mayr (2002)](https://doi.org/10.1006/jagm.2002.1217) embed a graph of bounded treewidth and maximum degree injectively into its optimal hypercube with dilation at most 3⌈log₂((Δ+1)(w+1))⌉+8. Taking d = ⌈log₂ N⌉ proves the upper bound. Their host embedding only requires edges to have short routes. The filtering argument above is what ensures that every nonedge is excluded. For trees the earlier embedding theorem of [Bhatt, Chung, Leighton and Rosenberg](https://fanchung.ucsd.edu/mypaps/fanpap/108hyperembed.pdf) also suffices.

For the circuit lower bound, the [ordinary-to-parallel simulation](https://github.com/open-goat/pequalnp-proofs/discussions/19729#discussioncomment-19917939) gives at most 2^C−1 parallel gates. Expanding each into two cross rectangles and collecting the full rows and columns globally gives at most 2^(C+1) positive rectangles, as in the [matching-number bound](../matching-bound/README.md). Any nonempty positive rectangle in a maximum-degree-Δ graph touches at most Δ vertices on either shore. Since every vertex is incident to an edge, N ≤ 2Δ · 2^(C+1).

For the flat lower bound, greedily choose an edge and discard all remaining edges with an endpoint adjacent to either chosen endpoint. At most 2Δ² edges disappear per choice. The chosen edges form an induced matching of size at least N/(4Δ²), since at least N/2 edges were present. Restricting the nonedge cover gives a biclique cover of a crown graph. With B coordinates, its matching can have at most binom(B,⌊B/2⌋) elements: the sets of rectangles containing each matched row form an antichain, because each off-diagonal zero must be covered and both diagonal cells are forbidden. The central binomial estimate gives the asserted lower correction. See [Bezrukov, Fronček, Rosenberg and Kovář](https://doi.org/10.1016/j.disc.2006.11.045) for the classical crown theorem. This argument bounds flat formulas. It does not bound the additive difference between unrestricted formulas and circuits from below.

## Degrees and treewidth may grow

For unrestricted formulas the tag test also has a deterministic implementation with a better dependence on Δ. Number the T tags and add one padding symbol that no row uses. For each column list its neighbor tags in Δ slots and pad the unused slots. Equality of a row tag and the selected slot uses at most 2ℓ−1 intersections, with ℓ = ⌈log₂(T+1)⌉. For each bit exclude the two directions of mismatch using two free unions of row and column stars. Intersect all 2ℓ unions. Take the free union over the Δ slots, then intersect once with the coarse containment test. Formula occurrences for the slots are paid separately. The cost is at most d + Δ(2ℓ−1) for d ≥ 1.

A pair of subsets of size at most b can be recorded by two sorted, zero-padded b-tuples over d+1 symbols. Thus M ≤ (d+1)^(2b) and log₂ T ≤ (4RΔ+1)log₂(d+1). Substitution of the explicit Heun–Mayr dilation bound gives, with absolute implied constants,

    F ≤ ⌈log₂ N⌉ + O(Δ² log₂((Δ+1)(w+1)) log₂(log₂ N+2)).

Consequently F/C tends to one whenever Δ² log₂((Δ+1)(w+1)) log₂(log₂ N+2) = o(log₂ N). The lower estimate C ≥ log₂ N − log₂ Δ − 2 still applies in that regime. In particular, on trees this covers maximum degree o(√(log₂ N) / log₂ log₂ N). Any family of trees with a fixed proportional saving, F ≥ (1+ε)C for all members, must eventually satisfy Δ = Ω_ε(√(log₂ N) / log₂ log₂ N). To see the quantitative last statement, when Δ ≤ √(log₂ N) its logarithm is at most order log₂ log₂ N. Comparing the two cost bounds then forces Δ²(log₂ log₂ N)² ≥ c_ε log₂ N. Larger Δ already meets the conclusion. The same threshold applies to the tree after keeping only one of any set of leaves with the same neighbor, with N now the reduced vertex count. Restriction preserves the upper budgets, and a formula or circuit on the reduced tree lifts by replacing the input star of the representative by the free union of the original stars it represents. Both optimum costs are therefore preserved. In a reduced tree, at most one leaf is adjacent to any vertex. Thus an asymptotic proportional gap at growing circuit budget requires a vertex with increasingly many **non-leaf** neighbors even after reduction. A fixed saving of two gates could occur at bounded degree.

## Why degree alone is insufficient

For fixed integer Δ, take n = Δs vertices on each shore, partition each shore into Δ labeled blocks of size s, and independently select a perfect matching between each ordered pair of blocks. This yields (s!)^(Δ²) distinct labeled simple Δ-regular graphs. An ordered k-intersection circuit in this model is specified by at most (2k+1)2n raw-star selection bits and k² bits selecting earlier gates for every arm and the output. Indeed, the latter count is 2Σ_{i=0}^{k−1}i+k. Unused gates provide padding. Comparing counts by Stirling's estimate shows that some such graphs have C ≥ (Δ/4)log₂ n − O_Δ(1). Already at fixed degree five, a leading coefficient of one fails without a restriction on structure. This is a counting argument, with no explicit extremal graph claimed.

## Verification and open questions

The official Mac verifier accepted the [standalone Lean theorem](verification.txt), rechecking 1,665 constants with axioms Quot.sound, propext, Classical.choice. The theorem proves the d+q rectangle conclusion from the edge-distance hypotheses, degree, equal-weight coloring and separating-code conditions. It derives the bound on the union of neighbor addresses and proves exact decoding on the entire grid. The greedy coloring bound, existence of short codes, application of Heun–Mayr, and asymptotic lower bounds are written arguments. Literature priority for this combination is unestablished.

From the root of this fork, replay the standalone target with the pinned toolchain:

```sh
node tools/check-lean.mjs lean/PEqualNP/SparseSharing/CubeFilter.lean notes/star-intersection-atlas/four-gate-sharing/cube-embedding/CubeFilter.statement check
```

From this note's directory, run `python3 -I -B replay.py`. It checks all 4,096 edge subsets of the three-cube, a 256-vertex path, an irregular 176-vertex binary tree, and an exhaustive small tag dictionary. Two explicit false-positive controls exercise what happens if either the containment or tag test is dropped. These runs verify finite instances. They do not measure the minimum formula cost of those trees.

The contribution is the conversion from short cube edges to a small cover of the bipartite complement, with the resulting bounds in the free-union model. Heun and Mayr supplied the bounded-treewidth embedding, earlier tree embeddings are due to Bhatt and coauthors, and the tag codes and matching lower bound use classical results. The leading coefficient for unrestricted-degree forests and the first tree with an additive saving of two remain open here.
