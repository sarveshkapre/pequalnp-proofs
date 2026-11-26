# How much can sharing save on a forest?

Let C(G) be the minimum number of binary intersections needed to build a finite bipartite graph from its row and column stars. Unions are free and a circuit may reuse any wire. Let F(G) be the minimum for a formula, which pays separately for every occurrence of an intersection.

**If G is a forest, F(G) ≤ 8 C(G) + 2.** More generally, if its edges are covered by a forests, then F(G) ≤ 2a(4 C(G) + 1). A circuit of cost zero is already a formula of cost zero. Thus for positive circuit cost, the multiplicative saving from sharing is bounded by a constant on forests, independent of the number of vertices. The [7×7 tree](https://github.com/open-goat/pequalnp-proofs/discussions/23239#discussioncomment-19914235) shows that sharing can still save a gate. At k=3 the public five-shape classification already gives F ≤ 4 on every graph. The new conclusion concerns arbitrarily large k. The best constant and the possible growth of the *additive* saving are open here.

The more general parameter is the number t of **bipartite P4-free layers** covering the edges. Each layer is a disjoint union of complete bipartite components, with isolated vertices allowed. Different layers can overlap. For every circuit with k paid gates, there is a formula costing at most t(4k+1).

A [matching-number refinement](../four-gate-sharing/matching-bound/README.md) gives a uniform upper bound of 2k + log₂(k+1) + O(1) on forests. The construction labels the stars in each layer with equal-sized subsets. Its size depends on the maximum matching even when a tree has vertices of arbitrarily large degree.

## Proof

Take complements of all wires. A free union of stars becomes a rectangle A × B in the zero set, meeting wires is free, and joining two wires costs one. The cost and reuse conventions survive this change exactly.

1. **Describe a row with at most 2k+1 bits.** Before each paid join, either operand is a free meet of raw rectangles and past wires. The raw rectangles together contribute one row mask and one column mask. Once the column is fixed, the value of the operand therefore depends on just one new row-membership bit and the previous paid wires. Record the two new row bits for each join and one more for the final free meet. Rows with equal signatures have identical full neighborhoods. This argument uses the paid gates in topological order and permits arbitrary reuse.
2. **Choose one row for each signature before looking at the cover.** Replace each row by its representative in every layer. This preserves the union of the layers because the full neighborhoods agree. Replacing representatives separately inside each original layer could fail: two identical full rows can have different component labels within the same layer.
3. **Write each layer as a formula.** On representative rows, assign each nonempty biclique component the signature of one of its rows. The labels are distinct because each representative belongs to at most one component of that layer. Give an active vertex its component label. A cell is outside the layer exactly when the two labels differ or at least one vertex has no label. Each bit contributes two rectangles, one for each direction of disagreement. Include a vertex with no label on both sides of its bit test, so every cell incident to it is covered. A union of these 2(2k+1) rectangles takes 4k+1 paid joins. Taking a free meet across all layers gives the claimed formula for the full zero set.
4. **Apply the forest decomposition.** Root every component of a forest. Put parent–child edges with a row parent in one layer and those with a column parent in another. Each layer consists of disjoint stars. Applying this separately to each covering forest gives at most 2a layers. The formal proof uses Mathlib's `SimpleGraph.IsAcyclic` for the supplied forests and proves the parent-edge property from uniqueness of simple paths.

## Attribution and scope

pjscruggs supplied the star-intersection atlas and its two-gate framework. His [larger-plane antichain proof](https://github.com/pjscruggs/pequalnp-proofs/blob/42423ae1a3fa6fcf725671b247fe7d18ab2b2d00/notes/star-intersection-atlas/larger-planes.md) already records two operand-selection bits per gate on a row. Step 1 is the arbitrary-output version of that observation, with a final raw-mask bit. The [8×8 sharing discussion](https://github.com/open-goat/pequalnp-proofs/discussions/23239) and its later tree example motivate the question. Brânzei, Maji, Mehta and Mukherjee study the P4-free cover number and record its relation to star arboricity and arboricity in [*P4-free Partition and Cover Numbers*, Appendix E](https://www.cs.purdue.edu/homes/hmaji/papers/BMMM20.pdf). Equality labels for forests and bounded-arboricity graphs also occur in the work of [Harms, Wild and Zamaraev](https://theoretics.episciences.org/16611). For the broader graph complexity framework see [Pudlák, Rödl and Savický](https://users.math.cas.cz/~pudlak/graph-complexity.pdf) and [Cavalar and Oliveira](https://arxiv.org/abs/2503.14117).

The contribution here is the explicit conversion from any k-gate star circuit to a formula, including the choice of representatives before applying the existing cover. The literature search identified the decomposition and coding ingredients. Priority for the combined inequality is unestablished. A family with unbounded F/C must have unbounded P4-free cover number and hence unbounded arboricity; neither is a sufficient condition for such a gap.

## Replay

The official Mac verifier returned `ACCEPTED (check)` for the standalone forest-cover theorem. It rechecked 1,891 constants with only `Quot.sound`, `propext` and `Classical.choice`. Manifest replay: 93 distinct source hashes matched. [Verifier receipt and manifest](verification.txt).

Use the repository's pinned Lean 4.36.0 and matching Mathlib dependencies. From a checkout with its dependency cache available, run

```sh
(cd lean && lake build PEqualNP.SparseSharing.Arboricity)
node tools/check-lean.mjs lean/PEqualNP/SparseSharing/Arboricity.lean \
  notes/star-intersection-atlas/sparse-sharing/Arboricity.statement check
python3 -I -B notes/star-intersection-atlas/sparse-sharing/check_construction.py
```

[General cover theorem and equivalence to the project's three-gate circuit](../../../lean/PEqualNP/SparseSharing/SparseSharing.lean) · [Forest and arboricity theorems](../../../lean/PEqualNP/SparseSharing/ForestSimulation.lean) · [Standalone verifier statement](Arboricity.statement).

The independent finite check tests the conversion on every labelled forest of dimensions 3×3, 3×4 and 4×3 (328, 1,856 and 1,856 respectively). It also reconstructs the published tree and an overlapping two-layer cover in which identical full rows have different component labels. It checks construction, not optimality.
