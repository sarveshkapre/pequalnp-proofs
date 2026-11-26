# A tree where sharing one gate saves an intersection

The forest conjecture is false in the free-union row-and-column-star model. A connected bipartite tree with seven rows and seven columns needs exactly three binary intersections as a circuit and exactly four as a formula. An edge is one in the following matrix. Indices start at zero.

```text
0101000
0100100
1010100
1000001
1000000
0000110
0001000
```

Here is the entire tree. Letters `r` and `c` distinguish the two vertex classes.

```text
c6──r3──c0──r2──c4──r1──c1──r0──c3──r6
        │   │   │
        r4  c2  r5──c5
```

## Construction and exclusion

For each rectangle X let U(X) be its complement. This is a free union of row stars outside its row set and column stars outside its column set. The six rectangles below use little-endian masks. Bit 0 selects row or column 0.

| Rectangle | A | B | C | D | E | F |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Rows | 121 | 87 | 62 | 95 | 99 | 124 |
| Columns | 63 | 106 | 79 | 119 | 125 | 126 |

First compute H = U(A) ∩ U(B). The other two gates compute U(C) ∩ (U(D) ∪ H) and U(E) ∩ (U(F) ∪ H). Their free union is the graph. The circuit reuses H, while expanding its two occurrences gives a four-intersection formula.

To exclude a different formula with three or fewer intersections, take complements. Rectangles and intersections are now free and unions cost one. The published classification gives four possible forms, with arbitrary rectangles for the letters.

1. A ∪ B ∪ C ∪ D.
2. (A ∪ B ∪ C) ∩ (D ∪ E).
3. (A ∪ B) ∩ (C ∪ D) ∩ (E ∪ F).
4. A ∪ ((B ∪ C) ∩ (D ∪ E)).

A row and a column each carry at most six membership bits. Their bitwise AND gives exactly the rectangle memberships at their cell. `ForestFinite.lean` rules out every assignment for every form using the earlier seven-column profile search, with this tree’s masks. `ForestGap.lean` translates those exclusions back to formulas and uses the two-gate circuit classification to exclude circuits with at most two intersections. `ForestGraph.lean` exhibits paths from a common vertex and checks the edge count. Mathlib’s connectedness-and-edge-count theorem gives `SimpleGraph.IsTree`.

`ForestGap.tree_exact_gap` in `ForestCounterexample.lean` combines the standard tree predicate and both exact costs for the same graph. A separate standard-library Python replay checks the circuit on all 49 cells and rejects the four formula shapes. It finds and verifies a formula after each of the 14 single-vertex deletions. The deletion checks are supplemental. Absolute minimum size among trees is open in this work.

## Replay

The official verifier returned `ACCEPTED (check)` on an Apple silicon Mac for `PEqualNP.ForestSharing.ExactGap`. The kernel rechecked 2,399 constants with `propext`, `Quot.sound` and `Classical.choice`. All 100 distinct source hashes in the manifest matched the checkout. The run took 10 minutes 14 seconds with the pinned dependency cache available.

From the repository root, use the pinned Lean 4.36.0 toolchain and the matching Mathlib cache. Run the project verifier against the standalone statement:

```sh
node tools/check-lean.mjs lean/PEqualNP/ForestSharing/ExactGap.lean \
  notes/star-intersection-atlas/forest-sharing/ExactGap.statement check
```

The statement gives the 49 cells explicitly, defines both gate budgets, and asks for Mathlib’s tree predicate on the same adjacency relation. It uses complements, so its counted operation is union. [Lean entry point](../../../lean/PEqualNP/ForestSharing/ExactGap.lean) · [Exact statement](ExactGap.statement) · [Verifier output and source hashes](verification.txt)

For the supplemental circuit and vertex-deletion checks, use Python 3.10 or later:

```sh
python3 -B notes/star-intersection-atlas/forest-sharing/replay.py
```

## Provenance

The search started from the earlier unicyclic graph. Deleting each of its six cycle edges gives a three-intersection formula. For this witness, delete edge (row 0, column 2), detach the leaf at row 2 from column 1, and attach it instead to column 3. The displayed matrix relabels that leaf as row 6. A new circuit witness was fitted and checked on the resulting graph.

This uses pjscruggs’s two-gate classification, the three-gate circuit and formula normal forms that ChatGPT Pro developed for the 8×8 example, and the profile checking from the previous 6×6 and 7×7 proofs. The tree, its circuit and the exclusion for this matrix are the additions for the forest question.

- [Previous 7×7 example and verifier record](https://github.com/sarveshkapre/pequalnp-proofs/tree/4d9459b728c5df44552957836e6f7df3461c19e7/notes/star-intersection-atlas/c4-free-sharing)
- [Forest question in the sharing discussion](https://github.com/open-goat/pequalnp-proofs/discussions/23239#discussioncomment-19913585)
- [pjscruggs’s two-intersection classification](https://github.com/pjscruggs/pequalnp-proofs/blob/7da7d81614b93ea808c11ac27f27136942fec385/notes/star-intersection-atlas/TwoIntersections.lean)
- [Three-intersection classification](https://github.com/sarveshkapre/pequalnp-proofs/tree/aee10584644a7ea1a60706a18cba658e980df159/notes/star-intersection-atlas/three-intersection-sharing)
