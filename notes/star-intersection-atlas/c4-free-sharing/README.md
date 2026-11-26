# A four-cycle-free graph where reusing an intersection saves a gate

**Counterexample.** The following bipartite graph has seven vertices on each side and fourteen edges. Its minimum in the free-union row-and-column-star model is three binary intersections for a circuit and four for a formula. A one denotes an edge. Both sides are ordered from 0 through 6.

```text
0111000
0100100
0100000
1010100
1000001
1000000
0000110
```

Any two rows have at most one common neighbor, which rules out a four-cycle. The graph is connected. Its unique cycle visits row 0, column 2, row 3, column 4, row 1 and column 1 before returning to row 0. A separate constructive check finds a formula using at most three intersections after deleting any single vertex. This establishes deletion-minimality for this example. The smallest possible dimensions of a four-cycle-free example remain undetermined here.

## The three gates

Let A through F be rectangles with the following row and column membership masks. Bit 0 selects vertex 0. For each rectangle X, write U(X) for its complement. This is the free union of all row stars outside its row side and all column stars outside its column side.

| Mask | A | B | C | D | E | F |
|---|---:|---:|---:|---:|---:|---:|
| Rows | 107 | 53 | 126 | 63 | 71 | 120 |
| Columns | 107 | 63 | 79 | 115 | 125 | 126 |

Compute H = U(A) ∩ U(B). The other two paid gates compute U(C) ∩ (U(D) ∪ H) and U(E) ∩ (U(F) ∪ H). Their free union is the graph. The circuit computes H once and reads it twice. Expanding the two occurrences into separate subtrees gives a four-intersection formula.

## Why a different three-intersection formula cannot work

In the complement, or zero-set, presentation, rectangles and their intersections are free. Each binary union costs one. The published classification says any formula of cost at most three has one of these four forms, for some choice of rectangles.

1. A ∪ B ∪ C ∪ D.
2. (A ∪ B ∪ C) ∩ (D ∪ E).
3. (A ∪ B) ∩ (C ∪ D) ∩ (E ∪ F).
4. A ∪ ((B ∪ C) ∩ (D ∪ E)).

For a fixed form, assign one bit per rectangle to every row and every column. The bits indicate membership in that rectangle’s row or column side. Their bitwise AND gives all rectangle memberships at their cell. This parametrizes **every** choice of rectangles, including empty and repeated rectangles. Each of the four forms fails on the complement of the displayed matrix. The two-gate circuit classification expresses every such circuit as a formula of cost at most two, so the formula exclusion proves the circuit lower bound as well.

The Python checker uses constraint propagation in both directions and explores every remaining choice. The Lean proof proceeds differently. It chooses row profiles successively, intersects each column’s remaining domain, and proves inside the kernel that every branch closes. The final declaration joins four-cycle-freeness, the circuit upper and lower bounds, and the formula upper and lower bounds for this same matrix.

## Discovery and replay

The one extra three-gate circuit form uses six rectangle leaves. Of 64 row membership codes there are 26 distinguishable profiles on the full set of column codes. Symmetry gives the same count on the other side. The search acts on the **edge** matrix, the complement of the normal form. For a pair of candidate rows with common neighbors, a four-cycle-free submatrix either omits one of the rows or keeps at most one common column. The algorithm branches on these alternatives and can also transpose. Identical rows can be restored by duplication. A row adjacent to every column can be restored by excluding it from every zero rectangle. Four or fewer rows always admit a three-union zero formula, using one rectangle per row. The column reductions follow by symmetry.

The first large witness found by the search had 11 rows and 10 columns. Its seven row representatives 27, 29, 30, 45, 46, 47, 53 and seven column representatives 31, 47, 54, 55, 58, 59, 61 give the example above. The short replay checks the selected profiles, every graph cell, all four formula exclusions with positive controls, the unique cycle and all 14 single-vertex deletions. It requires only Python 3.10+ and its standard library.

From the repository root, run the short replay. The optional second command repeats the search for the initial large witness.

```sh
python3 -B notes/star-intersection-atlas/c4-free-sharing/replay.py
python3 -B notes/star-intersection-atlas/c4-free-sharing/check.py --find
```

### Official Lean replay

From the repository root, use the pinned Lean 4.36.0 toolchain and the dependencies in `lean/lake-manifest.json`. With the project’s Mathlib cache available, run the following command.

```sh
node tools/check-lean.mjs lean/PEqualNP/C4FreeSharing/ExactGap.lean notes/star-intersection-atlas/c4-free-sharing/ExactGap.statement check
```

`PEqualNP.C4FreeSharing.ExactGap` names the matrix, writes out the cost model, excludes a four-cycle on four distinct endpoints, and proves both minima. The verifier reads the expected statement from `ExactGap.statement`. The connectivity, unique-cycle and vertex-deletion checks are in the separate Python replay.

The unchanged official verifier returned `ACCEPTED (check)` on an Apple silicon Mac with Lean 4.36.0. The kernel rechecked 2,164 constants using `propext`, `Quot.sound` and `Classical.choice`. All 95 distinct source hashes in the verifier manifest matched the checkout. The run took 6 minutes 18 seconds with the pinned dependency cache present. [Verifier output and source hashes](verification.txt)

## Attribution and scope

pjscruggs supplied the two-intersection classification. The earlier Pro/Codex work supplied the five circuit forms and four formula forms, building on pjscruggs. The previous 6×6 work supplied the six-bit rectangle-profile lemmas and the basis for this kernel replay. Here we selected a four-cycle-free submatrix of the 26×26 profile matrix and verified its exact gap. Whether such a gap is possible on a forest is a separate question. The claim concerns representation on one row and one column with free star unions. The repeated-wire inequality for full Boolean incidence circuits uses a different model. No historical priority claim is made.

- [Pjscruggs’s two-intersection theorem](https://github.com/pjscruggs/pequalnp-proofs/blob/7da7d81614b93ea808c11ac27f27136942fec385/notes/star-intersection-atlas/TwoIntersections.lean)
- [Three-gate classification and formula theorem](https://github.com/sarveshkapre/pequalnp-proofs/tree/aee10584644a7ea1a60706a18cba658e980df159/notes/star-intersection-atlas/three-intersection-sharing)
- [Prior 6×6 sharing result and proof](https://github.com/open-goat/pequalnp-proofs/discussions/23239#discussioncomment-19912880)
