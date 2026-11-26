# How much symmetry can a full cover retain?

All statements on this page use the particular column permutation in [SymmetricPlane.lean](SymmetricPlane.lean). Once the columns are relabeled, rows and columns share the same 21 labels and the board is invariant under reflection across its diagonal.

## Fourteen symmetric rectangles

A collection closed under reflection consists of pairs of transposed rectangles and self-transpose squares. Pad to fourteen slots with empty squares and enlarge each pair or square as far as legality permits. Coverage can only increase. Off-diagonal holes occur in pairs. To improve on 334, this arrangement must cover every required off-diagonal cell and all but possibly one required diagonal cell.

Five boundary points have forbidden diagonals, so none can belong to a square. One point, the pole, is compatible with all sixteen nonboundary points and none of the boundary points. Each of the remaining fifteen labels is an edge of the Petersen graph. The [Lean model](SymmetricPlane.lean) checks the labels and the board entries. Each of the 120 boundary permutations induces a permutation of the whole board, as the replay verifies.

The SAT searches first exclude three paired slots on the boundary alone, covering all smaller pair counts by padding. Separate cases exclude four or five paired slots from covering 335 cells. With six or seven pairs, classify each pair by whether the pole belongs to two, one or zero sides. In a maximal rectangle the pole belongs to a side exactly when the opposite side has no boundary points. Only the zero-pole pairs cover boundary-to-boundary cells. At least three two-sided cuts of the five boundary points are needed. Assigning one side bit per cut must distinguish five points, which two bits cannot do.

All fifteen pole distributions for seven pairs are excluded, as are nine of the ten for six pairs. The last distribution has four two-sided boundary cuts covering all ten unordered boundary pairs. If a side contains at least three points, a distinguished cut can have sizes 4×1, 3×2 or 3×1, up to reversal. Otherwise some cut must be 2×2 because four cuts of area at most two cover at most eight pairs. Each case fails. The symmetric starting arrangement attains 334, so the bound is sharp.

The reductions produce [31 formulas](symmetric-replay.tsv). The [encoder](symmetric.py) assigns a Boolean to each side membership, forbids rectangles containing a forbidden cell and requires every specified target to be covered. The search breaks symmetries by ordering interchangeable slots and orientations, and by permuting boundary labels with the same distinguished role. A lexicographically maximal representative under those operations satisfies the imposed ordering. The square slots can be sorted independently.

## Twelve symmetric rectangles and two exceptions

Write the arbitrary rectangles as A×B and C×D. Cells still needed after the other twelve come in transpose pairs. Both orientations of a cell are coverable by the two exceptional rectangles exactly on the union of X×X, Y×Y, U×V and V×U, where X = A∩B, Y = C∩D, U = A∩D and V = B∩C. Each piece is legal, and every cell of (X∪Y)×(U∪V) is legal. Conversely the rectangles (X∪U)×(X∪V) and (Y∪V)×(Y∪U) realize those four pieces. The [five general lemmas](TwoUnmatched.lean) verify these reductions and two shortcuts. If either X∪Y or U∪V forms a legal square, the exceptional pieces can be replaced by a symmetric pair or two squares. The preceding 334 maximum rules out a full cover in each of those cases.

Let k count the transposed pairs among the ordinary twelve. Their remaining slots are squares. Extend the ordinary rectangles and the four special sets maximally subject to legality. A full cover still needs at least three cuts on the boundary. This excludes k = 0 and k = 1 because the exceptional pair contributes at most one such cut. The next three cases, k = 2, 3 and 4, were checked with all boundary profiles free.

For k = 5 and 6, classify ordinary pairs by pole membership and give the exceptional cut zero, one or two sides containing the pole. After excluding the distributions with too few cuts, 22 pole distributions remain for k = 5 and 35 for k = 6. Of these, 52 are excluded directly. In the other five, distinguish an ordinary cut of maximum boundary area. Orient it with side sizes a ≥ b. The sides are disjoint on the five boundary points, so a+b ≤ 5. With c ordinary cuts, at most cab boundary pairs are covered by them. The exceptional cut can add at most six when two-sided. Discard sizes with total below ten. The board symmetries place the chosen sides at the first a and next b boundary labels. The other boundary memberships are free subject to coverage and legality.

In the final small-cut branch, four ordinary cuts must cover ten boundary pairs. A cut with a side of size at least three is already covered by the unconstrained distinguished 3×1, 3×2 and 4×1 cases. Otherwise a 2×2 cut is necessary. This supplies the remaining small-side formula. The [complete 79-case manifest](two-unmatched-replay.tsv) consists of three whole cases, 52 pole distributions and 24 distinguished-cut checks. The [encoder](two_unmatched.py) also supplies a positive control using the fourteen-rectangle arrangement.

## Replay

From this directory, regenerate all formulas and match their SHA-256 digests.

```sh
python3 -B replay_symmetric.py /path/to/scratch/symmetric
python3 -B replay_two_unmatched.py /path/to/scratch/two-unmatched
```

To also solve the regenerated formulas and check each LRAT certificate, append `--lean-bin /path/to/lean-4.36.0/bin` to each command. This requires the toolchain’s CaDiCaL and substantially more time and disk space than regenerating the hashes. The drivers use [CheckCover.lean](CheckCover.lean), which checks the DIMACS round trip and verifies the proof using Lean’s standard LRAT checker. The recorded runs verified 6,312,017 certificate actions for the 31 symmetric cases and 10,734,274 actions for the 79 two-exception cases. The case reductions above are written arguments. The formal geometric lemmas and explicit witness lists are included in the [main Lean replay](../../README.md).
