# When does sharing save an intersection on five rows?

In the row-and-column star model, unions are free and each binary intersection costs one. A circuit can reuse an intermediate result. A formula pays for each occurrence. On five rows, a graph of circuit cost three and formula cost four exists at exactly the following widths.

| Allowed columns | Widths |
| --- | --- |
| Column neighborhoods may repeat | Every integer from 7 onward |
| Column neighborhoods are pairwise distinct | Every integer from 7 through 22 |

These results build on pjscruggs’s two-intersection classification and star-intersection atlas, the three-gate normal forms from the 8×8 example, and the five-by-six classification. [Original atlas](https://github.com/pjscruggs/pequalnp-proofs/tree/7da7d81614b93ea808c11ac27f27136942fec385/notes/star-intersection-atlas) · [8×8 discussion](https://github.com/open-goat/pequalnp-proofs/discussions/23239) · [5×6 classification](../full-classification/REPLAY.md)

## The seven-column example

Here a 1 means that the row and column are joined by an edge.

```text
1010101
0110011
1011010
0011100
1100000
```

These are the first seven columns of a single 22-column graph with pairwise distinct neighborhoods. Its circuit shares one intermediate result and uses three intersections. A formula with three intersections on any prefix of width at least seven would restrict to a formula of the same cost on these seven columns. The Lean proof excludes every such formula. Expanding the shared expression gives a formula using four. Repeating columns preserves both costs at arbitrarily large widths. Widths below seven are ruled out by the 5×6 classification. [Seven-column lower bound](../../../lean/PEqualNP/FiveRows/Core.lean) · [22-column construction](../../../lean/PEqualNP/FiveRows/Geometry.lean)

For the upper cutoff, four of the five circuit shapes already have a formula of cost three. In the remaining shape, a column chooses its memberships in six rectangles. This gives 64 choices. Each row tests these choices, and there are 26 different row tests. Lean checks that every selection of five row tests lies in one of 126 lists and that even the full list distinguishes at most 22 kinds of columns. Thus a 23rd column must repeat an existing neighborhood in this shape. The formal statements use the zero cells of the graph. Complementing exchanges unions and intersections and preserves which columns have equal neighborhoods. [Partition argument](../../../lean/PEqualNP/FiveRows/Partition.lean) · [Checked finite certificate](../../../lean/PEqualNP/FiveRows/Templates.lean)

## Replay both official checks

With Git, Node.js and Lean’s toolchain manager installed, run the following commands from a fresh checkout. The proof revision pins Lean 4.36.0 and its library dependencies. The cache step needs network access on the first run. With the dependencies cached, both verifier commands can run offline.

```sh
git clone --single-branch --branch five-row-widths https://github.com/sarveshkapre/pequalnp-proofs.git five-row-widths
cd five-row-widths
git checkout --detach f34365b412bd7952c3c026971c16ec8b72061f2e
(cd lean && lake exe cache get)
node tools/check-lean.mjs \
  lean/PEqualNP/FiveRows/AllWidths.lean \
  notes/star-intersection-atlas/five-row-widths/AllWidths.statement check
node tools/check-lean.mjs \
  lean/PEqualNP/FiveRows/DistinctWidths.lean \
  notes/star-intersection-atlas/five-row-widths/DistinctWidths.statement check
```

Each command checks its own recorded statement and rechecks the project declarations the proof uses. [Unrestricted theorem](../../../lean/PEqualNP/FiveRows/AllWidths.lean) · [Distinct-column theorem](../../../lean/PEqualNP/FiveRows/DistinctWidths.lean)

The official checker returned the following results on a Mac with cached dependencies. Both runs used only `Quot.sound`, `propext` and `Classical.choice`. Every source hash in each verifier manifest matched the pinned proof revision.

| Theorem | Verdict | Constants rechecked | Source hashes matched | Elapsed |
| --- | --- | ---: | ---: | ---: |
| `PEqualNP.FiveRows.AllWidths` | `ACCEPTED (check)` | 3,486 | 114 | 5 min 42 s |
| `PEqualNP.FiveRows.DistinctWidths` | `ACCEPTED (check)` | 3,555 | 118 | 6 min 9 s |
