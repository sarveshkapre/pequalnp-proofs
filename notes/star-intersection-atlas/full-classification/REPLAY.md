# The unique four-intersection graph on a 5×6 grid

Among all bipartite graphs with five labeled rows and six labeled columns, the only one that needs four intersections is pjscruggs’s quadrangle, up to independent row and column permutations. Four is its exact cost both for circuits, which can reuse an intermediate wire, and for formulas, which pay again for each repeated subcomputation. Every other graph admits a formula using at most three intersections. This rules out a three-versus-four circuit–formula gap at this size.

Pjscruggs introduced the example, gave its four-intersection construction and certified its three-intersection obstruction. Their atlas established uniqueness among graphs with no four-cycle. The new result covers every graph, including those containing a four-cycle. The proof uses the existing structural lower bound for the quadrangle. [Original atlas](https://github.com/pjscruggs/pequalnp-proofs/tree/7da7d81614b93ea808c11ac27f27136942fec385/notes/star-intersection-atlas) · [Structural lower bound](https://github.com/sarveshkapre/pequalnp-proofs/blob/c70874050bbd170dc7694d6f77a3f2fa78deb5cd/notes/star-intersection-atlas/quadrangle-structural/QuadrangleStructural.lean)

## Replay the official check

The proof revision pins Lean 4.36.0 and the project dependencies. With Git, Node and Lean’s toolchain manager installed, run these commands in a fresh checkout. The cache command downloads the pinned library dependencies. Once those dependencies are available, the check can run offline.

```sh
git clone --single-branch --branch five-by-six-classification https://github.com/sarveshkapre/pequalnp-proofs.git atlas56
cd atlas56
git checkout --detach a4cb83d5c019ce69715de84fbeece5a6b8b62579
(cd lean && lake exe cache get)
node tools/check-lean.mjs \
  lean/PEqualNP/Atlas56/FullClassification.lean \
  notes/star-intersection-atlas/full-classification/FullClassification.statement check
```

On the Mac, the unchanged official checker returned `ACCEPTED (check): PEqualNP.Atlas56.FullClassification` in 5 minutes 48 seconds with cached dependencies. Its independent kernel pass checked 3,156 constants and reported only `Quot.sound`, `propext` and `Classical.choice`. The SHA-256 hashes in the verifier manifest match all 24 proof modules and 86 project definition modules at the pinned proof revision.

## How the proof works

The atlas starts with row and column stars, allows free unions and counts binary intersections. The Lean statement works on zero cells, the complement of the graph. In these coordinates the available sets are rectangles, intersections are free and each binary union costs one. Complementation exchanges the operations and preserves their cost. The exceptional graph is specified directly by its five edge-row masks, `49, 42, 22, 13, 3`. [Theorem](../../../lean/PEqualNP/Atlas56/FullClassification.lean#L62) · [Recorded statement](FullClassification.statement)

For each nonexceptional graph, its zero cells have the form `(A ∪ B) ∩ (C ∪ D) ∩ (E ∪ F)` for six rectangles. This is a formula with three paid operations. Fixing which rectangles contain each row leaves 64 choices for the six rectangle memberships of a column. Lean checks a table of these choices, then proves that every set of at most six five-bit column patterns either has one compatible row assignment or consists of the quadrangle’s six columns up to relabeling. Repeated columns can use the same choice. The last step applies the quadrangle lower bound in the exceptional case. [Finite cover](../../../lean/PEqualNP/Atlas56/Finite.lean) · [From column patterns to arbitrary graphs](../../../lean/PEqualNP/Atlas56/Semantics.lean) · [Bounds for the two cases](../../../lean/PEqualNP/Atlas56/Classification.lean)

For a short independent replay of the constructive cover, run the following from the repository root. The script uses only the Python standard library. It shows the 12 row assignments, enumerates all 2,324,784 column multisets including repetitions, and checks that the 15 uncovered multisets are exactly the quadrangle’s row relabelings. Those give 10,800 labeled graphs after ordering the columns. The Lean check above verifies the cover directly. [Independent checker](check_cover.py)

```sh
python3 notes/star-intersection-atlas/full-classification/check_cover.py
```
