# Replay the smallest square with circuit cost 3 and formula cost 4

In the free-union row-and-column-star model, this 6×6 graph needs three binary intersections when gates can be reused and four when each occurrence is counted separately. Each line is one row, and a one marks an edge.

```text
110010
100101
010001
100000
111110
111000
```

## Check the 6×6 theorem

Use Git, Node.js, elan and the repository's pinned Lean 4.36.0 toolchain. In a fresh checkout, fetch the exact proof revision and provision the pinned dependency cache.

```sh
git clone --single-branch --branch six-by-six-sharing https://github.com/sarveshkapre/pequalnp-proofs.git six-sharing
cd six-sharing
git checkout --detach 40673918766addef3b9a4ff4d449dfcae2e24bac
(cd lean && lake exe cache get)
```

From the repository root, run the official checker. Once the dependencies are present, the check can run offline.

```sh
node tools/check-lean.mjs \
  lean/PEqualNP/SixSharing/ExactGap.lean \
  notes/star-intersection-atlas/six-by-six-sharing/ExactGap.statement check
```

A successful run prints a final line beginning with `ACCEPTED (check): PEqualNP.SixSharing.ExactGap`. The [recorded statement](ExactGap.statement) specifies all 36 cells, the two circuit budgets and the formula cost rules. [ExactGap.lean](../../../lean/PEqualNP/SixSharing/ExactGap.lean) proves that these rules agree with the inductive definitions. [SixSharing.lean](../../../lean/PEqualNP/SixSharing/SixSharing.lean#L97) combines the three-gate construction, the two-gate exclusion, the four-gate formula and the exclusion of every cheaper formula. The accompanying finite search is checked in Lean's kernel. On an Apple silicon Mac, the unchanged official checker returned `ACCEPTED (check)` for `PEqualNP.SixSharing.ExactGap` and rechecked 2,115 constants. Its only reported axioms were `propext`, `Quot.sound` and `Classical.choice`. The run took 10 minutes 19 seconds with the pinned dependency cache already installed.

## Check the smaller squares

[Pjscruggs's atlas](https://github.com/pjscruggs/pequalnp-proofs/tree/7da7d81614b93ea808c11ac27f27136942fec385/notes/star-intersection-atlas) supplied the two-intersection classification and the 5×5 census. In the [enumerator](../rectangle_atlas.cpp#L62-L96), each extension uses the preceding expression once. Its constructions are therefore formulas. All 3,014 symmetry classes receive a construction costing at most three, covering all 33,554,432 labeled 5×5 graphs. Every smaller square extends to a 5×5 graph, and restricting a formula to the original rows and columns preserves its cost bound. Together with the 6×6 theorem, this gives the smallest square for this gap.

To reproduce the computational part from the repository root with a C++17 compiler and Python 3, run

```sh
(
  set -eu
  cd notes/star-intersection-atlas
  out=$(mktemp -d)
  c++ -std=c++17 -O3 rectangle_atlas.cpp -o "$out/atlas"
  "$out/atlas" 5 > "$out/square5.txt"
  python3 check_atlas.py 5 "$out/square5.txt"
)
```

The 6×6 proof builds on [the three-intersection classification and 8×8 example](https://github.com/open-goat/pequalnp-proofs/discussions/23239). The contribution here is the explicit smaller witness, its exact circuit and formula bounds, and the link to the 5×5 cutoff. The verifier command above checks the 6×6 theorem. The census command checks the smaller dimension separately.
