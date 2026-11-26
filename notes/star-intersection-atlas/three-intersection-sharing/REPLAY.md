# Replay the 8×8 circuit and formula proof

Unions of row and column stars are free, and each binary intersection costs one. A circuit may reuse a gate's result. A formula pays for each occurrence. For the graph defined by the zero-set matrix in `ThreeIntersectionsRectangleGap.lean`, the exact costs are three and four respectively.

The proof extends pjscruggs's two-intersection classification. The original `TwoIntersections.lean` is in the parent directory at base revision `7da7d81614b93ea808c11ac27f27136942fec385`. The small example and the three-intersection classification are due to this follow-up.

## Set up

Use a fresh checkout with the pinned Lean 4.36.0 toolchain. From a shell with Git, elan and Lake installed, run

```sh
git clone --single-branch --branch three-intersection-sharing https://github.com/sarveshkapre/pequalnp-proofs.git three-intersection-sharing
cd three-intersection-sharing/lean
lake exe cache get
```

## Check the proof

From the same `lean/` directory, run the following block. It compiles the nine required modules from source in a new temporary directory. Once the pinned dependencies are installed, this step can run offline.

```sh
(
  set -eu
  atlas="../notes/star-intersection-atlas"
  proof="$atlas/three-intersection-sharing"
  out=$(mktemp -d)
  cp "$atlas/TwoIntersections.lean" "$proof"/*.lean "$out/"
  LEAN_PATH="$out"
  for dep in "$PWD"/.lake/packages/*/.lake/build/lib/lean; do
    if [ -d "$dep" ]; then LEAN_PATH="$LEAN_PATH:$dep"; fi
  done
  export LEAN_PATH
  for module in TwoIntersections ThreeIntersections ThreeIntersectionsQuadrangle \
    ThreeIntersectionsSharingGap ThreeIntersectionsFormula ThreeIntersectionsRectangleGap \
    ThreeIntersectionsCubeGap ThreeIntersectionsBoxes ThreeIntersectionsSeparation; do
    lean --root="$out" -o "$out/$module.olean" "$out/$module.lean"
  done
)
```

The final module prints the axiom report for `ThreeIntersectionsSeparation.exact_circuit_formula_gap`. On the independent Mac replay it used only `propext`, `Classical.choice` and `Quot.sound`. The theorem supplies the three-gate circuit and a four-gate formula, and proves the matching lower bounds. No external SAT certificate is needed.
