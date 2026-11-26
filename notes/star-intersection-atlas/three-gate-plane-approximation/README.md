# How much of a projective plane can three intersections recover?

For every finite projective plane of order `q ≥ 16`, the maximum score is **10q − 2**. A correct positive prediction earns one point and an incorrect positive costs one. A negative prediction earns zero. At order 16, three intersections can pick out 158 actual point–line incidences without a single false positive. Even a circuit willing to accept false positives cannot improve that score.

The inputs are individual point and line stars. Unions are free, each binary intersection costs one, and its result can be reused. Planes need no field coordinates. The construction works for every order at least three. The upper bound starts at order 16.

## Proof

- [The construction](../../../lean/PEqualNP/ThreeGateGain/GainAttainment.lean) chooses four points on a line and a fifth point off it. The five points and the five selected lines touch `10(q+1) − 12` distinct incidences. Three intersections recognize precisely those incidences.
- [The upper bound](../../../lean/PEqualNP/ThreeGateGain/UpperBound.lean) allows every choice of raw stars, earlier wires, and free output union. Each circuit gives a finite table of point and line labels. Once full stars and vertices with nonpositive contributions are cleared, large classes of identical labels force unique neighbors. Counting those neighbors and bounding the remaining rectangles reduces the problem to a [finite verification](../../../lean/PEqualNP/ThreeGateGain/FiniteVerdicts.lean) independent of the plane order.
- [The exact maximum](../../../lean/PEqualNP/ThreeGateGain/Exact.lean) is stated for ordinary gate-by-gate circuits using at most three intersections. Lean proves both directions between these circuits and the word description used in the two independently specified verifier statements.

[How the finite certificate works](FiniteCertificate.md) describes the nine representative tables and the checks on their branches.

## Replay

The source tree uses upstream revision `1813aca84eec368df7970e54c4b11eb9f9bd0e63`, Lean 4.36.0, and the library revisions in the Lake manifest. From a fresh checkout with Git, Node.js and elan installed, fetch the pinned dependencies first.

```sh
git clone --branch research/three-gate-plane-gain --single-branch https://github.com/sarveshkapre/pequalnp-proofs.git plane-gain
cd plane-gain
(cd lean && lake exe cache get)
```

The proof checks can then run offline from the repository root.

```sh
proof=lean/PEqualNP/ThreeGateGain
spec=notes/star-intersection-atlas/three-gate-plane-approximation
node tools/check-lean.mjs "$proof/UpperBound.lean" "$spec/UpperBound.statement" check
node tools/check-lean.mjs "$proof/Attainment.lean" "$spec/Attainment.statement" check
(cd lean && lake build +PEqualNP.ThreeGateGain.Exact)
```

The first two commands compare the theorem types with self-contained statements and run the upstream verifier. The last builds the exact-maximum corollary and prints its axiom dependencies.

The unchanged upstream checker returned `ACCEPTED (check)` for [the upper bound](UpperBound.verification.json) and [the construction](Attainment.verification.json) on a Mac. It rechecked 8,464 and 2,093 constants respectively. Both proofs used only `propext`, `Classical.choice` and `Quot.sound`. Each receipt records the statement hash and all module hashes returned by the checker.

pjscruggs supplied the star-intersection model and the earlier low-budget normal form. The earlier two-intersection approximation supplies a rectangle bound used here. This proof establishes sharp optimality for the next intersection budget. [Pinned starting model](https://github.com/pjscruggs/pequalnp-proofs/blob/7da7d81614b93ea808c11ac27f27136942fec385/notes/star-intersection-atlas/TwoIntersections.lean) · [Two-intersection approximation](https://github.com/open-goat/pequalnp-proofs/discussions/19729#discussioncomment-19929446)
