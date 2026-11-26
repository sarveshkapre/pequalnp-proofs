# Replay the 5×6 quadrangle proof

Pjscruggs supplied the graph, the four-intersection construction, the SAT formula and the LRAT certificate in [Discussion #19729](https://github.com/open-goat/pequalnp-proofs/discussions/19729#discussioncomment-19903435). This branch adds a Lean proof that every three-intersection construction for that same graph would satisfy the formula, including constructions with free unions and reuse of earlier gates. The certificate rules out such an assignment. Together with the four-intersection construction this gives the exact minimum for this example.

## Replay

Use a fresh clone of the proof branch. It includes the hand-back at `7da7d81614b93ea808c11ac27f27136942fec385`, the proof sources and the original checker. Provision the project's pinned Lean 4.36.0 toolchain and mathlib cache in an isolated environment with Git and Node.js available.

```sh
git clone --single-branch --branch quadrangle-5x6-lean-replay https://github.com/sarveshkapre/pequalnp-proofs.git quadrangle-replay
cd quadrangle-replay
(cd lean && lake exe cache get)
```

After provisioning, the proof can be checked offline. From the repository root, run

```sh
(cd lean && LEAN_NUM_THREADS=2 lake build +PEqualNP.Quadrangle.LowerBound)
node tools/check-lean.mjs lean/PEqualNP/Quadrangle/LowerBound.lean notes/star-intersection-atlas/lean-certificate/LowerBound.statement check
(cd lean && lake env lean ../audit/InspectAxioms.lean)
```

The unmodified checker returned `ACCEPTED (check)` for `PEqualNP.Quadrangle.LowerBound` in the local Mac replay. The verifier run took about 23 minutes and used about 14 GiB of memory. Lean also checked the combined theorem `PEqualNP.Quadrangle.ExactMinimum`. Its reported axioms were `propext`, `Quot.sound` and `Classical.choice`.

[Theorem](../../../lean/PEqualNP/Quadrangle/LowerBound.lean) · [Circuit-to-formula proof](../../../lean/PEqualNP/Quadrangle/Encoding.lean) · [Certificate replay](../../../lean/PEqualNP/Quadrangle/Certificate.lean)
