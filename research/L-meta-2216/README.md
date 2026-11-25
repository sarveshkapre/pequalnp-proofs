# What a 61-gate circuit would have to do

[L-meta-2216](https://pequalnp.com/lemma#L-meta-2216) asks whether 61 AND/OR gates can solve the point–line incidence problem after one point has been removed from the plane of order 3. The circuit must also supply a second wire. Whenever the main output is false, this wire must say whether any of the four lines through the missing point was selected.

Amritpal-Nijjar previously reported a 62-gate circuit passing the boundary tests in [PR #8694](https://github.com/open-goat/pequalnp-proofs/pull/8694). The [Lean file](L_meta_2216_partial.lean) checks a 62-gate construction and proves that 62 is optimal when neither output is fed by an AND whose two inputs both trace back to line inputs. “Trace back” refers to the wiring. The two paths may start at the same line.

The argument puts the missing point back with an AND and an OR, following [the original reduction](https://github.com/open-goat/pequalnp-proofs/pull/4212) and [the checked restoration](https://github.com/open-goat/pequalnp-proofs/pull/4340). A 61-gate circuit with the restriction would give a 63-gate circuit for the full plane with the same restriction. [The full-plane bound](https://github.com/open-goat/pequalnp-proofs/pull/4507) requires at least 64.

The restriction also gives a test for candidate designs. Consider all inputs with at most one selected line. Replace any AND that is constant on those inputs or agrees with an earlier wire on all of them. The proof shows that, after these replacements, a correct 61-gate design would still need an AND combining two line-connected wires on a path to either output. A design using such a gate is the open case.

## Replay the proof

With Git and elan installed, run the following from this branch's repository root. The branch is based on upstream commit `e6bfe1a56efc768d244627b78f175b18de1acd6f` and uses the project's pinned Lean 4.36.0 and Mathlib.

```sh
cd lean
lake exe cache get
lake build +PEqualNP.Outside.L_meta_2420
lake env lean ../research/L-meta-2216/L_meta_2216_partial.lean
```

The two results to look for are `PuncturedPlane.exact_linear_minimum` and `PuncturedLineBound.Compression.necessary_after_simplification`.
