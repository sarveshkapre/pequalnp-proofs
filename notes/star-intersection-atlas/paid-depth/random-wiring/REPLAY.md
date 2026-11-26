# Replay the gate-wiring results

The proof sources and finite controls are pinned to commit `4ccd99b26a9a667265c9b628b8fa12a5771ca0e4` on branch `paid-depth-tradeoff`. Use a dedicated checkout of that revision with the repository's Lean 4.36.0 and matching Mathlib cache. Prepare the dependencies before isolating the checkout. From the repository root in the offline environment, run the following.

```sh
for name in SupportBlocks SupportMass AnchorReduction
do
  node tools/check-lean.mjs "lean/PEqualNP/PaidDepth/$name.lean" \
    "notes/star-intersection-atlas/paid-depth/random-wiring/$name.statement" check || exit 1
done
python3 -IB notes/star-intersection-atlas/paid-depth/random-wiring/check_random_wiring.py
python3 -IB notes/star-intersection-atlas/paid-depth/random-wiring/check_anchors.py
```

**SupportBlocks** proves the rejection-certificate equivalence and row/column factorization for any gate partition under explicit least-prefixed-point assumptions. **SupportMass** proves the finite product bound for real masses obeying the true-count recurrence. **AnchorReduction** proves the soundness and completeness implications for the reduced closure, including feedback. Constructing that closure from row and column unions, counting paid gates, the reverse-greedy weighting argument, the derivation of the stochastic recurrence and its infinite-product estimate are written mathematical arguments. [Deterministic proof](INDEPENDENT_GATES.md) · [Random-wiring proof](THEOREM.md)

The two programs reconstruct the certificate relations independently of the Lean development and compare them with direct forward iteration. Each exhausts 256 two-gate diagrams allowing self-loops and 4,096 three-gate diagrams allowing off-diagonal feedback, including every output set and every cell on the universal raw grid. The support tests also compare all five polynomial coefficients over 4,096 ordered four-gate wirings under five exact probability laws. The anchor tests compare the two sides of the reverse-greedy estimate over all 32,768 ordered six-vertex graphs. Both programs include larger feedback examples.


## Official verification on macOS

All three statements returned `ACCEPTED (check)` with Lean 4.36.0 in the offline sandbox at the proof revision above.

| Statement | Kernel-rechecked constants | Axioms |
| --- | ---: | --- |
| SupportBlocks | 1,660 | propext, Classical.choice, Quot.sound |
| SupportMass | 1,667 | propext, Classical.choice, Quot.sound |
| AnchorReduction | 1,660 | Classical.choice, propext, Quot.sound |

All 89 distinct source digests in the three verifier manifests matched the committed source files.
