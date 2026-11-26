# Replay the projective-plane sharing results

The proof sources, recorded statements and finite arithmetic check are pinned at `86eebd34bd9a70645c1fbf629d124e29a00efdad`. The repository pins Lean 4.36.0 and its mathlib dependencies.

```sh
git clone --single-branch --branch projective-plane-sharing https://github.com/sarveshkapre/pequalnp-proofs.git plane-sharing
cd plane-sharing
git checkout --detach 86eebd34bd9a70645c1fbf629d124e29a00efdad
(cd lean && lake exe cache get)
```

From the checkout root, the following commands can run offline once the pinned toolchain and dependency cache are in place.

```sh
node tools/check-lean.mjs lean/PEqualNP/PlaneSharing/Transfer.lean notes/star-intersection-atlas/plane-sharing/Transfer.statement check
node tools/check-lean.mjs lean/PEqualNP/PlaneSharing/DualRail.lean notes/star-intersection-atlas/plane-sharing/DualRail.statement check
python3 -IB notes/star-intersection-atlas/plane-sharing/check_coordinates.py
```

| Formal statement | Official Mac verdict | Kernel constants checked |
|---|---|---:|
| A rectangle formula using $k$ paid unions has a bipartite formula with at most $\max(2,4k)$ unary leaves. | `ACCEPTED (check)` | 1,674 |
| A sequence of $k$ Boolean AND gates with complemented wires can retain every available wire using $k$ paid intersections and free unions. | `ACCEPTED (check)` | 1,666 |

Both axiom lists consist of `propext`, `Classical.choice`, and `Quot.sound`. All 88 distinct source hashes across the two verifier manifests matched the pinned commit. The source statement of the first theorem uses complements of the target cells. The second theorem uses the incident cells directly.

The Python control uses only the standard library. It compares packed convolution and reversed-polynomial division with schoolbook multiplication and long division, and checks the complete incidence matrices and their Gram identities at orders 2, 3, 4, 5, 7, 8, 9, 11, 13 and 16. The expected last line is `Passed 144186 point-line pairs across 10 fields.`

The asymptotic conclusion uses the two checked translations plus the finite-geometry, sign-rank and bit-complexity arguments in the [mathematical proof](THEOREM.md).
