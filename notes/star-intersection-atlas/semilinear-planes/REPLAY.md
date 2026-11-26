# Replaying the semilinear-plane results

The four Lean files, their externally recorded statements, both finite controls, and the [mathematical proof](THEOREM.md) are pinned at `be060b2b804e481833dfc3305771acd2f3d3ee34`. The repository pins Lean 4.36.0 and its mathlib revision.

```sh
git clone --single-branch --branch semilinear-planes https://github.com/sarveshkapre/pequalnp-proofs.git semilinear-planes
cd semilinear-planes
git checkout --detach be060b2b804e481833dfc3305771acd2f3d3ee34
(cd lean && lake exe cache get)
```

With the pinned compiler and dependency cache available, the following checks run offline from the checkout root.

```sh
for name in VariableShift TwistedNine DenseDifferences NormCoefficient; do
  node tools/check-lean.mjs "lean/PEqualNP/PlaneSharing/$name.lean" \
    "notes/star-intersection-atlas/semilinear-planes/$name.statement" check || exit 1
done
python3 -IB notes/star-intersection-atlas/semilinear-planes/check_hall.py
python3 -IB notes/star-intersection-atlas/semilinear-planes/check_density.py
```

| Accepted Lean statement | What the kernel checked | Constants rechecked |
|---|---|---:|
| `VariableShift` | An actual sequence of AND gates with complemented wires routes a vector according to selected powers of a fixed map. The count is three gates per bit per selector and both output polarities remain available. | 1,690 |
| `TwistedNine` | The nine slope maps are additive and their graphs are disjoint away from zero. The displayed two perspective triangles violate the conclusion of Desargues’ theorem in the projective completion. | 1,661 |
| `DenseDifferences` | The trace shear is bijective and the coefficients away from the two original positions are nonzero for a surjective difference of two scaled field automorphisms in a finite group action. | 1,672 |
| `NormCoefficient` | A sign and automorphism selected by a common preserved key, followed by a fixed automorphism and nonzero scaling, permute the field. This is the fibre argument used on each of the Hall slope coefficients. | 1,660 |

All four returned `ACCEPTED (check)` on the Mac. Across the source-hash manifests all 90 distinct sources matched the proof commit. The only axioms reported were drawn from `propext`, `Quot.sound` and `Classical.choice`.

The first Python control checks all 8,281 incidences, each pair of lines and each pair of points at order nine. It executes one explicit 93-intersection circuit as bit vectors over the entire grid. Its gate count is an implementation check. The Desargues witness has centre 0, top triangle (9,10,1), bottom triangle (18,20,3), and noncollinear crossings (90,58,28), in the numbering defined in the source.

The second control constructs the fields and recovers the coefficients from slope values by solving a Moore interpolation system. It independently tests the resulting polynomial on every field element. At Hall orders 81 and 729, respectively, all 3,240 slope differences had four nonzero coefficients and all 265,356 had six. The finite controls use only the Python standard library.

The all-orders conclusions combine the checked lemmas with the written coordinate expansions, the cited finite-plane construction, and published arithmetic and formula bounds. The four verifier verdicts refer to the four statements in the table.
