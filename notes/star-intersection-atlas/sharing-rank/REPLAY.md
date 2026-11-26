# Replaying the sharing and rank theorem

Use the Lean and mathlib revisions pinned by the repository. The graph lives in the finite row- and column-star model. In the Lean files the graph is represented by its zero cells, so the paid binary intersections of the edge graph appear as binary unions of zero sets. All ranks use the real field.

From the fork, check out the proof commit listed below. Run the cache command once to fetch the pinned build dependencies. The remaining commands can run offline with that cache on a machine with Git, Lean, Node, and Python 3.

```sh
git clone --single-branch --branch sharp-sharing-rank https://github.com/sarveshkapre/pequalnp-proofs.git sharing-rank
cd sharing-rank
git checkout --detach 7fa107e37fad8b028af6b1050f5fb8ae68bd076d
(cd lean && lake exe cache get)
```

## Official verifier

Run each command from the checkout root. The checker rebuilds the named theorem, reads the statement against the pinned library, independently checks the project constants, and reports its verdict and a source-hash manifest.

```sh
node tools/check-lean.mjs lean/PEqualNP/SharingRank/Rigidity.lean notes/star-intersection-atlas/sharing-rank/Rigidity.statement check
node tools/check-lean.mjs lean/PEqualNP/SharingRank/NoFlatFamily.lean notes/star-intersection-atlas/sharing-rank/NoFlatFamily.statement check
node tools/check-lean.mjs lean/PEqualNP/SharingRank/ExactFamily.lean notes/star-intersection-atlas/sharing-rank/ExactFamily.statement check
```

- `Rigidity` gives the general rank bound and the two-unit loss whenever a port differs from its canonical flat formula.
- `NoFlatFamily` excludes every clipped intersection of k unions of two rectangles on the witness family, for every k ≥ 3.
- `ExactFamily` asserts that for each k ≥ 3 one and the same finite graph has rank 3^k − 2, minimum circuit cost k, and minimum formula cost k + 1. The recorded formula predicate is the least class generated from rectangles by free intersections and paid unions. The conversion to and from finite expression trees is proved in `Records.lean`. The general upper bound for graphs that require sharing follows from `SharingRank.ceiling`.

## Mac verification

All three commands returned `ACCEPTED (check)` on the proof commit above. The independent kernel rechecked 1,716 constants for Rigidity, 1,697 for NoFlatFamily, and 2,058 for ExactFamily. The three axiom lists contained only `propext`, `Classical.choice`, and `Quot.sound`. Each manifest’s source hashes were compared with the committed files. The official verifier, toolchain pin, dependency manifest and build scripts matched upstream.

## Independent checks

```sh
python3 -IB notes/star-intersection-atlas/sharing-rank/check.py
```

This standard-library calculation independently constructs the circuit and formula, recovers their polynomial coefficients, and checks the fooling set. It enumerates all normalized dependency patterns at budgets one through three and directly eliminates the full zero-cell matrices over GF(2) at budgets three through five. The three direct ranks are 25, 79 and 241. Together with the real rank upper bound, each modular calculation determines the real rank on that instance.

The proof for all k is in [the theorem and construction](THEOREM.md). The [Lean sources](../../../lean/PEqualNP/SharingRank) include the real-matrix calculation, explicit circuit, formula construction and both lower bounds.
