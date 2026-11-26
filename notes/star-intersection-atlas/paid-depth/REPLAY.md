# Replay the paid-depth results

The proof sources and independent controls are pinned at f0b1426a29fae120743f3f3f99bc8f7a14b9c2d9 on the paid-depth-tradeoff branch. The checkout uses Lean 4.36.0. With the pinned toolchain and matching Mathlib cache prepared, run the following from the root of an isolated checkout.

```sh
git checkout --detach f0b1426a29fae120743f3f3f99bc8f7a14b9c2d9
for name in FoolingBound DigitFormula ParallelComplement
do
  node tools/check-lean.mjs "lean/PEqualNP/PaidDepth/$name.lean" \
    "notes/star-intersection-atlas/paid-depth/$name.statement" check || exit 1
done
python3 -IB notes/star-intersection-atlas/paid-depth/check_depth.py
python3 -IB notes/star-intersection-atlas/paid-depth/check_complement.py
python3 -IB notes/star-intersection-atlas/paid-depth/check_affine.py
```

## Mac verifier results

The unchanged official checker returned `ACCEPTED (check)` for all three standalone statements on the Mac in a credential-free, network-disabled sandbox. The source-hash manifests cover 89 distinct files. Every hash matches the pinned proof commit. The three reported axioms were propext, Classical.choice and Quot.sound.

| Theorem | Constants rechecked |
| --- | ---: |
| FoolingBound | 1679 |
| DigitFormula | 1668 |
| ParallelComplement | 1669 |

## What each theorem checks

- **FoolingBound.** Every accepted cell of an arbitrary circuit has a rectangle certificate. Distinct fooling-set cells receive different index subsets of size at most two to the power of the zero-based gate level. The bank has eight indices per gate and two for the output.
- **DigitFormula.** Starting with row and column tests, a balanced formula tests whether all digits match. Both the paid cost and the permitted depth follow from the formula rules.
- **ParallelComplement.** Given all raw operands of a parallel circuit, the complement has a formula at the displayed depth and cost. A label explicitly selects a false operand for each gate in a block. The source can include final raw output stars.

The binomial estimates, graph decompositions, geometric application and joint asymptotic statements are in the [written proof](THEOREM.md).

## Independent finite controls

The first script evaluates the constructed formulas on all 8,704 labelled graphs of sizes 3 by 3, 3 by 4 and 4 by 3, at three depth budgets. The 4,040 forests include graph labellings on transposed grids. It separately checks 32,203 positive gate/cell certificates from circuits with reused wires, including containment of the full rectangle in the gate output.

The second script compares both bounded-depth constructions with direct evaluation on all 65,536 ordered two-gate sources on the 2 by 2 grid, including different syntactic descriptions of the same gate. It also tests 600 padded sources on a 4 by 5 grid at four block widths, with output stars and empty sources.

The third constructs and evaluates binary gate operations for carry-save summation, carry prefixes and comparison with multiples of the characteristic. Across 931 systems with one or more equations over primes 2, 3, 5, 7 and 17, the computed answer agrees with direct modular matrix multiplication. The finite control tests the affine arithmetic inside the written translation-plane proof.
