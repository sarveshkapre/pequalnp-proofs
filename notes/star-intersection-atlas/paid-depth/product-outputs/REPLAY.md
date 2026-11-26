# Replaying the output and tensor results

Use this revision of the fork’s paid-depth-tradeoff branch, with the pinned Lean 4.36.0 toolchain and Mathlib dependencies. The parent revision is e113253a3e25fadab8b8d8e655ea70e63b046206. From the repository root, with the dependencies cached, the checks run offline.

~~~sh
for name in CommonOutputBank SimultaneousEqualityLower
do
  node tools/check-lean.mjs "lean/PEqualNP/PaidDepth/$name.lean" \
    "notes/star-intersection-atlas/paid-depth/product-outputs/$name.statement" check || exit 1
done
python3 -IB notes/star-intersection-atlas/paid-depth/product-outputs/check_products.py
~~~

| Formal statement | Official Mac verdict | Constants rechecked | Distinct project modules hashed |
| --- | --- | ---: | ---: |
| [CommonOutputBank](CommonOutputBank.statement) | ACCEPTED (check) | 1,679 | 87 |
| [SimultaneousEqualityLower](SimultaneousEqualityLower.statement) | ACCEPTED (check) | 1,682 | 89 |

Both verdicts report the axioms `propext`, `Quot.sound`, and `Classical.choice`. The second theorem imports the first and the earlier checked `OptionalEqualityBank`. Its depth parameter `d` counts levels above the first paid gate, so the mathematical depth is `D = d + 1`. Its alphabet has `n + 2` symbols. It quantifies over all circuit wiring and both raw output shores. [Simultaneous proof](THEOREM.md)

The balanced upper construction, exact depth-one count, single-query comparison, and tensor limit are written proofs. Independent finite controls give the following results. The crossing and bit-set computations use Python’s standard library. [Tensor proof](TENSOR.md) · [Control source](check_products.py)

- Exhaustive gate generation finds 8,776 distinct depth-one gates on the four-word grid. Exact joint set cover agrees with the predicted optimum for all eight families of nonempty equality masks on two binary coordinates.
- The common bank reconstructs all 64 choices of gate taps in each of 128 independently generated six-gate circuits, from direct cell truth tables.
- The balanced constructors reproduce 15,552 selected-mask and independently wildcarded cells across five parameter settings, including digit encodings with unused labels.
- The four-symbol disequality relation has integral cover number four. The one- and two-copy fractional constructions cover all positive cells with the required multiplicities, giving fractional optima three and nine by the matching area bounds.

| Input | SHA-256 |
| --- | --- |
| CommonOutputBank.lean | `d0c9ed79a1a68ca0d80a86ca82fd602c98401bb41a87dbfc24cf205962b3381c` |
| SimultaneousEqualityLower.lean | `c7f41033326a2e36a3838adceaa0aed160dd4962cf194ebc8302b875fa63bc14` |
| check_products.py | `7f3b24bfca79d70918b525b26c6603c06b0b37d69f2316ac107b5512bbb1c3dc` |
| check-lean.mjs | `c8fc4b209e678f76adc3cf4e988be55675ef9384e44cd388203c95c6afb68846` |
