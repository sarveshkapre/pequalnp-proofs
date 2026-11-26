# Eight positive roots for a product of trinomials plus one

For any two real polynomials `f` and `g` with at most three nonzero terms each, the polynomial `1 + f g`, if nonzero, has at most **eight distinct positive real roots**. The exponents can be arbitrarily large. A previous construction attains eight, so the bound is sharp. [Published eight-root witness](https://github.com/open-goat/pequalnp-proofs/blob/6cc3df5019880145e92446ed2e526ea7f169e408/lean/PEqualNP/Outside/L_gct_261.lean)

## Why nine looked possible

Expanding the product gives up to nine monomials, plus the constant one. Descartes’ rule of signs allows a ten-term polynomial to have nine positive roots. The nine product coefficients have extra structure. Writing the three coefficients of each factor down the side and across the top of a square makes each product coefficient an entry of a rank-one table. In every two-by-two rectangle, multiplying the entries on either diagonal gives the same answer.

Suppose nine distinct positive roots exist. Substituting `x = exp(t)` turns them into nine distinct real zeros of an exponential sum. Repeated applications of Rolle’s theorem constrain the signs and relative sizes of its coefficients. Together with the rectangle identities, these constraints reduce the possible orders of the exponents to separated groups, up to swapping the factors. The remaining exponent inequalities are incompatible. The final part of the source certifies the polynomial inequalities used to close those cases. The argument covers all real coefficients and includes factors with fewer than three terms. [Upper-bound proof](EightPositiveRoots.lean)

## What the files check

- `EightPositiveRoots.lean` imports Mathlib and proves `GapAudit.positive_root_count`. It counts distinct roots using the set of positive elements of the polynomial’s root multiset.
- `CheckStatement.lean` imports the compiled module and checks the theorem against the stated polynomial type. The axiom report contains `propext`, `Classical.choice`, and `Quot.sound`.
- `check_witness.py` independently checks the earlier construction by hedanbaomi, whose Lean source is linked above. Exact integer interval arithmetic gives alternating signs at nine increasing positive rational points. Continuity gives one root in each of the eight disjoint intervening intervals.

## Replay

The upper-bound source, its imported statement, and the compiled module passed Lean 4.36.0 and its standalone kernel checker. The verified upper-bound source has SHA-256 `1f89014c6c765f1dd71294f770a21d36dab05fbbfec83614af9cc19c1b678a53`.

Use Python 3.10 or later and the [Lean project at the replay revision](https://github.com/open-goat/pequalnp-proofs/tree/7da7d81614b93ea808c11ac27f27136942fec385/lean). The project pins [Mathlib revision fc4f59e](https://github.com/leanprover-community/mathlib4/tree/fc4f59e577feb1a4956671bc04ac18aaaf8cd842) and its transitive dependencies in [lake-manifest.json](https://github.com/open-goat/pequalnp-proofs/blob/7da7d81614b93ea808c11ac27f27136942fec385/lean/lake-manifest.json). Prepare that project’s pinned dependencies and their compiled libraries with `lake exe cache get` in its `lean` directory, or build Mathlib there with `lake build Mathlib`.

From this note’s directory, replace `UPSTREAM_LEAN_DIRECTORY` with that prepared `lean` directory and `LEAN_TOOLCHAIN_DIRECTORY` with the Lean 4.36.0 installation that contains `bin/lean` and `bin/leanchecker`.

~~~sh
python3 -I replay.py UPSTREAM_LEAN_DIRECTORY LEAN_TOOLCHAIN_DIRECTORY
python3 -I check_witness.py
~~~

The first command checks the source digest, dependency lock, dependency revisions, and Lean version. It builds in a fresh temporary directory, imports the resulting module, checks the reported axioms, and asks `leanchecker` to replay the module. The second command needs only Python’s standard library.
