# The two-block identity has riffle-rank exponent one in characteristic zero

For every characteristic-zero field $F$ and every $\varepsilon>0$, the two-block identity has an exact riffle decomposition of width $O_\varepsilon(n^{1+\varepsilon})$. This includes the rationals. Fixing $a=b$ leaves an $n$-by-$n$ identity matrix in $c,d$, and each summand then has ordinary matrix rank at most one. Thus the growth exponent is exactly one. Whether an absolute constant $C$ suffices for width $Cn$ over $\mathbb Q$ remains open.

The model is Rossman's. A term has the form $A(a)C(b,c)D(b,d)$, and the sum must equal $[a=b][c=d]$ on all four inputs. The upstream project already gives the bound $3^{\lceil\log_2 n\rceil}$. tomatotomata proposed a near-linear bound in fixed positive characteristic using disjoint recovery sets from private information retrieval codes. The construction here uses polynomial interpolation in characteristic zero. [Rossman, Appendix C](https://users.cs.duke.edu/~br148/riffle-rank.pdf) · [Upstream bound](../../lean/PEqualNP/Gct/L097.lean) · [tomatotomata's proposal](https://github.com/open-goat/pequalnp-proofs/discussions/26249)

## Lean statement

The locally verified theorem uses the project's definitions of the identity and its riffle rank. [PairBound.lean](PairBound.lean) · [Upstream definitions](../../lean/PEqualNP/Defs/RiffleRank.lean)

~~~lean
theorem pair_exponent_one (F : Type) [Field F] [CharZero F] (d : ℕ) (hd : 0 < d) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n → ∃ r : ℕ, RiffleRankLe r (pairId (Fin n) F) ∧
      r^d ≤ K * n^(d+1)
~~~

This is the integer-power form of the upper bound. Given $\varepsilon>0$, choose $d$ with $1/d\le\varepsilon$. The formal proof encodes symbols in $t$ base-$s$ digits and gives width at most $(t(s-1)+1)(2s-1)^t$ whenever $s\ge2$ and $n\le s^t$. The first interpolation produces factors with the three allowed input dependencies. A second interpolation extracts the constant term after the digits are combined. The use of interpolation with tensor powers follows a classical idea of Bini. [Interpolation identity](PackedRiffle.lean) · [Bini on exact and approximate bilinear algorithms](https://link.springer.com/article/10.1007/BF02575865)

## A short sphere proof

There is a direct way to see the exponent over $\mathbb Q$. It uses Behrend's equal-norm lattice construction. The key choice is that each requested symbol $b$ gets its own layer for encoding the second input. [Behrend](https://pmc.ncbi.nlm.nih.gov/articles/instance/1078964/pdf/pnas01693-0039.pdf)

1. Fix $h\ge3$ and an integer $s\ge2$. In the box $\{0,\ldots,s-1\}^h$ there are at most $h(s-1)^2+1$ squared norms. If $n\le s^h/(h(s-1)^2+1)$, choose $n$ distinct vectors on one sphere and use them as the alphabet $S$. For each $b\in S$, the dot product $b\cdot t$ takes at most the same number of values on the box. Choose $n$ distinct vectors $t_b(c)$ on one such layer, indexed by $c\in S$.
2. Multiply the polynomials $\sum_{a\in S}x_a X^a$ and $\sum_{c\in S}y_c X^{t_b(c)}$. The coefficient of $X^{b+t_b(d)}$ is $x_b y_d$. Indeed, a collision $a+t_b(c)=b+t_b(d)$ gives $b\cdot a=b\cdot b$. Since $a$ and $b$ also have equal squared norm, $\|a-b\|^2=0$. Hence $a=b$, and distinctness on the layer forces $c=d$.
3. The polynomial product has degree at most $2s-2$ in each variable. Interpolate it on a rational product grid with $2s-1$ nodes per coordinate. For a grid node $u$, let $L_u$ be its multivariate Lagrange basis polynomial. The three factors are $u^a$, $u^{t_b(c)}$, and the coefficient of $X^{b+t_b(d)}$ in $L_u$. Their sum over the grid is exactly $[a=b][c=d]$, using $(2s-1)^h$ terms. Rational coefficients embed into any characteristic-zero field.
4. Take $s=\lceil((h+1)n)^{1/(h-2)}\rceil$. The counting condition holds, and the width is $O_h(n^{h/(h-2)})$. For any $\varepsilon>0$ choose $h$ large enough that $2/(h-2)\le\varepsilon$. This proves the claimed exponent.

The interpolation proof in PairBound.lean formalizes the full characteristic-zero upper bound. For the sphere proof, Lean verifies the collision argument in step 2. The counting and interpolation steps above are written arguments. The rational checker independently expands all 1,393 tensor entries in three examples. [Sphere lemma](Sphere.lean) · [Exact-arithmetic check](check_sphere.py)

## Replay

Starting at the root of this fork checkout, use a Mac with the pinned Lean 4.36.0 toolchain installed through elan and the repository's compiled Mathlib dependencies present under lean/.lake. The replay builds the upstream definition and the three supplied modules in a temporary offline sandbox, prints the theorem axioms, and runs leanchecker on the resulting modules. The rational check requires only Python 3.

~~~sh
python3 -I notes/riffle-rank-characteristic-zero/replay.py .
python3 -I notes/riffle-rank-characteristic-zero/check_sphere.py
~~~

The observed Mac replay lists only propext, Classical.choice and Quot.sound for the exponent theorem. This package is a research hand-back for a proposed theorem ID. [Replay output](verification.txt)
