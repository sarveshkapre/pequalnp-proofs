# At least 90 terms for the rational 32-symbol two-block identity

**Theorem.** No 89-term rational riffle dictionary computes the two-block identity on 32 symbols. The exact rank is at least 90. The existence of a 90-term construction and the uniform rational linear-width question remain open.

The proof uses ordinary exact rank and allows arbitrary target-dependent, overlapping rank-one decoders. The new step is consistency between different quotients of one dictionary. There is an exact seven-target, 64-term example for which every single-column quotient works. An eight-target, 65-term example would need *every two-column quotient* to work, and their incidence counts are incompatible. [Upstream definition](https://github.com/open-goat/pequalnp-proofs/blob/f0ba75d581affddd034144e392d7ffaa2f87b3a2/lean/PEqualNP/Defs/RiffleRank.lean) · [Previous bound and construction](DYADIC.md)

## The quotient facts

First columns are vectors in a \(k\)-dimensional rational vector space. For each of \(k\) basis targets \(b\) there are matrices \(L,B\) such that \(L\operatorname{diag}(x(v_i))B=x(b)I_{32}\) for every functional \(x\). Replacing first columns and targets by their images under a quotient map preserves the surviving target equations, by pulling functionals back. Zero columns may be deleted. On contracting an arbitrary nonzero dictionary column one may discard any target having a nonzero coefficient in that column's basis expansion. The other \(k-1\) targets form a basis of the quotient. This also lets us retain any specified target not on the contracted line.

Write \(r_j=64-2^{6-j}\) for \(1\le j\le6\). The previous rectangular theorem gives a minimum of \(r_j\) columns for \(j\) targets with output size 32. The values are 32, 48, 56, 60, 62 and 63. If there are \(r\) columns in any \(j\)-target dictionary, at least \(64-r\) lie on each target line, counting zeros. Indeed, a functional vanishing exactly on the positions on that line gives a rank-\((r-t)\) diagonal matrix annihilated between two rank-32 matrices, so \(64+(r-t)\le2r\). This counts actual positions. At optimal width \(r_j\), for \(j\ge2\), quotienting by that target must leave at least \(r_{j-1}\) positions. The two inequalities force precisely \(2^{6-j}\) positions on the target line, and the quotient is again optimal. A zero position in an optimal dictionary is impossible.

## What 63 terms must look like

Take any width-63 dictionary with six independent targets and choose them as coordinates. For a proper subset \(T\) of the six coordinates, quotient away the targets in \(T\) successively. The positions lost are exactly those with support contained in \(T\), and their number is \(63-r_{6-|T|}=2^{|T|}-1\). This count is also correct for the full set. By induction on \(|T|\), **each nonempty support occurs once**. Write \(v_S\) for that unique column, and note that each singleton is a coordinate column up to scale.

Fix \(b\) and a nonempty \(S\) not containing \(b\). Contract the column \(v_S\), discarding a coordinate in \(S\) and retaining target \(e_b\). This five-target dictionary has 62 positions and hence is optimal. Its target line \(e_b\) must contain exactly two positions. One is the image of the singleton \(v_{\{b\}}\). The other original column belongs to \(\operatorname{span}(e_b,v_S)\). Its coefficient on \(v_S\) is nonzero, as the singleton is the only column on the \(e_b\) line; its coefficient on \(e_b\) is nonzero, as the support \(S\) occurred only once. Its support is therefore \(S\cup\{b\}\), and its entries on \(S\) are proportional to those of \(v_S\).

Descending from the full support now shows that every \(v_S\) is proportional to the restriction of the same full-support vector to \(S\). A single diagonal change of coordinates followed by individual column rescalings gives exactly the 63 nonzero zero-one vectors. Both operations preserve projective dependencies. This proves uniqueness of the first-column geometry even when the decoders overlap. It uses no integrality assumption on candidate columns.

## Two quotients give a contradiction

Suppose an 89-term dictionary exists. Contract 24 independent columns to obtain eight targets and 65 positions. The columns span the target space, since a functional vanishing on them all cannot detect a basis target. In this 65-position dictionary every pair of positions is independent. Otherwise extending a maximal independent subset of the pair to two independent columns and quotienting would leave a further zero among the remaining 63 positions, contradicting the six-target lower bound. The same argument excludes zero positions. Thus **every** pair can be contracted, and each pair quotient has the 63-point geometry just proved.

Call three distinct columns in the quotient a triangle if they are linearly dependent. For nonempty zero-one vectors over the rationals this happens precisely when one support is a disjoint union of the other two. To see this, express one column as a linear combination of the other two. If their supports are incomparable, the two exclusive regions force both nonzero coefficients to be one. Their common region must then be empty. If the first support is properly contained in the second, the exclusive region of the second forces its coefficient to be one. On their common region the first coefficient must be minus one, giving the set difference. Identical supports were excluded.

A point supported on \(t\) coordinates lies on

$$d(t)=(2^{t-1}-1)+(2^{6-t}-1)$$

triangles. The first summand counts unordered nontrivial partitions of its support. The second counts disjoint nonempty supports to add to it. Exactly seven points have degree 31 (the six singletons and the full set), 21 have degree 16, and 35 have degree 10.

For an unordered triple \(T\) of the 65 original positions, define \(d(T)\) to be the number of unordered disjoint pairs \(\{u,v\}\) for which the five columns in \(T\cup\{u,v\}\) have rank at most four. Contract any two members of \(T\). The rank drops by exactly two, so \(d(T)\) is exactly the triangle degree of the remaining member in that quotient. Crucially it is the *same integer* whichever two were contracted.

Mark \(T\) when \(d(T)=31\). Each of the \(\binom{65}{2}=2080\) pairs extends to exactly seven marked triples. Each marked triple contains three pairs. This gives \(3\,\#\{\text{marked triples}\}=14{,}560\), whose right side is one modulo three. This contradiction excludes 89. The previously kernel-checked lower bound excludes all smaller widths.

## A second count and a positive control

Instead contract only 20 columns, leaving 69 positions and 12 targets. Every six positions are independent: any dependent six-set can be extended from a basis of its span to six independent columns using positions outside that span, leaving at least one extra zero in the width-63 quotient. For every such six-set the quotient has exactly 301 triangles, either by summing the point degrees and dividing by three or counting disjoint unions directly. Thus each six-set belongs to exactly 301 nine-sets of rank at most eight. Counting incidences between six-sets and these nine-sets would give

$$\#\{\text{such nine-sets}\}=\frac{\binom{69}{6}\,301}{\binom{9}{6}}=\frac{1{,}288{,}682{,}824}{3}.$$

This contradiction uses total triangle counts and a different contraction depth. Both counts use the proved 63-column classification.

For the positive control use the 64 columns \((1,\pm1,\ldots,\pm1)\) with six independent sign coordinates. For each sign target use the 32 pairs differing in that sign. For the first target use 32 antipodal sign pairs. Their half-differences or half-sums give the desired target, one recovery on each diagonal coordinate. Quotienting by any vertex subtracts that vertex's sign coordinates from the others, giving all 63 nonempty subset supports up to diagonal scaling. The contrast locates the obstruction at the following extension to eight targets.

## The same obstruction at other sizes

Let \(k\ge4\), \(n=2^{k-1}\). The support and contraction argument above works verbatim for \(k\) targets at optimal width \(2^k-1\). The rectangular minima on \(j\le k\) targets are \(2^k-2^{k-j}\); the first arbitrary contraction leaves the optimal \(2^k-2\) positions and exactly two on each retained target line. Thus the optimal first columns are all nonempty subsets of the \(k\) coordinates up to the same rescalings. Their triangle degrees are \(2^{t-1}+2^{k-t}-2\). This is maximized exactly at \(t=1,k\), giving \(k+1\) distinguished points.

Equality in the previous square bound would leave \(2^k+1\) positions at dimension \(k+2\). The same pair count therefore requires \(3\mid\binom{2^k+1}{2}(k+1)\). When \(k\equiv0\) or \(4\pmod6\), the binomial coefficient is one modulo three and \(k+1\) is nonzero modulo three. It follows that \(R_{\mathbb Q}(n,2)\ge3n-k\) throughout these two infinite families. This gives 20 at eight symbols and 90 at 32. The improvement is one term on those sizes and does not change the asymptotic order of the lower bound.

## Verification and attribution

The [independent checker](check_89.py) tests all 39,711 triples by integer Gram determinant, checks the two incidence totals, constructs all seven decoders in the positive control and checks all 64 one-column quotients. [Exact output](check-89-replay.txt)

From the root of the fork checkout, the first command uses only the Python standard library. The second uses the pinned Lean 4.36.0 toolchain and the project's prebuilt Mathlib dependencies on macOS.

```sh
python3 -I notes/riffle-rank-lower-bound/check_89.py
python3 -I notes/riffle-rank-lower-bound/replay.py .
```

Lean 4.36.0 and leanchecker check the arbitrary-column decoder equation, the optimal target-quotient counts, recovery of support multiplicities from subset sums, propagation of projective scalings, and both impossible incidence families. These are component theorems of the written proof. The geometric passage from an arbitrary 89-term witness to one of those incidence families is proved above and has yet to be composed into an end-to-end Lean theorem. [Quotient lemmas](ThreeLinear.lean) · [Incidence and scaling lemmas](QuotientIncidence.lean) · [Kernel replay](ninety-lean-replay.txt)

Rossman posed the riffle-rank problem. The subset construction has classical binary PIR antecedents, and tomatotomata connected disjoint recovery to the project's upper bounds. The additional argument here forces the subset geometry for unrestricted rational decoders and compares contractions of one common dictionary. The subset configuration also occurs as the resonance arrangement. Historical priority for the riffle-rank conclusion remains undetermined. [Rossman](https://scholars.duke.edu/publication/1696504) · [Kurz and Yaakobi](https://arxiv.org/abs/2001.03433) · [Project discussion](https://github.com/open-goat/pequalnp-proofs/discussions/26249) · [Kühne on the resonance arrangement](https://link.springer.com/article/10.1007/s00493-023-00006-x)
