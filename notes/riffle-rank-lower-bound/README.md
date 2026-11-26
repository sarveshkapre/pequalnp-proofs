# An all-field lower bound for two-block riffle rank

The [logarithmic-deficit theorem](DYADIC.md) raises the 32-symbol lower bound to 89 and gives an exact rectangular family. At four symbols the [field comparison](FOUR-SYMBOLS.md) gives eight terms outside characteristic two and nine in characteristic two. Each note states its verification scope. The original square-root bound and proof follow.

Let \(R_F(n,2)\) be the minimum number of exact riffle-basic terms for the two-block identity over a field \(F\). For every \(1\le m\le n\),

$$
R_F(n,2)\ \ge\ n-m+\left\lceil\frac{2nm}{m+1}\right\rceil.
$$

In particular \(R_F(n,2)\ge 3n-O(\sqrt n)\). Every constant \(C<3\) eventually fails as an upper bound \(Cn\). At \(n=32\), setting \(m=7\) gives **81 terms**. The existence of a uniform linear upper bound with a larger constant remains open.

Rossman introduced riffle rank and posed the two-block identity question. The proof below uses the project's original factorization and Sylvester's matrix rank inequality. Tomatotomata's separate positive-characteristic upper-bound proposal and the characteristic-zero upper bound are in the same discussion. This result concerns exact lower bounds with arbitrary first factors and target-dependent, overlapping rank-one decoders. [Rossman's paper](https://www.sciencedirect.com/science/article/pii/S1877050925036488) · [Upstream definition](https://github.com/open-goat/pequalnp-proofs/blob/f0ba75d581affddd034144e392d7ffaa2f87b3a2/lean/PEqualNP/Defs/RiffleRank.lean) · [Upper-bound discussion](https://github.com/open-goat/pequalnp-proofs/discussions/26249)

## Proof

Write the first factors as columns \(v_i\in F^n\). At target \(b\), the decoder satisfies \(L_b\operatorname{diag}(x(v_i))D_b=x(e_b)I_n\) for every linear functional \(x\). The proof first works over an infinite field.

1. **Erase one term per discarded coordinate.** When the input dimension is \(k>m\), some term has a nonzero coefficient on the coordinate to be discarded. Otherwise decoding at that coordinate fails. Quotient by that term's first-factor vector. The other \(k-1\) coordinate vectors still form a basis, the term vanishes, and their target equations survive in the quotient. After \(n-m\) steps there are \(s=r-(n-m)\) available positions for \(m\) targets. The decoded identity matrix still has size \(n\). A zero column can be given any nonzero value by setting its decoder contribution to zero.

2. **Count the columns on one target line.** Let \(t_b\) be the number of positions proportional to the \(b\)-th surviving coordinate vector. Choose \(h\) that vanishes on that vector and is nonzero on all columns off its line. Over an infinite field this only requires avoiding finitely many proper hyperplanes. For \(m=1\) take \(h=0\). The diagonal matrix \(H=\operatorname{diag}(h(v_i))\) has rank \(s-t_b\), and \(L_b H D_b=0\). Both \(L_b\) and \(D_b\) have rank \(n\), since a functional taking value one at the target decodes to \(I_n\). Applying Sylvester's inequality to the two products yields \(n+(s-t_b)+n\le2s\). Thus \(s+t_b\ge2n\).

3. **Count all surviving target lines.** These \(m\) lines are distinct and their nonzero columns are disjoint. Summing \(s+t_b\ge2n\) gives \((m+1)s\ge2mn\), as claimed. In Lean, each column is assigned to one of its nonzero coordinates, which gives disjoint counts even when some columns have more than one nonzero coordinate.

4. **Pass to every field.** Any exact \(r\)-term decomposition over \(F\) remains an \(r\)-term decomposition over the infinite rational function field \(F(T)\) by applying the field embedding to each factor. The same inequality follows for finite fields.

Choosing \(m=\lceil\sqrt{2n}\rceil-1\) gives \(r+2\lceil\sqrt{2n}\rceil\ge3n+1\) for \(n\ge1\). Optimizing the displayed finite bound over integers \(m\) can give a stronger numerical value.

## Verification

The public theorem is **RiffleLower.pair_lower_all_fields**. Its hypothesis is the upstream **RiffleRankLe r (pairId (Fin n) F)**. **RiffleLower.pair_lower_near_three** and **RiffleLower.pair_lower_32** derive the square-root and 32-symbol bounds. Lean 4.36.0 and leanchecker on macOS replayed the original definition and both proof modules. The final theorems use propext, Classical.choice and Quot.sound.

With the pinned Lean toolchain and this repository's compiled Mathlib dependencies available, run from the fork checkout root:

    python3 -I notes/riffle-rank-lower-bound/replay.py .

The script checks the upstream definition's SHA-256, compiles the modules and runs leanchecker in a network-disabled temporary sandbox. [Matrix lemma](PencilRank.lean) · [Full Lean theorem](ThreeLinear.lean) · [Observed replay](three-linear-replay.txt)
