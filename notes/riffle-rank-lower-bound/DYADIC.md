# A logarithmic deficit in the two-block riffle lower bound

Let \(R_F(n,2)\) denote the exact two-block riffle rank of the identity on \(n\) symbols over a field \(F\). For \(n\ge1\),

$$R_F(n,2)\ \ge\ 3n-\lfloor\log_2 n\rfloor-2.$$

The bound is 89 at 32 symbols and 184 at 64. The earlier count gave 81 at 32. A uniform upper bound \(Cn\) over the rationals remains open.

## What the decoder must preserve

Write \(D_F(k,n)\) for the minimum width with \(k\) independent coordinate targets and an \(n\)-dimensional identity to recover at each target. A width-\(r\) dictionary consists of shared first columns \(v_i\in F^k\). Each target \(b\) has its own \(n\times r\) matrix \(L\) and \(r\times n\) matrix \(B\). For every functional \(x\),

$$L\,\operatorname{diag}(x(v_i))B=x(e_b)I_n.$$

This permits arbitrary coefficients and overlapping rank-one terms. At \(k=n\) this is exactly the project's two-block factorization. Applying a field embedding to all factors preserves these equations, so we can work over the infinite field \(F(T)\) when proving lower bounds.

Fix a target. Let \(q\) count columns outside its line, with multiplicities. Choose a functional vanishing on that line and nonzero on all \(q\) columns by avoiding finitely many proper hyperplanes. Its diagonal matrix \(H\) has rank \(q\) and \(LHB=0\). Both outer matrices have rank \(n\), since another functional gives \(I_n\). The product rank inequality gives \(2n+q\le2r\). Quotient the first-factor space by the target line. The \(q\) surviving columns still decode the other \(k-1\) independent targets, with the same output size. Thus

$$2D_F(k,n)\ \ge\ 2n+D_F(k-1,n)$$

over an infinite field. Starting at \(D_F(1,n)=n\) and rounding to integer widths gives \(D_F(k,n)\ge 2n-\lfloor n/2^{k-1}\rfloor\) for every field.

A second kind of quotient erases one chosen column whose coefficient on the discarded target is nonzero. Such a column exists because that target decodes an identity. The remaining targets are independent modulo the column. Repeating this step \(n-k\) times gives

$$R_F(n,2)\ \ge\ n-k+2n-\lfloor n/2^{k-1}\rfloor.$$

Take \(k=1+\lfloor\log_2 n\rfloor\). No assumption about symmetry or sparsity enters the bound.

## Where the rectangular estimate is exact

If \(n=t\,2^{k-1}\), then \(D_F(k,n)=t(2^k-1)\) over every field. Take \(t\) copies of all nonempty subset indicators in \(F^k\). For target \(b\), pair each subset omitting \(b\) with the subset obtained by adding \(b\). The signed difference is \(e_b\). For the empty subset the singleton alone suffices. Put each pair or singleton on its own diagonal entry, using disjoint positions within each target. This attains the lower bound. For six targets and output dimension 32, the exact width is 63. The full 32-target problem retains the additional cost of the discarded dimensions.

The subset construction and optimality for classical binary disjoint-recovery PIR codes are established coding theory. Kurz and Yaakobi describe the simplex construction and its optimality. Tomatotomata connected disjoint recovery to the project's upper-bound question. The result here extends optimality to arbitrary overlapping riffle decoders over all fields and yields the logarithmic-deficit bound in Rossman's square model. Historical priority for these extensions is undetermined. [Kurz and Yaakobi](https://arxiv.org/abs/2001.03433) · [Tomatotomata's proposal](https://github.com/open-goat/pequalnp-proofs/discussions/26249) · [Rossman's paper](https://scholars.duke.edu/publication/1696504)

## Verification

Lean 4.36.0 and leanchecker replayed **rectangular_dyadic**, **pair_log_lower**, **pair_dyadic_32** and **simplex_optimal** in namespace **RiffleLower**. The square theorem takes the upstream **RiffleRankLe** hypothesis directly. Each theorem uses propext, Classical.choice and Quot.sound. The same package contains the [four-symbol field comparison](FOUR-SYMBOLS.md). [Lower-bound proof](ThreeLinear.lean) · [Exact rectangular construction](SimplexOptimal.lean) · [Replay output](dyadic-replay.txt)
