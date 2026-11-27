# Seven is the sharp positive-root multiplicity bound through exponent span 64

Computational research note, November 27, 2026.

Let P be a nonzero sum of three cubes of real polynomials with at most two monomials each. Real scalar weights are allowed since they can be absorbed into the inputs by taking real cube roots. Subtract the smallest input exponent from every input exponent. Divide the differences by their gcd when it is positive. A single distinct exponent has normalized span zero. **If the resulting exponents span at most 64, every positive root of P has multiplicity at most seven.** maxkieff's polynomial below attains seven within this range. The maximum for unrestricted integer exponents is still between seven and nine.

The new census completes all configurations in spans 33–64 in which at least two inputs share an exponent but no exponent belongs to all three. NathanNT previously reported an exact exclusion for every support through span 32 and described the two-cube interpolation used in the second verifier. The full census below also checks the cases with six distinct endpoints or an endpoint shared by all three. Aargau supplied the unrestricted upper bound of nine. [NathanNT's bounded computation](https://github.com/NathanNT/pequalnp-proofs/blob/7899eeecc840bc735de49f344f83a2da5fad36dd/notes/note-sparse-root-bounds/paper/sparse-root-bounds.tex#L519) · [Aargau's proof](https://github.com/open-goat/pequalnp-proofs/pull/23576)

## Which cases were checked

The counts below fix the smallest exponent at zero. They retain dilations and reflections. Each row counts unordered multisets of three unordered exponent pairs. Within each pair the two listed endpoints are distinct. The coefficients at those endpoints may vanish. A monomial can be padded with any second exponent already present. If all the exponents coincide, P is zero or a monomial and the assertion is immediate.

| How the three pairs overlap | Distinct input exponents | Cases at spans 33–64 |
| --- | ---: | ---: |
| Two pairs meet and the third is disjoint | 5 | 17,982,480 |
| The three pairs form a path | 4 | 440,448 |
| Two identical pairs and a disjoint third pair | 4 | 220,224 |
| The pairs form a triangle | 3 | 1,520 |
| **Total** | | **18,644,672** |

View the exponent pairs as edges of a multigraph. In the pairwise-overlap cases without a common endpoint every vertex is used, the maximum degree is two, and some vertex has degree two. Those conditions give exactly the four rows above. For k vertices and span s, choose k−2 interior exponents from 1,…,s−1. The numbers of patterns per vertex set are respectively 30, 12, 6 and 1. The two verifiers generate their cases differently and agree with these formulas at each span.

For the full bound, the other possibilities are three disjoint edges or an endpoint common to all three. The second verifier also checked those families. In all, it handled 134,359,744 translated support multisets over spans 1–64. For n available exponents, the number of multisets before fixing the extremes is F(n)=C(C(n,2)+2,3). Consequently the expected count at each span s is F(s+1)−2F(s)+F(s−1). Every count matched.

## Reduction that preserves positive-root multiplicity

For smallest exponent m and common difference divisor g, the original sum is x^(3m) times the normalized sum evaluated at x^g. Near any positive root r, x^g has nonzero derivative. Thus even supports with arbitrarily large numerical exponents are covered when their normalized span is at most 64.

Rescale a positive root to 1, absorbing powers of r into the coefficients. For the pair (a,b), the four positions of its cube have exponents tⱼ=(3−j)a+jb and coefficients hⱼ=C(3,j)A^(3−j)B^j. Write S for the set of distinct expanded exponents and Hₜ for the **sum** of all coefficients at t. Substituting x=exp(y) shows that a root at 1 has order at least eight exactly when

    ∑ₜ Hₜ tᵏ = 0   for k=0,…,7.

If |S|≤8, Vandermonde forces every Hₜ to be zero. In every case P≠0 requires at least one nonzero aggregate coefficient.

## First verification by aggregate coefficients

Put D(T)=∏ₜ(T−t) and N=|S|. When N≥9, the complete kernel of the eight moment equations is

    Hₜ = q(t)/D′(t),       deg q ≤ N−9.

Lagrange interpolation gives ∑ tʲ/D′(t)=0 for j≤N−2 by extracting the top coefficient. This proves the inclusion. Evaluation is injective on the N−8 dimensional space of polynomials q in the display. The eight independent moment equations leave exactly N−8 dimensions. An input overlap ensures N≤11, leaving at most three unknown coefficients for q.

For positions used by just one cube, Hₜ is also the coefficient of that cube. Any cube satisfies h₁²=3h₀h₂, h₂²=3h₁h₃, h₁h₂=9h₀h₃ and the corresponding cubic identities on triples of positions. The first pass substitutes q into those identities. With one free coefficient one can set q=1 by homogeneity. A pair of known adjacent nonzero coefficients of a cube determines its remaining coefficients by a geometric progression after division by C(3,j). A shared term with one unknown contribution determines that contribution by subtraction. With two or three free coefficients, the checker multiplies the identities by monomials and tests whether they span all homogeneous forms of a fixed degree. Full rank forces every pure power of a coordinate to vanish. These tests use the prime 1009. All denominators used in interpolation or reconstruction are units modulo that prime, and a nonzero determinant modulo the prime is nonzero over the rationals.

There were 5,656 inconclusive first-pass patterns in spans 33–64. The second stage retained the shared-coefficient equations. To see how they work, write cⱼ=hⱼ/C(3,j) for a cube. For two private slots a<b, the unknown hₖ obeys d hₖ^(b−a)=n, where

    d = cₐ^max(0,k−b) cᵦ^max(0,a−k),
    n = C(3,k)^(b−a) cₐ^max(0,b−k) cᵦ^max(0,k−a).

These polynomial identities hold even if a coefficient vanishes. At a shared node, the unknown contributions xᵢ also satisfy ∑xᵢ=Hₜ. Eliminate them by taking the determinant of multiplication by (∏dᵢ)(Hₜ−∑xᵢ) in the monomial basis with powers of each xᵢ less than its order mᵢ=bᵢ−aᵢ. On wrapping xᵢ^mᵢ, replace its factor dᵢ xᵢ^mᵢ by nᵢ. Evaluating the basis at a common solution gives a nonzero left null vector (its constant entry is 1), so the determinant must vanish. If dᵢ=0 at a solution, nᵢ=0 there as well, and the cleared matrix still gives a necessary identity.

At the prime 65537 these identities and the private equations excluded the remaining 3,396 one-coordinate, 2,240 two-coordinate and 20 three-coordinate cases. The binary checks use polynomial gcd and explicitly check the point at infinity. The ternary checks use full rank of homogeneous forms. Every decision is an exact implication in characteristic zero. [First pass](aggregate.cpp) · [Per-span counts](aggregate.tsv) · [Shared-term elimination](aggregate_finish.py) · [Completion log](aggregate_finish.log)

### A triangle at span 33

Take (0,1), (0,33) and (1,33). Their nine expanded exponents are 0,1,2,3,33,35,66,67,99. If the eight moments vanished for a nonzero sum, rescaling gives Hₜ=1/D′(t). The two contributions to exponent zero are determined by the private pairs at (1,2) and (33,66). Their sum would have to equal H₀. In exact arithmetic,

    H₀ − H₁²/(3H₂) − H₃₃²/(3H₆₆) = −12247/1456887790088640.

Thus this configuration cannot give an eightfold root. The check works on the sum of the two contributions at zero, which is where treating the repeated exponent as separate would give the wrong equations.

## Independent verification by eliminating two cubes

The second program constructs the list of exponent pairs, enumerates ordered indices i≤j≤k, and keeps triples whose smallest endpoint is zero. It uses no code or intermediate case list from the aggregate verifier. It follows NathanNT's two-cube interpolation approach with a polynomial identity for the split at a shared node.

Designate one cube and let E be the distinct expanded exponents of the other two. The checker tries the three designations as necessary. When E has eight or seven elements, the first |E| moment equations uniquely determine the combined coefficient at each s∈E. For the cardinal polynomial ℓₛ of E it is

    Fₛ(A,B) = −∑ⱼ C(3,j) A^(3−j)B^j ℓₛ(tⱼ).

At seven nodes there is one more necessary equation, obtained with the polynomial ∏ₛ(T−s) of degree seven. At eight nodes the two cubes have disjoint expanded positions, so each quadruple F must obey the cube identities. At seven nodes they share one position. The three private positions of each cube give a necessary quadratic or cubic identity and an identity h_missing·d=n from the private values. The combined coefficient at the shared position must obey Fₛd₁d₂=n₁d₂+n₂d₁. This uses no division by a potentially vanishing cube coefficient.

The cases A=0 or B=0 are checked separately. Then there are at most nine nodes. If there are nine, the other eight coefficients are uniquely determined by the single monomial and can be tested directly. A=B=0 leaves at most eight nodes.

For AB≠0 the necessary homogeneous binary forms may be divided by exact factors A or B. The program tracks conservative degree bounds through every operation, so a coefficient that merely becomes zero modulo a prime cannot justify discarding a factor. It requires both a unit gcd on the finite chart and a nonvanishing form at its point at infinity modulo 10007. A common projective root in characteristic zero would give the rational binary forms a common homogeneous factor of positive degree. By the primitive polynomial lemma over the rationals localized at the prime, its nonzero reduction would still divide every reduced form and have a projective zero over the algebraic closure. The modular checks exclude that possibility. This argument covers arbitrary real coefficients, including irrational ones.

This verifier had zero unresolved cases over all spans 1–64. Its second pass covers the disjoint and common-endpoint families, completing the full bound. [Two-cube verifier](two_cubes.cpp) · [Pairwise-overlap results](two_cubes.tsv) · [Other families](complement.tsv)

## Sharpness, controls and replay

maxkieff's integer polynomial 2250(x³−x²)³−125(x⁴−x)³+9(x⁵−1)³ has order exactly seven at 1. The first seven Taylor coefficients vanish and the coefficient of (x−1)⁷ is 2925. This establishes sharpness for the whole span-at-most-64 statement. [Original example](https://github.com/open-goat/pequalnp-proofs/discussions/21999)

As a positive control for order eight, in characteristic 11 the polynomial (1+x)³+4(1+9x¹⁰)³+4(x+9x²)³ has Taylor coefficients 0 through degree seven and coefficient 2 at degree eight. Its three pairs have overlaps and no common endpoint. Both compiled verifiers and the shared-coefficient elimination retain this example when run over that field. Its distinct expanded nodes remain distinct after reduction. The control confirms that the tests can preserve a true solution. It makes no claim about these coefficients over the reals.

With Python 3.10 or later and a C++17 compiler, run the following from this directory. The runner builds in a temporary directory, checks both positive controls, exhausts the support triples, compares the complete output to the saved counts and reconciles each span independently. It uses only the standard libraries.

    python3 -I replay.py

The result is a locally reproduced computational proof. The checks are separate implementations within this research effort. The finite computation has not been formalized in Lean or independently reviewed upstream. [Replay receipt and source hashes](verification.txt)
