# Dense slope differences can have cheap incidence circuits

On an infinite family of **non-Desarguesian Hall planes**, every pair of distinct finite slopes can differ in **every Frobenius coefficient**, even though their incidence graphs have nearly logarithmic circuit cost. Counting those coefficients in a given representation cannot certify a large circuit. The cost gap between formulas and circuits also extends to **every finite André plane**, with no restriction on the rule that chooses twists.

Rows are points, columns are lines, and cells encode incidence. Arbitrary unions of individual row and column stars are free. Each binary intersection costs one. Circuits can reuse a computed set, whereas formulas pay separately at each occurrence. Write $C$ and $F$ for the two minimum costs. Put $Q=p^d$ for the plane order, $p$ prime, $L=\lceil\log_2 Q\rceil$, $h=\log_2(2+L)$, and $j=\log_2(2+h)$. Constants below are independent of the plane and its representation. The input is one point and one line.

## How many gates does a twisted line need?

Use affine points $(x,y)$ in $K^2$, $K=\mathbb F_Q$. Suppose the lines in each direction are the level sets of a surjective $\mathbb F_p$-linear map $A:K^2\to K$. Directions have distinct kernels forming a spread. Suppose each $A$ can be written as a sum of at most $s$ terms
$$
       a_i z_i^{p^{e_i}},\qquad z_i\in\{x,y\},\quad 0\le e_i<d ,
$$
plus a map of $\mathbb F_p$-rank at most $r$. The coefficients, exponents, choice of input coordinate, low-rank maps and level values may vary arbitrarily by line. **Then**
$$
       C=O((1+s+r)Lh^5j^3).
$$
The test can use an implicit equation involving both $x$ and $y$, without constructing an inverse for a slope map.

**Proof.** Use the representation of Couveignes and Lercier (Theorem 4). It embeds a field element in $O(d\log^2(2+d)\log^2\log(4+d))$ base-field coordinates. A Frobenius step is a fixed permutation of coordinates. Addition is coordinatewise, and multiplication uses $O(d\log^3(2+d)\log^3\log(4+d))$ base-field arithmetic operations. The representation and all field constants are fixed for the given plane. The multiplication formulas and their convolution circuits have a fixed schedule. For $d=1$ use the prime field directly. [Couveignes and Lercier, *Elliptic periods for finite fields*, Theorem 4 and §5.2](https://arxiv.org/abs/0802.0165)

Each bit of $x,y$ in this representation is a one-sided input and so is its complement. The same holds for the bits encoding every line parameter. Choose $x$ or $y$ by a multiplexer. For each bit position $b$ of the exponent, conditionally apply the fixed permutation raised to $2^b$. An output bit uses three AND-inverter gates per stage, including access to both polarities. Composing the stages applies the required Frobenius power with $O(\log(2+d))$ stages regardless of the line's exponent. The [Lean routing theorem](../../../lean/PEqualNP/PlaneSharing/VariableShift.lean) proves the exact $3wb$ count for a $w$-bit vector and $b$ independent selectors, retaining every output and its complement. Multiply the routed word by the coefficient and add the terms.

A rank-$r$ correction has the form $\sum_{i=1}^r u_i\lambda_i(x,y)$ by choosing a basis of its image. The $u_i$ and the coefficients of the $2d$-input prime-field linear functionals are one-sided line data. Use free point-coordinate bits in any fixed ordinary basis to evaluate each functional in $O(d)$ prime-field operations. Multiply each resulting scalar into the coordinates of $u_i$ and add. Testing equality with the line's level is a comparison of the represented words. For lines and points at infinity, the only further tests are the point and line types and equality of two direction labels of $O(L)$ bits.

One prime-field addition costs $O(b)$ Boolean gates for $b=\lceil\log_2 p\rceil$. A prime-field product costs $O(b\log^2(2+b))$, using integer multiplication and fixed-modulus reciprocal reduction as in the [field-plane proof](../plane-sharing/THEOREM.md). Since $db=O(L)$, the stated bound covers all products, selectors, comparisons and additions. The previously checked [dual-rail translation](../../../lean/PEqualNP/PlaneSharing/DualRail.lean) charges at most one paid intersection per binary Boolean gate. This proves the bound. [Fürer, *Faster Integer Multiplication*](https://doi.org/10.1137/070711761)

For an arbitrary translation plane presented by a spread in $\mathbb F_p^{2d}$, there is also a direct bound $C=O(dLh^2)$. Each kernel has codimension $d$. Choose a $d$-by-$2d$ matrix with that kernel and store its coefficients as free tests on the line. Evaluating the resulting $d$ scalar equations costs $O(d^2)$ prime-field operations. In particular, **all translation planes of bounded extension degree over the prime field** have $C=L^{1+o(1)}$ along growing orders. The point–line rank lower bound of pjscruggs supplies the matching exponent one in these statements. [pjscruggs’s larger-plane bounds](https://github.com/pjscruggs/pequalnp-proofs/blob/7da7d81614b93ea808c11ac27f27136942fec385/notes/star-intersection-atlas/larger-planes.md)

## Every finite André plane

An André spread uses slopes $T_m(x)=m x^{p^{e(m)}}$, with a field automorphism chosen according to a norm class, plus the vertical direction. Intercepts translate the graphs. In the equation $y-T_m(x)=b$ there are at most two terms, so $s=2,r=0$ for all these planes. The preceding upper bound holds even when the public description of the norm-class table is very large, since the actual choice is a property of the line alone. This also applies to the dual planes by transposing the grid. The geometry and its construction are classical. [Dover, *Computational Enumeration of André Planes*, §§2–4](https://arxiv.org/abs/2105.07439)

If only $b$ distinct twists occur, an elementary alternative costs $O(bL+Lh^3)$. Supply all $b$ conjugates of $x$ directly as free row predicates in the ordinary polynomial representation. For each of their $O(L)$ bit positions intersect each candidate with its one-sided line selector and freely union the results. Do the same for complemented bits. A single ordinary field multiplication, addition and comparison now suffice, with the costs from the field-plane construction. In particular, the infinite Hall counterexample below has **$C=O(Lh^3)$ with only two choices**, independent of the elliptic-period construction.

The already established bound $F=\Omega(L^2/h^2)$ applies to all finite projective planes via the incidence spectrum and bipartite sign rank. Thus for every growing sequence of André planes,
$$
         F/C=\Omega\bigl(L/(h^7j^3)\bigr)\ \longrightarrow\ \infty .
$$
More generally any spread presentation above with $s+r=O(L^{1-\epsilon})$ for fixed $\epsilon>0$ gives a growing gap. These are deterministic exact computations. The available ordinary circuit lower bound is logarithmic. [Formula lower bound and model transfer](../plane-sharing/THEOREM.md) · [Alon, Moran and Yehudayoff](https://proceedings.mlr.press/v49/alon16.pdf) · [Tal, §5](https://www.ias.edu/sites/default/files/math/csdm/16-17/TalSTOC2017.pdf)

## Why even pairwise coefficient density can be misleading

Every $\mathbb F_p$-linear endomorphism of $K$ has a unique representation $\sum_{i=0}^{d-1} c_i x^{p^i}$. For uniqueness, a nonzero difference has ordinary degree at most $p^{d-1}<Q$ and cannot vanish at all $Q$ elements. The $Q^d$ coefficient lists exhaust the $Q^d$ linear endomorphisms. Support below means the number of nonzero coefficients in this unique polynomial in the displayed coordinates.

Replacing $(x,y)$ by $(x,S(y))$ for an invertible $\mathbb F_p$-linear $S$ sends the affine line $y=A_m(x)+b$ to $y'=S(A_m(x))+S(b)$. Extend by sending each direction point to the corresponding direction point. This gives row and column bijections, preserving **both** gate minima exactly. Composing linearized maps with invertible maps is also a standard equivalence in rank-metric coding theory. [Sheekey, *A new family of linear maximum rank distance codes*, §2](https://arxiv.org/abs/1504.01581)

First there is a simple bound for any André spread and $d\ge2$. Write $T(z)=\operatorname{Tr}_{K/\mathbb F_p}(z)$. Choose $u\ne0$ with $T(u)=0$ and put $S(z)=z+uT(z)$. Its inverse is $z\mapsto z-uT(z)$. For any two distinct slopes, $A=A_m-A_n$ is surjective and has support at most two. The functional $T\circ A$ is nonzero, so equals $x\mapsto T(vx)$ for some $v\ne0$ by the trace pairing. Indeed $T$ is nonzero by the polynomial root bound; for any $v\ne0$, multiplication by $v$ is a bijection, so $v\mapsto T(v\,\cdot)$ is injective and gives the full dual by dimension. Consequently $uT(A(x))$ has coefficient $u v^{p^i}\ne0$ in **all** $d$ positions. Adding $A(x)$ can cancel at most two. The same $S$ gives support at least $d-2$ for **every** pair of distinct finite slopes. The [Lean trace theorem](../../../lean/PEqualNP/PlaneSharing/DenseDifferences.lean) proves the shear is bijective and the off-support coefficients are nonzero for the corresponding two-automorphism difference.

### A single presentation with full support for every pair

Let $p$ be odd, $E=\mathbb F_{p^a}\subset K$, and let $[K:E]=d/a$ be even. Assume $d\not\equiv2\bmod p$. Choose any André rule whose exponent $e(m)$ is a multiple of $a$ and depends only on the relative norm $N(m)=N_{K/E}(m)$. At $m=0$ choose any branch. Set
$$
        u=-1/2\in\mathbb F_p,\qquad S(z)=z+uT(z).
$$
This time $S$ is invertible because $1+T(u)=1-d/2\ne0$. Explicitly the inverse subtracts $uT(z)/(1+T(u))$. Its linearized coefficients are $s_0=1+u=-u$ and $s_j=u$ for $j\ne0$. Both signs have the same relative norm because $[K:E]$ is even.

Fix an output coefficient index $t$. After expanding $S(T_m(x))$, the coefficient of $x^{p^t}$ is
$$
       b_t(m)= s_j\,m^{p^j},\qquad j=(t-e(m))\bmod d .
$$
It satisfies $N(b_t(m))=N(u)\,N(m)^{p^t}$ because the exponent $e(m)$ fixes $E$. Therefore equality of two outputs forces equality of the input norms, then equality of their selected exponents. Within that single branch multiplication by $s_j\ne0$ and Frobenius are bijections. Thus **each $b_t$ is a permutation of $K$**. It follows simultaneously for all $m\ne n$ that **all $d$ coefficients of $S T_m-S T_n$ are nonzero**. The [Lean coefficient theorem](../../../lean/PEqualNP/PlaneSharing/NormCoefficient.lean) formalizes this recovery of the branch: after removing the common scalar and outer Frobenius, the sign and remaining automorphism preserve the norm key on each branch.

For an infinite concrete family take $p=3$, $d=2k$, $k\ge2$, $k\not\equiv1\bmod3$, and $E=\mathbb F_{3^k}$. Switch the relative-norm-one class by the quadratic conjugation and leave every other class alone. This is the classical single-regulus Hall plane, non-Desarguesian for these orders. Every pair of its finite slopes now has the maximum possible support $2k$. The original sparse presentation still gives the same nearly logarithmic circuit cost. In particular a lower-bound argument using coefficient density must handle its dependence on the displayed coordinates, even if it compares every pair of directions. [Dover, §3, Hall planes of index one](https://arxiv.org/pdf/2105.07439)

## Scope and replay

The new conclusions are the circuit upper bound in this paid-intersection model, the resulting extension to André planes, and the simultaneous coefficient-density obstruction. The finite planes, field arithmetic, and sign-rank inequalities used to derive them are prior work. The checked project sources and scoped literature searches did not establish historical priority.

Four official Lean statements cover the variable-cost routing construction, the trace shear, the norm-fibre coefficient permutation, and the explicit spread and failure of Desargues at order nine. The assembled asymptotic and full-support family theorems above are written proofs. Finite controls independently evaluate an order-nine circuit and recover the transformed coefficients by interpolation. [Commands, exact scope and checks](REPLAY.md)
