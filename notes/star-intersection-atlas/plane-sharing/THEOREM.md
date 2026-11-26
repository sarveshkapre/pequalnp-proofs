# Sharing on the incidence graphs of finite projective planes

Take a row for each point and a column for each line. The target cells are the incident pairs. Start with individual row and column stars. Any union is free, and a binary intersection costs one. Write $C$ for the minimum cost when a wire can be reused and $F$ for the minimum when each occurrence in an expression tree is charged separately.

**Theorem.** Put $L=\lceil\log_2 q\rceil$ and $h=\log_2(2+L)$. Every finite projective plane of order $q\ge2$ satisfies $F=\Omega(L^2/h^2)$. For the field-coordinate plane $\mathrm{PG}(2,q)$, for every prime power $q$, we also have $C=O(Lh^3)$. Consequently
$$
  \frac{F(\mathrm{PG}(2,q))}{C(\mathrm{PG}(2,q))}
    =\Omega\!\left(\frac{L}{h^5}\right)\ \longrightarrow\ \infty .
$$

The same point–line incidence graph appears on both sides. A proof that rules out small formulas can miss circuits by an arbitrarily large factor even within this family. Combined with pjscruggs’s $\Omega(L)$ circuit bound, the upper bound also confines the circuit cost to $L^{1+o(1)}$. Thus a fixed-power improvement $\Omega(L^{1+\epsilon})$ for these field-coordinate planes is impossible for every fixed $\epsilon>0$. A superlinear improvement such as $L\log\log L$ remains consistent with the bounds. The estimates give no new exact gate count for order three. The model takes one point and one line as input. Circuits required to work on arbitrary subsets of points and lines have additional obligations. [pjscruggs’s bounds and model](https://github.com/pjscruggs/pequalnp-proofs/blob/7da7d81614b93ea808c11ac27f27136942fec385/notes/star-intersection-atlas/larger-planes.md) · [Cavalar and Oliveira, §4](https://arxiv.org/html/2503.14117v1#S4)

## From counted intersections to bipartite formula leaves

Complement every wire of a star formula. A free union of raw stars becomes a rectangle, free unions become intersections, and the $k$ paid gates become unions. Conversely every rectangle is the complement of a free union of stars. A bipartite formula counts leaves, each an arbitrary test of just the row or just the column. Its binary operations are AND and OR.

**Clipping lemma.** Intersect the output of any rectangle formula costing $k$ with any further rectangle. The result has a bipartite formula with at most $\max(2,4k)$ leaves. At cost zero the result is a rectangle, hence uses two leaves. At a paid union, distribute the clipping rectangle into both children and take their OR. If their costs are $i,j$, the sum of the two bounds is at most $4(i+j+1)$. At a free intersection, absorb a cost-zero child into the clip. When both children have positive cost, clip one and retain the other with the universal clip. The two sizes sum to at most $4(i+j)$. This proves the claim by structural induction. Complementing a bipartite formula exchanges AND and OR and negates each one-sided test, preserving the leaf count.

Even the factor four at budget one can be necessary. On the four subsets of $\{1,2\}$ on each side, use the union of the two rectangles “both subsets contain $i$”, for $i=1,2$. All four row neighborhoods are distinct, as are all four column neighborhoods. A formula using at most one row-test occurrence has at most two row neighborhoods. The same holds for columns. Thus four one-sided leaves are necessary.

## A formula lower bound independent of coordinates

Let $B$ be the zero-one incidence matrix. It has $N=q^2+q+1$ rows and columns, each of degree $\Delta=q+1$. Distinct points lie on exactly one common line, so $BB^\top=qI+J$. Its largest singular value is $q+1$ and its second is $\sqrt q$. Also $2\Delta\le N$. The sign matrix $S=2B-J$ therefore satisfies
$$
  \operatorname{signrank}(S)\ge\frac{\Delta}{\sigma_2(B)}
     =\frac{q+1}{\sqrt q}.
$$
Here sign rank means the least real rank of a matrix with the prescribed strict signs. The inequality is Theorem 4 of Alon, Moran and Yehudayoff. Their paper already gives finite projective geometry as an application. The spectral argument above also works for a plane presented solely by its incidence axioms. [Alon, Moran and Yehudayoff, *Sign rank versus VC dimension*](https://proceedings.mlr.press/v49/alon16.pdf)

Tal's Lemma 5.3 gives $\operatorname{signrank}(S)\le s^{O(\sqrt s)}$ for a bipartite formula with $s$ leaves. If binary-string domains are desired, take a surjection from the next power-of-two domain onto the points, and likewise for the lines. This repeats rows and columns, preserving sign rank in both directions. Unary tests pull back along these surjections. Sign rank is also invariant under changing every sign. Applying the clipping lemma with a universal clip yields $L=O(\sqrt{F+1}\log(2+F))$. If $F\ge L^2$ the claimed bound holds immediately. Otherwise the logarithm is $O(h)$, which gives $F=\Omega(L^2/h^2)$. All constants are absolute. [Tal, *Formula Lower Bounds via the Quantum Method*, §5](https://www.ias.edu/sites/default/files/math/csdm/16-17/TalSTOC2017.pdf)

## A circuit for every prime power

Fix $q=p^d$. Use a monic irreducible $g$ of degree $d$ over $\mathbb F_p$ to represent $\mathbb F_q$. Choose one homogeneous coordinate triple for each point and one dual triple for each line. A point lies on a line exactly when their three-term dot product is zero in the field. Every bit of each coordinate, and its opposite, is a union of raw stars on one side. These tests are free even if the public vertex numbering is arbitrary. The circuit may depend on the plane and its fixed modulus.

Work with canonical coefficients in $[0,p)$. Compute three polynomial products and add them coefficientwise modulo $p$ to obtain $H$ of degree at most $2d-2$. Reducing $H$ modulo $g$ takes two further products. For a polynomial of degree less than $s$, define $\operatorname{rev}_s(A)=X^{s-1}A(1/X)$, with zero padding. Hardwire $v=(\operatorname{rev}_{d+1}g)^{-1}\bmod X^d$, which exists because $g$ is monic. Writing $H=Qg+r$ with $\deg r<d$ gives
$$
 \operatorname{rev}_{2d}(H)\equiv
  \operatorname{rev}_d(Q)\operatorname{rev}_{d+1}(g)\pmod{X^d}.
$$
Indeed the reversed remainder contributes a multiple of $X^d$. Multiply the low $d$ coefficients of the left side by $v$, truncate and reverse to recover $Q$. Form $Qg$ and test $H-Qg=0$ coefficientwise. This works also for $d=1$.

For an explicit common bit bound set $b=\lceil\log_2(8(d+1)p^2)\rceil$ and use base $2^b$ digits. Each coefficient of a raw convolution in these five products has at most $d+1$ summands of size less than $p^2$. Multiplying the packed integers therefore gives the ordinary convolution with no carries between coefficients. Each integer input has $O(db)$ bits. Reduce each output digit $0\le c<2^b$ modulo $p$ using $u=\lfloor 2^b/p\rfloor$. The integer $\lfloor cu/2^b\rfloor$ is at most $\lfloor c/p\rfloor$ and at least $\lfloor c/p\rfloor-1$, because the two unrounded quotients differ by less than one. Subtract the estimated multiple of $p$, then conditionally subtract $p$ once. This requires two $O(b)$-bit multiplications and $O(b)$ other Boolean gates per digit. Fixed-width addition, comparison and subtraction use ordinary linear-size carry circuits. Reversals, truncations and extraction of bits are wiring.

Write $M(t)=O(t\log^2(2+t))$ for an available bounded-fan-in Boolean circuit size for multiplying two $t$-bit integers. Fürer proves the stronger $O(t\log t\,2^{O(\log^* t)})$ in the Boolean circuit model. Each convolution above costs $O(M(O(db))+dM(O(b))+db)$. Since $d\log_2 p=\log_2 q$, $db=O(Lh)$ and $\log(2+db)=O(h)$. The five convolutions and the remaining coefficient operations cost $O(Lh^3)$ gates in total. [Fürer, *Faster Integer Multiplication*](https://doi.org/10.1137/070711761)

Finally, retain both truth values of every Boolean wire as sets of cells. For AND, intersect the positive sets and freely union the negative sets. For OR, freely union the positive sets and intersect the negative sets. NOT exchanges the two wires. Thus each binary AND or OR adds at most one paid intersection, and reuse is permitted throughout. Any fixed finite binary Boolean basis converts to these gates with constant overhead. This proves the circuit bound.

## Attribution and verification

pjscruggs introduced the project's examples and proved the logarithmic circuit lower bound on these planes. Tal's inner-product theorem already implies unbounded sharing savings on unrestricted graphs in this model, using a linear circuit for parity of the coordinate products. The contribution here is the quantitative application to the project's plane family, the two model translations, and the explicit prime-power cost accounting. Historical priority for the combined observation is unestablished.

The two Lean files formalize the formula and circuit translations. The asymptotic theorem above uses the cited papers and the written coordinate argument. The independent arithmetic control compares the packed computation with schoolbook multiplication and polynomial long division. Its finite trials exercise the implementation. The proof of the universal bounds is the argument above. [Formula translation](../../../lean/PEqualNP/PlaneSharing/Transfer.lean) · [Circuit translation](../../../lean/PEqualNP/PlaneSharing/DualRail.lean) · [Replay](REPLAY.md)
