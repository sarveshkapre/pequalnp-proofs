# The size–depth tradeoff for intersections on sparse graphs

A cell is one row and one column of a finite bipartite graph. A union of arbitrary row stars, column stars and earlier wires is free. Each binary intersection costs one. Its paid depth is one plus the greatest paid depth on its inputs. Raw inputs have depth zero. The last free union adds no depth. Write $C_D(G)$ for the minimum cost at paid depth at most $D$, and $\nu(G)$ for the maximum matching size.

**Sparse graph theorem.** Fix an integer $a\ge1$. For every graph covered by $a$ forests, and every $D\ge1$, put
$$
 n=\max(2,\nu(G)),\qquad u=\min(2^{D-1},\lceil\log_2 n\rceil).
$$
Uniformly in the graph, its dimensions and the depth,
$$
                 1+C_D(G)=\Theta_a\big(u\,n^{1/u}\big).
$$
The same estimate holds for the minimum cost of a *formula* at the same depth. The lower bound allows arbitrary wire sharing. The upper bound constructs a formula. The additive one handles graphs obtainable from raw stars alone. With a large matching in a forest, the successive fixed-depth costs have orders $n,\sqrt n,n^{1/4},n^{1/8},\ldots$. Once the permitted depth reaches $1+\lceil\log_2\lceil\log_2 n\rceil\rceil$, the cost is of order $\log n$.

**Plane theorem.** Every finite projective plane of order $q$ requires $\Omega_D((q^2+q+1)^{1/2^{D-1}})$ intersections at fixed paid depth $D\ge1$. Every family of circuits of size polynomial in $\log q$ requires $\Omega(\log\log q)$ paid depth. For **every finite translation plane**, circuits of size polynomial in $\log q$ attain $O(\log\log q)$ depth. This identifies the asymptotic depth at that size scale. A superlogarithmic unrestricted size lower bound and a matching size upper bound for projective planes at every fixed depth remain separate questions.

**Complement theorem.** Among graphs produced in one layer with at most $k$ intersections, the greatest cost of the complementary graph at target depth $D$ is of order $v\,2^{k/v}$, where $v=\min(k,2^{D-1})$ and $k\ge1$. Equality of $k$-bit labels attains that order. The result also holds when the target is required to be a formula.

## The rectangle certificates of a circuit

A rectangle is a product of a set of rows with a set of columns. A *fooling set* consists of accepted cells such that, for each distinct pair, at least one of the two crossed cells is rejected. A rectangle contained in the graph meets such a set at most once.

For a circuit with $k$ intersections prepare a common dictionary of $K=8k+2$ rectangles. For each of the two operands of each gate, collect all its raw row stars into one row strip and all its raw column stars into one column strip. Reserve those four strips. Also reserve the four rectangles formed by intersecting one raw strip from each operand. Reserve the two raw strips of the output. Empty or duplicate slots are allowed. Individual dictionary rectangles may contain cells outside the output.

**Certificate lemma.** At paid depth at most $D\ge1$, every accepted cell belongs to an intersection of at most $m=2^{D-1}$ dictionary rectangles contained in the output. At depth one both operands must hold on a raw strip. Their intersection is already a *single* dictionary rectangle. At a deeper gate, an operand holds either on one raw strip or on a previous gate. Take one witness for each arm and unite the sets of indices. The intersection they specify establishes both arms simultaneously. At the final free union take the witness for one true alternative. Index sets ignore order and repeated wires. The entire circuit uses one dictionary, including when paths share intermediate gates.

The positive rectangle cover number and the size $M$ of any fooling set are consequently at most
$$
                     \sum_{j=0}^{\min(K,m)} {K\choose j}.
$$
The witness rectangles may overlap. Their union covers every positive cell. Equality of index sets at two fooling-set cells would force both crossed cells to be positive. The [Lean theorem](../../../lean/PEqualNP/PaidDepth/FoolingBound.lean) proves this injection for a gate-indexed circuit with arbitrary raw masks, dependencies and final free union. Its first paid gate has level zero, so the standalone statement uses exponent $d=D-1$.

## The lower bound in sparse graphs

If a rectangle contains $s$ edges of a matching, the graph contains $K_{s,s}$. A forest restricted to those $2s$ vertices has at most $2s-1$ edges. For $s>0$, $s^2\le a(2s-1)$ forces $s<2a$. Thus the positive rectangle cover number is at least $\nu/(2a-1)$. For forests each rectangle meets the matching at most once.

There is also a direct way to apply the machine-checked fooling-set statement. Contract the matching edges within the subgraph on their endpoints, discarding loops and parallel edges. Every induced subgraph on $t>0$ contracted vertices has fewer than $2at$ edges by the same forest bound. Every such subgraph has a vertex of degree at most $4a-1$. Greedy coloring in reverse deletion order uses at most $4a$ colors. The largest color class gives an induced submatching of size at least $\nu/(4a)$.

The binomial sum is always at most $2^K$, giving $K=\Omega_a(\log n)$ for large $n$. For $1\le m\le K$, it is at most $(eK/m)^m$. Multiply each term by $(m/K)^j$, use $j\le m$, and bound $(1+m/K)^K\le e^m$. When $m<\lceil\log_2 n\rceil$ this implies $K=\Omega_a(m n^{1/m})$. If $m>K$ in this range, $K=\Omega_a(\log n)$ implies $n^{1/m}=O_a(1)$, so the same conclusion holds. For $m\ge\lceil\log_2 n\rceil$, the logarithmic lower bound suffices. Small matching sizes are covered by the additive one.

## An upper construction at the same depth

Root each tree in each covering forest. Separate the edges with a row parent from those with a column parent. Each of the resulting at most $2a$ layers is a vertex-disjoint union of stars. A layer has at most $\nu$ nonempty components: choose one edge in each. The [earlier forest hand-back](https://github.com/sarveshkapre/pequalnp-proofs/tree/988b680d249ffb31e141fa4269f5f73907fcf1a4/notes/star-intersection-atlas/sparse-sharing) already uses this decomposition for an unrestricted formula bound.

Assign a distinct base-$b$ identifier of $u$ digits to each component of a layer, with $b=\lceil n^{1/u}\rceil$. A vertex outside the layer has no identifier. For each digit and each possible value, intersect the row strip and column strip carrying that value, then freely union over values. This checks digit equality and rejects inactive vertices. Intersect the digit tests in a balanced tree. A pair passes exactly when its vertices belong to the same component, and every such cross-part pair is an edge. Each layer costs at most $ub+u-1$ with paid depth at most $1+\lceil\log_2 u\rceil\le D$. Freely union the layers. The [second Lean theorem](../../../lean/PEqualNP/PaidDepth/DigitFormula.lean) constructs a formula from the raw-star, union and intersection rules. For $w=2^h$ digits and alphabet $b$, its cost is $w(b+1)-1$ at depth $h+1$. Padding with always-true digits to the next power of two uses at most $2u$ digits and suffices for the same asymptotic bound.

## The worst cost of complementing one parallel layer

Let $H(k,D)$ be the largest $C_D(\overline G)$ among finite grids with $C_1(G)\le k$. For $k\ge1$ and $D\ge1$, put $v=\min(k,2^{D-1})$. With absolute constants,
$$
                H(k,D)=\Theta\big(v\,2^{k/v}\big).
$$
The same order holds if the complement must be produced by a formula. The size bound is independent of the grid dimensions.

For the upper bound, a one-layer source is a free union of output stars and at most $k$ terms $U_i\cap V_i$, whose arms are raw star unions. Group the gates into $v$ blocks of at most $g=\lceil k/v\rceil$ gates. A cell avoids every gate of one block if we can choose one false arm at each gate. For a fixed choice of arms, every chosen row test and column test must be false. Their conjunction is just **one rectangle**. The output-star exclusions can be absorbed into every such rectangle. Thus the complement is an intersection of $v$ free unions of at most $2^g$ rectangles. Each rectangle costs one intersection, and a balanced tree combines the blocks. The resulting formula costs at most $v2^g+v-1$ at depth at most $D$. The [Lean construction](../../../lean/PEqualNP/PaidDepth/ParallelComplement.lean) derives this directly from the original parallel circuit for $2^h$ blocks of $g$ gates. Empty gates pad the last block. If $v$ is not a power of two, then $v=k<2^{D-1}$ and we can use the next power of two with one gate per block.

For a matching lower bound use $2^k$ row labels and the same column labels. Inequality of labels has a parallel $k$-gate circuit: for each bit, intersect the union of the two zero strips with the union of the two one strips. This gate accepts exactly a mismatch at that bit. Freely union the $k$ results. Cavalar and Oliveira already prove the exact logarithmic cost for inequality. Its complement is a matching of size $2^k$, so the sparse lower bound at depth $D$ gives the claimed cost. [Cavalar and Oliveira, Proposition 40](https://arxiv.org/html/2503.14117v1#S4.SS2)

The independent contribution here is the matching upper bound for **every** parallel source together with the lower bound for every target depth, using the established inequality example. For instance, retaining one layer can cost exponentially many gates, while allowing order $\log k$ layers always suffices at linear size for this source class. The block proof uses the absence of dependencies between the source gates.

**A concrete scale.** On all $2^{20}=1{,}048{,}576$ labels, inequality takes exactly 20 intersections in one layer. Equality at the same depth takes **exactly 524,288**. Indeed, a useful one-layer gate inside the diagonal cannot include a full row or column. Expanding its two raw arms leaves at most two cross rectangles, each covering at most one diagonal cell. Conversely, one gate $(R_i\cup C_j)\cap(R_j\cup C_i)$ covers the two diagonal entries for any two different labels $i,j$. At depth two, compare the two ten-bit halves separately. On each half, pairing its 1,024 values costs 512 gates, and intersecting the two comparisons costs one more, for **at most 1,025**. At depth six, each of the twenty individual bit equalities takes one gate, and their balanced conjunction takes nineteen, for **at most 39**. The latter two counts describe constructions. The first count is an exact optimum for equality at depth one.

## Projective planes

A plane has $N=q^2+q+1$ points and as many lines. Its incidence graph is regular of degree $q+1$. Counting incident flags at any subset of points gives at least as many neighboring lines as selected points, so Hall's theorem supplies a perfect matching. Two different points have exactly one common line. Therefore no positive rectangle can contain two of the matching edges, and the certificate lemma applies with $M=N$ in any coordinates. At fixed $D$ the size is $\Omega_D(N^{1/2^{D-1}})$. At depth one the [existing project hand-back](https://github.com/open-goat/pequalnp-proofs/discussions/19729#discussioncomment-19914391) has the sharper exact count $\lceil(q+1)^2/2\rceil$.

Put $L=\lceil\log_2 q\rceil$. From $M\le(K+1)^m$ (encode a sorted subset in $m$ positions with a padding symbol), $k=L^{O(1)}$ forces
$$
        D\ge \log_2 L-\log_2\log_2(2+L)-O(1).
$$
A sharper statement holds for $k=O(L(\log(2+L))^b)$ at fixed $b\ge0$. The binomial estimate gives $m=\Omega_b(L/\log(2+\log(2+L)))$: $x\log(eK/x)$ increases for $x\le K$, and at $x=\epsilon L/\log(2+\log(2+L))$ it is at most $O_b(\epsilon L)$ for all sufficiently large $L$ at fixed $\epsilon>0$. Thus
$$
        D\ge\log_2 L-\log_2\log_2(2+\log_2(2+L))-O_b(1).
$$
For $k=O(L)$ use $x=\epsilon L$ and $\epsilon\log(1/\epsilon)\to0$ to obtain $D\ge\log_2 L-O(1)$. Constants may depend on the asserted size bound. If $m>K$, the unrestricted $K=\Omega(L)$ already implies these conclusions.

For the upper construction, take a translation plane represented by a spread over the prime field, $q=p^e$. Affine points are vectors of $2e$ prime-field coordinates. Each affine line is a coset of an $e$-dimensional subspace, so its descriptor supplies the $e$ rows of a defining matrix and their target values. Every descriptor bit and its opposite are free one-sided inputs. This is a nonuniform circuit for the given plane.

Let $b=\lceil\log_2 p\rceil$. For each equation expand each product as binary partial products of a point bit and a coefficient bit. Give the bit product the fixed weight $2^{i+j}\bmod p$. Add the one-sided bits of the negative target with weights $2^i\bmod p$. This nonnegative integer sum is a multiple of $p$ exactly when the equation holds. There are $T=2eb^2+b$ words, each smaller than $p$. Width $W=\lceil\log_2(Tp+1)\rceil$ suffices. Reduce triples to pairs using constant-depth full adders at each bit and shift the carry one position. The word count after each round is $2\lfloor T/3\rfloor+(T\bmod3)$, so $O(\log(T+1))$ rounds leave two words. Compute their sum with a parallel-prefix adder of depth $O(\log(W+1))$: compose the carry functions of adjacent intervals by successive doubling. Compare against each of the at most $T+1$ multiples of $p$ in range, then take the OR. Bit comparisons and the final conjunction of $e$ equations use balanced trees. Since $T,W,e$ are polynomial in $L$, the size is polynomial in $L$ and depth is $O(\log L)$. The extra cases at infinity require type checks and equality of two direction identifiers, at depth $O(\log L)$. Keeping both polarities of each binary Boolean wire charges at most one intersection per AND or OR and preserves the depth upper bound. The geometry and the [matrix presentation](../semilinear-planes/THEOREM.md) are prior ingredients.

## Attribution and scope

pjscruggs supplied the project's star model, plane experiments and logarithmic unrestricted lower bounds. Earlier sparse work and Brânzei, Maji, Mehta and Mukherjee give the forest and biclique-layer background. Pudlák, Rödl and Savický, and Jukna studied graph complexity and bounded-depth circuits under several charging and fan-in conventions. Here arbitrary unions are free, intersections are binary, and depth counts serial intersections only. The finite certificate bound, uniform sparse size–depth law, extremal complementation tradeoff and translation-plane depth consequence are the results established here. Historical priority for their formulations is unestablished. [Atlas](https://github.com/open-goat/pequalnp-proofs/discussions/19729) · [P4-free Partition and Cover Numbers](https://www.cs.purdue.edu/homes/hmaji/papers/BMMM20.pdf) · [Pudlák, Rödl and Savický](https://users.math.cas.cz/~pudlak/graph-complexity.pdf) · [Jukna](https://eccc.weizmann.ac.il/report/2004/005/revision/1/download/) · [Replay](REPLAY.md)
