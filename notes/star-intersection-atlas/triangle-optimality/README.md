# A triangle minimizes the total error of two intersections on any finite projective plane

Let a finite projective plane have order $q\ge 2$, $n=q^2+q+1$ points and as many lines, and $d=q+1$ lines through each point. The input is one point and one line. An ordinary acyclic circuit starts with a star for each row and column, takes arbitrary unions for free, and pays one per binary intersection. Earlier gates may be reused. Give a false positive and a false negative the same cost.

**Theorem.** Among all such circuits with at most two paid intersections, the minimum number of wrong cells is $nd-6q$. A triangle attains the minimum with zero false positives.

| Order | True incidences | Correctly accepted by a triangle | Minimum total errors |
| ---: | ---: | ---: | ---: |
| 2 | 21 | 12 | 9 |
| 3 | 52 | 18 | 34 |
| 4 | 105 | 24 | 81 |

The model and the two-intersection classification come from [pjscruggs’s atlas](https://github.com/pjscruggs/pequalnp-proofs/blob/7da7d81614b93ea808c11ac27f27136942fec385/notes/star-intersection-atlas/TwoIntersections.lean). Our [earlier comment in pjscruggs’s discussion](https://github.com/open-goat/pequalnp-proofs/discussions/19729#discussioncomment-19914391) used the triangle in a seven-intersection construction. The contribution here is the matching lower bound on **total cell errors**, allowing arbitrary mistakes of either sign on the entire plane.

## The triangle construction

Choose three noncollinear points $p_1,p_2,p_3$ and let $L_i$ be the side opposite $p_i$. For each $i$, take the free union of all rows for points on $L_i$ and all columns for lines through $p_i$. Intersect these three unions with two gates.

At a triangle vertex the remaining condition is that the input line pass through that vertex. At any other point on a side, the remaining two conditions require the input line to be that side. Off all three sides they require a line through all three vertices. Thus the accepted cells are exactly the incidences touching a vertex or side of the triangle. The six incidence stars have size $d$ each, with six vertex–side incidences counted twice. This gives $6d-6=6q$ correct positives.

## Reducing the lower bound to two cases

Give every incident cell weight $+1$ and every nonincident cell weight $-1$. If the accepted cells have weight $W$, the circuit makes $nd-W$ errors. It suffices to prove $W\le 6d-6$.

There are two forms. The paid gates can feed a common union in parallel, or the prediction can be an intersection of three raw unions. To see why this includes reuse, write the first gate as $u=A\cap B$. If $u$ occurs in both arms of the second gate, distributivity gives $u\cup(C\cap D)$. If $u$ is also selected at the output, absorption gives the same parallel form when only one arm uses it. With one use and no direct output from $u$, the second gate is $(C\cup u)\cap D=(C\cup A)\cap(C\cup B)\cap D$. A free output union can be absorbed into all three clauses. These forms include the smaller gate budgets.

For $q\ge3$ we have $n\ge3d$. Rows or columns accepted everywhere by the raw choices can be set aside. If there are $a$ such rows and $b$ such columns, their union has area $n(a+b)-ab$ and at most $d(a+b)$ true cells. When $a$ or $b$ is at least $2d$, the area is at least $2nd$ and the entire plane has only $nd$ incidences. Otherwise $ab\le d(a+b)$. In both cases the union has nonpositive weight. For an upper bound, restrict to the remaining rows and columns. The direct Fano enumeration below includes full rows and columns without this estimate.

**Rectangle estimate.** In a board of incidences without a four-cycle and of maximum degree $d\ge3$, any rectangle has weight at most $d$. If both sides have size at least two, it has weight at most three. Fix its $a\ge2$ rows. A positive column meets more than half of them, and two columns have at most one true neighbor in common. If two or more columns are positive, $a$ is odd, each positive column contains $(a+1)/2$ true neighbors, and their complements are pairwise disjoint. There are at most three positive columns, of weight one each. If a lone positive column has weight $s\ge4$, any second column contributes at most $2-s$ since it contains at most one of the first column’s true neighbors. For a rectangle with a single row or column the degree bound suffices.

## Three raw clauses

Label each point and line by the subset of clauses its own raw star activates. A cell is accepted if the two labels together contain all three bits. Full labels have been set aside. Empty labels have no accepted cells among the remaining vertices. This leaves six types per shore, three with one bit and three with two bits. Each row type times its accepted columns is a rectangle, and these six rectangles are disjoint. The same holds on the column side.

Suppose $d\ge7$ and $W>6d-6$. Repeatedly remove vertices whose individual signed contribution is nonpositive. This can only increase $W$ and preserves the label representation on the restricted board. If any type is absent on either shore, the remaining five rectangles weigh at most $5d\le6d-6$. So all six types occur on both shores, and every surviving vertex contributes positive weight.

Consider a two-bit row class of multiplicity at least two. It accepts three nonempty column classes, so its weight $x$ is at most three. The combined deficit of the other five row classes relative to $5d$ is at most $5-d+x\le1$, since weights are integers. In particular each of the three one-bit row classes weighs at least $d-1$.

A one-bit row class accepts only the complementary two-bit column class. That column class must be a singleton. Indeed its full predicted neighborhood contains three row types. If it held two or more columns, its full rectangle would have weight at most three. Every column is individually positive, so there would be at most three columns. Restricted to the one-bit row class, its weight would then be at most three, either by its size for a single row or by the rectangle estimate for several rows. This contradicts $d-1>3$.

The three one-bit row classes therefore meet three distinct single columns, representing three lines. Their row classes are disjoint, so each point contributes at most one positive cell to the three rectangles together. Three distinct lines contain at most $3d-2$ points, even when concurrent. This forces a deficit of at least two, contradicting the preceding upper bound of one. All two-bit row classes are singletons. By duality the two-bit column classes are also singletons.

These six vertices cover every accepted cell. Their six predicted stars overlap exactly in the six accepted crossings between two-bit rows and two-bit columns with different missing bits. If $b$ of the crossings are false, their weight is $6-2b$. Each center has at most $d$ true cells and counts its false crossings negatively, so the six center weights sum to at most $6d-2b$. Subtract the double-counted weight to obtain $W\le6d-6$.

For $d=5,6$, the finite type check below gives respective upper bounds 24 and 30, exactly $6d-6$. The labelled planes cover $d=3,4$.

## Parallel gates

Outside full rows and columns, each raw intersection is a union of two rectangles, one from each crossing of a row arm with the opposite column arm. The two row sets are disjoint, as are the two column sets. The parallel output is therefore a union of four rectangles with at most eight active membership types per shore (choose neither arm or one arm per gate, excluding the empty choice).

For a union of rectangles, trim vertices of nonpositive weight. If a vertex has a single predicted neighbor, removing that neighbor costs at most $d$ and eliminates at least one whole rectangle. After the first such step we may allow the remaining rectangles to be arbitrary. Otherwise every active vertex has at least two predicted neighbors. In this case each type has multiplicity at most three. Four positive vertices with identical neighborhoods would give a rectangle of weight at least four with at least two rows and columns. There are at most 24 vertices per shore for the four structured rectangles, and at most 21 for three arbitrary rectangles.

The finite check bounds the weight of these latter boards with no degree-one vertices. For two arbitrary rectangles the bound is 7, for three arbitrary rectangles it is 14, and for four rectangles from two parallel gates it is 24. A cap of 24 on the number of true neighbors in the checked board is valid for every plane order by the preceding support bound. Starting with one rectangle of weight at most $d$, the degree-one removal then gives
$$W\le\max(4d,\,2d+7,\,d+14,\,24).$$
This is at most $6d-6$ for $d\ge5$. The two smaller degrees are covered below.

## What the finite calculations certify

The [type checker](leafless_rectangles.cpp) enumerates multiplicities on both shores for each admissible label. In the parallel calculation the predicted degree is at least two after trimming. For three clauses, retain degree-one vertices as well. Such a type has at most $d$ members because every one must be a true neighbor of the same vertex. Otherwise a type has multiplicity at most three. For three clauses, two labels are compatible if their bitwise union is 7. For rectangles, row and column masks are compatible if they select a common rectangle.

For a predicted neighborhood of size $h$, every surviving vertex needs at least $\lfloor h/2\rfloor+1$ true cells. Two vertices with the same neighborhood can share at most one true neighbor. For $h\ge2$ this forces $h$ odd and both true degrees equal to $(h+1)/2$. With three such vertices, the disjoint complements force $h=3$. A single vertex may have up to $\min(d,h)$ true neighbors. A lower bound of $t$ true neighbors already consumes $\binom t2$ pairs. Adding one more consumes $t$ additional pairs. Each eligible pair may be used at most once, since two points determine a unique line, and dually. Charging the cheapest remaining increments first on each shore gives an upper bound for that profile. Maximizing over profiles hence bounds every realization, including non-coordinate planes. A [separate order-four checker](four_nested_audit.cpp) excludes gain 25 and retains 84 profiles at gain 24 as a control.

For orders two and three the labelled incidence checks optimize over all choices of the circuit arms. In these orders the coordinate plane suffices: delete a line at infinity and choose two affine directions as rows and columns of a $q$-by-$q$ grid. The remaining $q(q-1)$ lines are distinct permutation graphs. For $q=2,3$ these exhaust the $q!$ permutations. Their directions are determined by disjointness, which also reconstructs the points at infinity.

The [order-two checker](fano_two_distance.cpp) directly tests both forms on all 49 cells. At order three the [nested checker](three_clause_distance.cpp) fixes three excluded point sets and lets each line choose its best union of them. The [parallel checker](two_parallel_distance.cpp) fixes full rows and the two banks of disjoint row sets, and optimizes each line over both banks. Projective symmetries reduce the searches to 20,269,474 triples and 217,845,001 bank pairs, respectively. They give minima of 34 and 36. The lower value is attained by the displayed triangle. The input generator constructs the field plane and its 5,616 projective transformations.

## Verification and open questions

The geometric deductions above are written mathematics. All ten [finite checks](finite-checks.txt), including the order-four control, were replayed on the Mac. The [replay instructions](REPLAY.md) give the commands.

In related work on total errors, Lean’s standalone kernel verified [the adjacent-row inequality and its chain and partition consequences](ChainHamming.lean). For example, if one predicted row is contained in the next, the true entries lost between them are bounded by misses in the first plus false positives in the second. The [kernel record](chain-hamming-kernel.log) lists only `propext`, `Classical.choice`, and `Quot.sound`. The triangle theorem and the finite optimizations still await an end-to-end Lean proof. The exact circuit cost for recognizing all incidences of the 13-point plane with unrestricted wire reuse also remains open at six or seven. No historical priority claim is made.
