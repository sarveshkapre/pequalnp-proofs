# The exact price of a shared rectangle bank for optional equality tests

Suppose $g$ disjoint paths can each be requested or skipped. When requested, path $i$ tests whether the two labels at that coordinate are equal. For example, on a mandatory chain of $s$ gates, put a different raw bit-mismatch test at each gate. Requesting rejection at the downstream end checks equality of the two $s$-bit labels. Skipping the chain imposes no test. Its alphabet has $N=2^s$ symbols.

Let coordinate $i$ have alphabet $X_i$ of size $N_i\ge2$. The row and column spaces are both $\prod_i X_i$. A request $S$ asks for equality at every coordinate in $S$. One bank contains rectangles in the full row-by-column grid. Each request is answered by selecting some of those rectangles and taking their free union. The same rectangle may be selected by any number of requests.

For any family $\mathcal F$ of allowed requests the minimum number of distinct rectangles in such a bank is exactly

$$
\sum_{S\in\mathcal F}\prod_{i\in S}N_i.
$$

**Construction.** For every requested subset $S$ and assignment $z$ to its coordinates, include the rectangle whose rows and columns both extend $z$. The union over all $z$ gives precisely the equality test on $S$.

**Lower bound.** For each pair $(S,z)$ choose a cell $(x,y)$ with $x_i=y_i=z_i$ on $S$, and $x_i\ne y_i$ everywhere outside $S$. This is possible because every alphabet has two distinct symbols. Consider any rectangle selected by request $S$ that covers this cell. All its rows and columns must agree on the fixed value $z_i$ at each $i\in S$, since any row in the rectangle can be crossed with any of its columns. At every coordinate outside $S$, the witness cell itself exhibits unequal values. Consequently the rectangle determines both $S$ and $z$ from the coordinates on which its entire row and column projections agree on one value. It cannot serve as a witness rectangle for a different pair. Counting the witnesses gives the lower bound.

For the full request family with uniform alphabet size $N$, the minimum is $(N+1)^g$. The Lean theorem proves this exact minimum for every $g\ge0$ and $N\ge2$, including arbitrary choices of rectangle bank and request-specific reuse. The unequal-alphabet and restricted-family statements follow from the written argument. [Lean proof](../../../../lean/PEqualNP/PaidDepth/OptionalEqualityBank.lean)

If requests are constrained by a dependency order, the same formula quantifies the saving. For uniform $N$, divide the exact minimum by $N^g$. This gives $\sum_{S\in\mathcal F}N^{-|S^c|}$. If every omitted set is a final segment on each of $w$ chains, then this ratio is at most $(1-1/N)^{-w}$. For a disjoint union of chains where every choice of final segments is allowed, the exact ratio is the product of their finite geometric sums. Thus comparability can remove the growing overhead without changing the alphabet size.

Checking every coordinate together uses $N^g$ rectangles. Supporting all requests multiplies that by $(1+1/N)^g$. Reuse of identical rectangles therefore leaves a growing overhead at fixed $N$. This identifies an obstruction to a particular improvement of the [subdivision bound](THEOREM.md). A general two-layer circuit can combine predicates in other ways. The minimum subdivision length for such a circuit remains open. [Replay instructions](REPLAY.md)
