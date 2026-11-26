# The price of answering every equality request

Take two words of length $g$ over $N$ symbols. For each subset $S$ of the coordinates there is an output $E_S$. It accepts when the words agree at every position in $S$. In the star model a circuit has free unions of row stars, column stars and earlier wires, including on the final output. Each binary intersection costs one gate. All outputs may use the same wires. Paid depth counts successive intersections.

For $g\ge1$, $N\ge2$, and fixed paid depth $D\ge1$, put $m=2^{D-1}$. The minimum cost of supplying all these outputs on one circuit is

$$
\Theta_D\big((N+1)^{g/m}+2^g\big).
$$

The constants depend only on depth. At depth two over four symbols, the answer is $\Theta(5^{g/2})$. There are $2^g$ requests. Even the hardest individual request costs only $\Theta(2^g)$. A single circuit given a request as part of the input can also answer it in $\Theta(2^g)$ gates. The joint requirement therefore adds a factor of order $(\sqrt5/2)^g$ beyond both benchmarks.

The complemented outputs have a small common source. For $N=2^t$, each of the $tg$ bit comparisons costs one gate. A mismatch is the intersection of “at least one bit is zero” with “at least one bit is one.” A free output union selects the bit comparisons at its requested coordinates. Thus a source of $tg$ parallel gates supplies every mismatch output. This uses the bitwise inequality construction in the model of Cavalar and Oliveira and builds on pjscruggs’s star atlas. [Cavalar and Oliveira](https://eccc.weizmann.ac.il/report/2025/033/) · [pjscruggs’s atlas](https://github.com/open-goat/pequalnp-proofs/discussions/19729)

## Lower bounds with unrestricted sharing

A rectangle is a set of rows times a set of columns. Write $s$ for the total paid gates. All free unions of gate outputs in a depth-$D$ circuit can be represented by choosing from the **same** bank of at most $(8s+1)^m$ rectangles. Within a single arm the raw row signal and raw column signal are two strips. At level one, include the four strips from each gate and the four pairwise intersections between strips from opposite arms. Include one full rectangle. At every later level replace the bank by all ordered pairwise intersections. Taking a member twice preserves it. Each arm is a union of old bank members, so its intersection with the opposite arm is covered by new members. All gates use this bank simultaneously. An output takes the union of precisely those members it needs. [Lean theorem](../../../../lean/PEqualNP/PaidDepth/CommonOutputBank.lean)

Every nonempty $S$ has no full row or column in $E_S$. Thus any final raw contribution to it is empty. One additional full rectangle suffices for the empty request. The exact rectangle bank for these requests has size $(N+1)^g$. Consequently $(N+1)^g\le(8s+1)^m+1$. [Earlier exact bank proof](../relay-subdivisions/OPTIONAL_BANK.md)

There is also a lower bound $s\ge 2^g-1$ at **every** depth. For each nonempty $S$, take two words agreeing exactly on $S$ and choose a tapped gate covering this witness. A gate tapped by both $S$ and $T$ is contained in both outputs. If it covers both chosen witnesses, then $S\subseteq T$ and $T\subseteq S$. Thus each nonempty request has a distinct witness gate. The two inequalities, including arbitrary direct row and column outputs, are combined in one theorem. [Lean theorem](../../../../lean/PEqualNP/PaidDepth/SimultaneousEqualityLower.lean)

## Matching construction

Write $g=um+r$ with $0\le r<m$. Give each of $m$ blocks its own $u$ complete coordinates. Encode each remaining coordinate in $m$ digits of base $B=\lceil N^{1/m}\rceil$, using any injection. Give digit $j$ of each of these $r$ coordinates to block $j$. Every word now has an encoding in each block.

Each block purchases one rectangle for each pattern of specified or wildcard values at its positions. Its two shores consist of words agreeing with every specified value. At most $(N+1)^u(B+1)^r$ rectangles suffice. Since $B+1\le3(N+1)^{1/m}$, this costs at most $3^{m-1}(N+1)^{g/m}$ gates per block, including when $m>g$. For a request $S$, each block takes the free union of rectangles with exactly the required positions specified. In the digit positions all blocks use the same original coordinate mask. A balanced tree of $m-1$ further intersections gives $E_S$ at depth $D$. There are $2^g$ such trees.

## Exact depth-one answer

Allow coordinate alphabets $N_i\ge2$ and any family $\mathcal F$ of requests. The exact joint cost at depth one is

$$
\sum_{\varnothing\ne S\in\mathcal F}
  \left\lceil\frac{\prod_{i\in S}N_i}{2}\right\rceil .
$$

For each assignment $z$ on $S$, pick a witness equal to $z$ there and unequal elsewhere. A depth-one gate contained in $E_S$ has no full strip. Expanding its two arms leaves at most two cross rectangles. Each nonempty rectangle in $E_S$ fixes a common label at every selected coordinate, so each gate covers witnesses for at most two assignments. A gate counting toward two different requests would cover a distinguished witness for each, which the inclusion argument above excludes. This proves the sum of the rounded lower bounds.

For the upper bound, pair the label assignments within each request. The cylinder for $z$ has row shore $R_z$ and column shore $C_z$. For two different assignments their respective shores are disjoint. The gate $(R_z\cup C_{z'})\cap(R_{z'}\cup C_z)$, with shore sets understood as strips, computes exactly the union of the two cylinders. A leftover assignment uses one rectangle gate. The empty request is the free full grid.

## Supplying the request as input

Give each shore a word over ordinary symbols plus a wildcard. A single output requires agreement everywhere both symbols are ordinary. This includes one-sided requests and, by restriction, a jointly specified mask. Its depth-$D$ cost is $\Theta_D(N^{g/m})$.

Use the same $m$ blocks and digit encoding. A wildcard matches every value of its coordinate or digit. In a block, purchase a rectangle for each possible ordinary completion of its positions. The row and column are compatible in the block exactly when they have a common completion. At most $N^uB^r\le 2^{m-1}N^{g/m}$ completion rectangles suffice per block. Some tuples of digits may be unused codes. This cannot introduce a false positive because the only obstruction is two distinct ordinary labels, which differ in at least one digit. A balanced conjunction finishes the construction. On fully specified inputs the diagonal has $N^g$ cells, each requiring its own rectangle. The common-bank bound gives the reverse order. Restricting to any selected subset gives the corresponding single-request upper bound, and selecting all coordinates gives the hard diagonal.

This identifies a limitation of optional-path constructions for the open single-output fixed-length question. Having every mask available as a choice of taps can force exponential overhead. Moving those choices into ordinary inputs can eliminate the entire factor. Independent copies obey a more general constraint. [Single-output tensor powers](TENSOR.md) · [Earlier fixed-length question](../relay-subdivisions/THEOREM.md) · [Replay](REPLAY.md)
