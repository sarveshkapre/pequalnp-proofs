# Private readers in a circuit with feedback

Draw two copies of the paid gates. Connect a gate in the first copy to each gate in the second copy that reads it on at least one operand. Self-reads become edges between the two copies of the same gate. An induced matching of size $w$ consists of $w$ senders and $w$ readers whose incidence submatrix is a permutation matrix. The matching here is in the **source dependency relation**.

Let $k$ be the gate count, fix target paid depth $D\ge1$ and put $m=2^{D-1}$. If the maximum such matching has size $w$, every single-output complement has a formula of cost at most

$$
3m\;2^{k/m}\sum_{j=0}^{w}\binom kj .
$$

In particular $w=o(k)$ gives the sharp worst exponential rate $1/m$, including for least-fixed-point feedback and arbitrary placement of each read. More precisely, an excess of $\epsilon k$ in log cost requires a rejected cell with linearly many true gates having distinct private readers. The lower example for worst-case masks and outputs is the bitwise inequality construction on any fixed wiring. Historical priority for this particular fixed-depth criterion is unestablished. [Inequality and diagonal lower bound](../THEOREM.md)

## The reduction

For a set $W$ of senders write $N(W)$ for the readers of at least one of them. Call $W$ irredundant if every member has a reader reached by none of the other members. For a fixed rejected cell with true set $X$, choose an inclusion-minimal $W\subseteq X$ with $N(W)=N(X)$. Removing a sender with no private reader would preserve the union. Thus each sender in $W$ has a private reader, and these pairs are an induced matching. This neighborhood-union argument is related to Boolean-width and induced-matching methods in graph algorithms. [Bui-Xuan, Telle and Vatshelle](https://arxiv.org/abs/0903.4796) · [Neighbourhood equivalence and induced matchings](https://link.springer.com/article/10.1007/s00453-020-00692-9)

For each irredundant guess $W$, force its members true. Any reader touched by $W$ propagates the operand opposite a hit. If both operands are hit, the gate is true. At every remaining gate use the intersection of its two **raw** operands. Take the least solution of these rules. Besides requiring the designated outputs false, require every paid predecessor of a remaining gate to be false in this solution. This last condition is essential: it justifies removing all its incoming reads.

The resulting test is sound. The transformed true set contains the anchors. At a touched reader, if both original operands are true on the transformed set, the propagated operand is true. At a remaining gate, the guard makes both paid inputs empty, so any original firing is a raw firing. Thus the transformed set is closed under the original rules. Conversely, with $W$ chosen from the actual true gates as above, the original set is closed under the forced values, one-operand propagation and raw seeds. It contains the transformed least set. Every remaining reader has no actual true predecessor because $N(W)=N(X)$. Both the guard and the desired output test therefore pass. Lean proves the equivalence for finite directed wiring as well as existence of a guess with private readers. [Lean proof](../../../../lean/PEqualNP/PaidDepth/PrivateReaders.lean)

Once $W$ is fixed, propagation among touched gates uses only unions. Even if it cycles, its least closure is reachability from the forced constants, raw signals and remaining raw-intersection gates. The output and guard together request absence of a union of such signals. A reachable forced constant makes a branch empty. Raw exclusions give a single rectangle. At most $b=k-|W\cup N(W)|$ independent raw-intersection signals need to be absent. Each absence is a union of two rectangles. Partition these tests into $m$ groups, distribute within each group and take a balanced conjunction of the group unions. The common raw rectangle can be absorbed into the first group. The cost is at most $3m\,2^{b/m}$ for the branch. Taking the free union over irredundant $W$ proves the sharper estimate

$$
3m\sum_{W\ {\rm irredundant}}2^{(k-|W\cup N(W)|)/m}.
$$

Only one adequate guess per rejected cell is needed. If each such cell admits a generator inside its true gates of size at most $t$, one may enumerate the sets of size at most $t$; the binomial estimate with $t$ then holds even if the full wiring has much larger induced matchings. The entropy bound on the binomial sum proves the cell-specific necessity above.

For example, place arbitrary arms on all forward edges of a bipartite crown with $n$ senders and $n$ readers, missing just one distinct reader per sender. Both graph treewidth and the size of a set of pairwise unwired gates grow linearly. No three senders have private readers. Every nonempty irredundant guess hits at least $n-1$ gates, so the weighted bound is $O_D(2^{2n/m})$ even including its polynomially many nonempty guesses.

The earlier anchor argument required the guessed gates to feed every other true gate. Here the guesses need only account for which **readers** receive any true input. Arbitrarily many true gates may arise directly from raw inputs, including gates with no predecessors. The predecessor guard converts this weaker condition into a valid circuit reduction. [Earlier anchor reduction](../random-wiring/INDEPENDENT_GATES.md) · [Cut result and credits](THEOREM.md) · [Replay](REPLAY.md)
