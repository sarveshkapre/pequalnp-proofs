# When a cut with many readers makes a single output easier to complement

In pjscruggs’s star model, arbitrary unions of row sets, column sets and prior wires are free. Each binary intersection costs one and adds one to paid depth. For an acyclic source of $k=2n$ paid gates, consider computing the complement of **one** designated output with a circuit of paid depth two. Number the source gates in any topological order. A late gate *reads* an early gate if either of its operands includes that gate. Count distinct readers, including a reader using the same gate on both operands only once.

**Dense cut.** Fix $\delta>0$. If every gate among the first $n$ has at least $(1/3+\delta)n$ readers among the last $n$, the worst complement cost on that wiring is $\Theta_\delta(2^n)$. All dependencies within either half and all arm assignments are arbitrary. The upper bound holds uniformly under additional forward reads. To attain the lower bound on each wiring, give each source gate its own raw bit-mismatch test and tap all gates. On equal words no gate fires, while a differing bit fires its gate directly. The complement is a diagonal of size $2^{2n}$, which needs $\Omega(2^n)$ gates at depth two.

**Sparse random cut.** Require each possible forward read between the halves independently with probability $p$, then allow arbitrary additional forward reads, arbitrary internal acyclic wiring and arbitrary placement on the two operands. With probability tending to one, the worst complement cost has exponent $1/2$ per source gate whenever $np\to\infty$. If $np\ge128\ln(n+1)$, the cost is $\Theta(2^n)$ up to an absolute constant. The constant 128 is a sufficient value in the proof.

**Converse.** Fix $\epsilon>0$. For all sufficiently large $n$, a circuit whose output requires at least $2^{(1/2+\epsilon)2n}$ gates to complement must satisfy the following at **every** balanced topological cut. Some set of at least $c_\epsilon n$ early gates is read by fewer than $n/3$ late gates. In particular it has no direct read into more than two thirds of the late half.

These statements use the earlier unrestricted $P(k)2^{3k/5}$ upper bound with a fixed polynomial $P$, and the established diagonal lower bound. The numerical threshold is a sufficient condition arising from that upper estimate. Both graphs in a cut are graphs of dependencies between gates. [Unrestricted bound](../structure/UNRESTRICTED.md) · [Diagonal lower bound](../THEOREM.md) · [pjscruggs’s star atlas](https://github.com/open-goat/pequalnp-proofs/discussions/19729) · [Cavalar and Oliveira’s inequality construction](https://arxiv.org/html/2503.14117v1#S4.SS2)

## Certifying a rejected input

At a fixed row and column, a set of gates $X$ is closed if it contains every gate whose two operands are true on $X$. Rejection is equivalent to the existence of a closed set disjoint from the designated gates. The actual least firing state provides such a set whenever the input is rejected. A raw signal in the final union supplies one common rectangle restriction throughout.

Write $A$ for the prefix and $B$ for the suffix. For $T\subseteq A$, write $N(T)\subseteq B$ for its readers. Fix an integer $1\le r\le n$. The following branches cover all rejected cells and each branch implies rejection. [Lean equivalence](../../../../lean/PEqualNP/PaidDepth/ReaderCut.lean)

1. **Few true prefix gates.** Guess $T\subseteq A$ with $|T|<r$. Require that it excludes the designated prefix gates and that it is closed on the prefix. Supply exactly these guessed constants to the suffix and test whether the suffix rejects. Prefix closure makes the actual prefix a subset of $T$. A larger supplied set can only turn on more suffix signals. Conversely, guessing the actual prefix passes both checks on a rejected cell.
2. **Many true prefix gates.** Select $W\subseteq A$ of size $r$ and force those gates true. A gate reading a forced value has one true operand, so it can be replaced by its other operand. If both operands read a forced value it is constant true. The modified computation dominates the original. On a rejecting input with at least $r$ true prefix gates, select any $r$ of them and the computation is exact. At most $2n-r-|N(W)|$ paid gates survive. Substituting free unions for the removed outputs preserves the model and acyclicity.

There is no need to compute the guessed set from an input with another circuit. The output is a free union of the sound alternatives. The first branch checks closure once for each guess. The second branch can use the unrestricted complementation theorem on its simplified source.

## Paying for a small guess

For $j=|T|$, put $u=n-j$ and $v=n-|N(T)|$. Each of the $u$ prefix gates outside $T$ must have a false operand after substituting $T$. This is a union of two rectangles. An operand reading a guessed true gate has empty rejection rectangle. No check is required for the gates in $T$. In the suffix, all readers in $N(T)$ simplify to free unions or constants. The remaining $v$ gates admit a rejection cover of at most $2^v$ rectangles. One chooses a rejecting operand per paid gate and collects the raw exclusions reachable from the outputs. This certificate construction also works when some choices are unused. [Orientation argument](../product-outputs/TENSOR.md)

If $u\ge v$, move $\lfloor(u-v)/2\rfloor$ of the independent prefix checks into the suffix bank by distributivity. Take a second bank for the remaining prefix checks. If $u<v$, use one bank for the entire prefix and one for the suffix. Purchase one gate per rectangle, take two free unions and intersect them. Each bank has at most $2^{\max(v,\lceil(u+v)/2\rceil)}$ entries. This balancing step is needed for the constant-factor sparse bound.

Let $L(r)=\min_{|W|=r}|N(W)|$. Up to absolute constant factors the total cost plus one is at most

$$
\sum_{|T|<r} 2^{\max(n-|N(T)|,\lceil(2n-|T|-|N(T)|)/2\rceil)}
+\binom nr P(2n)2^{3(2n-r-L(r))/5}.
$$

A missing constraint or an empty branch only decreases the cost. Taking $r=1$ leaves one small guess of cost $O(2^n)$. When $L(1)\ge(1/3+\delta)n$, the other term has exponential slack $3\delta n/5$, which absorbs the polynomial. This proves the dense result.

More generally, if $r=o(n)$ and $L(r)\ge n/3-o(n)$, both terms are at most $2^{n+o(n)}$. For the converse, choose $r=\lfloor\eta n\rfloor$ with $0<\eta<1/2$ and binary entropy $H_2(\eta)<2\epsilon$. If $L(r)\ge n/3$, both terms are at most $P'(n)2^{n+nH_2(\eta)}$ for a fixed polynomial $P'$, contradicting the assumed cost for large $n$. One can take $c_\epsilon=\eta/2$.

## A random cut suffices with adversarial wiring inside the parts

Let $d=np\to\infty$ and take $r=\lceil3/p\rceil$, so $r=o(n)$. If an $r$-set meets fewer than half the late readers, there is an empty $r$ by $\lceil n/2\rceil$ rectangle in the required edges. By a union bound the probability is at most
$4^n(1-p)^{r\lceil n/2\rceil}\le\exp((\ln4-3/2)n)$.
Thus $L(r)\ge n/2$ with probability tending to one. The preceding theorem gives the sharp exponent.

For the constant-factor claim assume $d\ge128\ln(n+1)$. For a fixed $j$-set with $1\le j<r$, its number of readers is binomial with mean $\mu=n(1-(1-p)^j)\ge dj/4$. Here $pj<3$ and $1-e^{-x}\ge x/4$ on $[0,3]$. The probability of fewer than half the mean is at most $\exp(-\mu/8)$, by applying Markov’s inequality to $2^{-|N(T)|}$. A union bound over at most $n^j$ sets for each $j$ shows, with probability tending to one, that every such set has at least $dj/8\ge4j\log_2(n+1)$ readers. In particular $v\le u$. Its small-guess cost is $O(2^n(n+1)^{-2j})$. Summing over guesses costs $O(2^n)$. The empty guess also costs $O(2^n)$. The large guesses have exponent at most $9n/10+o(n)$. This proves the claim uniformly for every source extending the sampled cross edges.

The arbitrary acyclic single-output exponent remains between $1/2$ and $3/5$. Independent repetitions and inputs encoding an optional mask give the baseline. These cut bounds also apply to internally interacting circuits of linear treewidth and independence number. A separate obstruction uses activity across the whole directed diagram and allows feedback. [Private readers](PRIVATE_READERS.md) · [Earlier independent-copy result](../product-outputs/TENSOR.md) · [Replay](REPLAY.md)
