# Sharp fixed-depth complementation after adding random predecessor wires

The randomness is in the connections between paid gates. The row and column sets, the raw stars on every arm, the output gates and all additional connections can be chosen after seeing those random wires. In particular the graph being complemented need not be random.

Use pjscruggs’s star model. Raw row and column stars and their unions are free. A paid gate intersects two arms, each a union of raw stars and paid predecessor signals. An acyclic diagram uses its usual evaluation. A diagram with feedback uses the least fixed point, starting every gate false. All targets below are acyclic formulas. The paid depth counts intersections along a path.

Fix a target depth D ≥ 1. Write m = 2^(D−1) and a = 2^(1/m). Start with k ordered paid gates. For each pair j < i independently, place j on a random subset of the two arms of i. Each arm receives it with probability at least p > 0. The two choices for the **same** pair may have any joint law. In particular, an input can be forbidden to appear on both arms. The laws need not be identical. Call the resulting connections H.

Let M(H) be the largest minimum depth-D formula cost for the complement, over all finite row and column sets, raw masks, outputs and **all diagrams containing H** on these k gates. Extra connections may include reverse edges and self-loops under least-fixed-point semantics.

**Theorem.** For constants depending only on D,

    c_D · a^k ≤ E M(H) ≤ C_D · a^k · exp(C_D/p).

Costs here and below concern k≥1. The lower bound holds on every wiring even if the target may reuse gates. At fixed positive p the expected worst cost is consequently Θ_D,p(2^(k/m)). If kp tends to infinity, the base-two exponent per source gate tends to 1/m with probability tending to one. A failure by a fixed positive amount has exponentially small probability. At depth two the sharp exponent is 1/2. The unconditional upper exponent for arbitrary acyclic wiring remains 3/5. The random statement permits even an adversary who chooses the extra wires, graph and output after seeing H.

A [companion deterministic theorem](INDEPENDENT_GATES.md) proves the sharp exponent whenever the forward wiring has sublinear independence number. It also gives a necessary condition on the actual true gates of a rejecting cell.

The random-wiring result survives the deletion or redesign of all wires incident to any o(k) chosen gates when kp tends to infinity. In the pure ordered model with homogeneous arm marginal p, only p of order 1/k can support a strict excess exponent along a whole sequence. These two qualifications are proved below. The sparse conclusion applies to the pure model. Unrestricted additions to a nearly empty random diagram could supply almost the entire wiring.

## One certificate for all diagrams containing a specified set of wires

For any set T of possibly true gates, call an arm of i legal if none of its paid predecessors belong to T. A support T is admissible if every gate outside T has at least one legal arm. Let h_H(T) count the gates outside T with two legal arms. Put

    Z(H) = sum over admissible T of a^h_H(T).

Adding connections can only remove admissible supports or reduce h on surviving supports. Thus Z decreases weakly under arbitrary additional connections.

For a specified output, retain only supports disjoint from its paid output gates. For each gate outside T choose one legal arm. Require that all the raw signals on the chosen arm are absent. The allowed rows times the allowed columns form one rectangle. If these checks hold, updating the gates from any state contained in T stays inside T. Hence the least fixed point is contained in T and the output gates are false. Conversely, at a rejecting cell use the actual set of true gates as T. Each gate outside it has an arm with absent raw inputs and all predecessors false. Raw output stars add one common rectangle restriction to every certificate. The [Lean theorem](../../../../lean/PEqualNP/PaidDepth/SupportBlocks.lean) proves the equivalence for an arbitrary partition of the gates into blocks under explicit least-prefixed-point hypotheses.

Every global choice of arms restricts to each block. Conversely, taking each gate’s choice from its own block assembles a global choice for the same support. The partition can therefore depend on T. At a fixed support, only h gates have a choice of arm. Split them evenly over m blocks and place all other obligatory checks anywhere in these blocks. For a block with b choices, freely union at most 2^b rectangles, each costing at most one paid intersection. Intersect the m block outputs with a balanced tree. The choices of arms in different blocks are independent once T is specified. Free union over T gives a depth-D formula of cost at most

    sum_T (m · 2^ceil(h_H(T)/m) + m−1) ≤ 3m · Z(H).

The bound applies simultaneously to every completion of H, because its support sum cannot increase. It also applies to arbitrary finite universes. Counting all supports can overcount a particular output very substantially.

## Estimating the support sum

Fix a subset T, and process gate indices in increasing order. A gate in T contributes weight 1 and increases the number s of possible earlier true gates by one. A gate outside T contributes weight a if both arms are legal, 1 if just one is legal, and zero if neither is legal. Its expected weight for s=0 is exactly a. For s ≥ 1 it is at most

    v_s = min(2 exp(−ps), a − (a−1)(1−exp(−ps))).

Indeed the probability of avoiding all s sources on either specified arm is at most (1−p)^s. The weight never exceeds the number of legal arms, since 1 < a ≤ 2. Also, if the first arm is hit the weight is at most 1. These two facts give the two bounds without assuming independent arms. Incoming random connections to different destinations are independent, so for this fixed T the expectations of gate weights multiply.

Group subsets T by their number t of true indices and the lengths r₀,…,rₜ of the intervening runs of false indices. Each such list with sum k−t specifies exactly one subset. Divide its expected weight by a^k. The run before the first true index costs no factor. For each later run the factor is at most (v_s/a)^r_s, with v_s < a. Sum over all nonnegative later run lengths, dropping the length constraint, and then sum the weights a^(−t). This gives

    E Z(H) / a^k ≤ (1−1/a)^−1 · product_{s≥1}(1−v_s/a)^−1.

For completeness, the logarithm of the product is at most O_D(1/p), uniformly even as p tends to zero. Put L = ceil(log(4)/p), using natural logarithms. For 1 ≤ s ≤ L the gap 1−v_s/a is at least (1−1/a)(1−exp(−ps)). The sum of −log(1−exp(−ps)) over all s ≥ 1 is at most 2/p. This follows by expanding the logarithm as a positive series, summing the geometric progression, and using exp(pj)−1 ≥ pj and sum 1/j² ≤ 2. The constant gap factor contributes O_D(L). For s > L, v_s/a ≤ 2 exp(−ps)/a ≤ 1/2. Use −log(1−u) ≤ 2u and sum the geometric tail, of order 1/p. This proves the claimed upper estimate. Markov's inequality gives, for each fixed ε > 0,

    Pr[M(H) > 2^((1/m+ε)k)] ≤ C_D · exp(C_D/p − εk log 2).

There is also a finite form of the counting argument. Let P(n,s) be the expected unnormalized weight after n gates with s true indices. At zero true indices the mass grows by a factor a. For s+1 true indices its next value is at most v_(s+1) P(n,s+1) + P(n,s). Here v is the common upper bound on the conditional incoming weight for each fixed support, allowing the laws to differ. Put b₀=1 and b_(s+1)=b_s/(a−v_(s+1)). Induction gives P(n,s)≤a^n b_s, because (a−v_(s+1))b_(s+1)=b_s. The [Lean finite inequality](../../../../lean/PEqualNP/PaidDepth/SupportMass.lean) checks the resulting sum bound. Summing b_s gives the same infinite-product estimate used above.

## Matching lower bound on every wiring

Designate all gates as outputs. Use two raw arms at gate i to test whether the i-th bits differ. The first raw arm is true if either string's i-th bit is one, and the other is true if either bit is zero. If a bit mismatches, its gate fires immediately. If every bit agrees, the all-false state is already a fixed point. This realizes inequality on k-bit strings whatever the connections are, including feedback. Its complement is equality on 2^k labels. The [fixed-depth matching lower bound](../THEOREM.md) gives Ω_D(2^(k/m)) against arbitrary circuit targets. Thus even choosing the wiring first cannot lower the worst-case rate below 1/m.

## Adversarial changes and the sparse regime

Suppose J consists of r gates whose incident connections may be removed arbitrarily. Keep only the sampled connections among the other k−r gates. An admissible support induces an admissible support there. In summing over possible states on J, each included gate costs one and each excluded gate costs at most a. The total extension factor is at most (1+a)^r. The score of the damaged wiring, even after arbitrary extra connections, is bounded by (1+a)^r times the score of that induced sampled diagram. Taking a union bound via the sum over all size-r exceptional sets gives

    E[max damaged cost] ≤ C_D · binom(k,r) · (1+a)^r · a^(k−r) · exp(C_D/p).

Any set of at most r gates can be extended to one of exactly r. When r=o(k) and kp tends to infinity, all the extra logarithmic costs are o(k). The same lower bound and Markov argument apply.

For the pure ordered model write e for the number of ordered pairs joined on at least one arm. At most 2e gates are incident to a wire. Put all isolated nonoutputs inside T and all isolated outputs outside T. At a rejecting cell this is always allowed, because an isolated gate affects no other gate. The remaining supports have at most 2^(2e) choices. The same block construction therefore costs at most 3m · a^k · 4^e. If both arm marginals equal p, each independent pair is joined with probability at most 2p. Thus E[4^e] ≤ exp(3pk(k−1)). Together the dense and sparse estimates give

    log₂ E[pure worst cost] = k/m + O_D(1 + min(pk², 1/p)).

This settles the exponential rate both for pk → 0 and for pk → infinity. It leaves the bounded positive mean-degree regime open in general. The bounds concern representation size. They place no polynomial-time requirement on finding an optimal representation.

## Scope and prior work

Pudlák, Rödl and Savický introduced graph complexity. Pjscruggs supplied the project’s star-intersection atlas. Cavalar and Oliveira’s bitwise inequality construction supplies the lower-bound source and their work treats cyclic graph covers. The project’s fixed-depth equality bound supplies the target lower bound. The parallel investigation of negative Boolean rank studies how many full rejection rectangles are necessary. The size estimate here groups legal arms after fixing a possible true set. Historical priority for this random-wiring theorem is unestablished. [Graph complexity](https://users.math.cas.cz/~pudlak/graph-complexity.pdf) · [Atlas](https://github.com/pjscruggs/pequalnp-proofs/tree/7da7d81614b93ea808c11ac27f27136942fec385/notes/star-intersection-atlas) · [Cavalar and Oliveira](https://eccc.weizmann.ac.il/report/2025/033/) · [Negative-rank discussion](https://github.com/open-goat/pequalnp-proofs/discussions/19729#discussioncomment-19919194) · [Previous unrestricted bound](../structure/UNRESTRICTED.md) · [Replay](REPLAY.md)
