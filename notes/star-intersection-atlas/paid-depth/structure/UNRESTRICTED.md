# A three-fifths upper exponent for unrestricted two-layer complementation

In the free-union star model, every acyclic source of k paid binary intersections has a complement circuit of paid depth at most two and size

    (k+1)^O(1) · 2^(3k/5).

The source and the target may reuse wires. The intersection cost counts gates and allows arbitrary finite raw row and column sets. The construction is nonuniform. It uses the existence of small finite dictionaries and places no running-time bound on finding them. Equality versus inequality supplies the lower bound Ω(2^(k/2)). Thus the unresolved interval for the worst exponential rate is [1/2, 3/5].

For comparison, a direct cut after b gates pays 3^b to record every possible early rejection state (inactive, left, or right). At most 2^(k−b) binary completions of the suffix then need two more gates each. This gives the upper exponent log₂3/(1+log₂3) ≈ 0.613147. The improvement comes from moving selected obligations into the suffix’s own rectangle and bounding the cost under every possible set of mandatory early obligations.

## A prefix matched in topological order

Normalize each operand to a union of raw stars and predecessor gates. Scan gates in topological order. Match a new gate to any currently unmatched predecessor, if one exists. In every prefix the matching is maximal, so its unmatched vertices form an independent set. Write S for the 2h endpoints of the h matched edges and E for the n unmatched vertices. Thus the prefix has b=2h+n vertices. Every dependency within the prefix touching an unmatched gate has its other end in S.

Give each gate in S one of three states: inactive, or active with one of two specified rejecting arms. An active gate cannot select an operand referencing an inactive gate in S. Each matched edge excludes at least one of its nine state pairs. The edges are disjoint, leaving at most 8^h valid signatures. Fix one signature σ. Let D⊆E be all unmatched predecessors demanded by its selected arms. The construction below checks their raw masks. D depends only on σ.

Fix one binary choice per suffix gate. Starting from output gates and following rejecting arms backwards only through demanded suffix gates yields raw exclusions, a demand T⊆S, and a demand A⊆E. Raw exclusions are a rectangle, since all accumulated row masks and all accumulated column masks must be absent. Unused choices have no effect. Initial raw output masks are included.

Use the dictionary lemma below to choose a retained set B⊆A with |A∖B|≤n/10+O(1). For the omitted gates select one arm each, put their raw exclusions into the suffix rectangle and add every predecessor they require to T. Their only paid predecessors lie in S. There are at most 2^(k−b+n/10+O(1)) resulting suffix labels. A label uses one depth-one rectangle.

Its other operand freely unions entries of a shared depth-one rectangle bank. For each σ compatible with the augmented T, set J=D∪B. Select one arm for each j∈J; discard choices that demand an inactive gate of S. The bank entry imposes all raw exclusions from those arms and from σ. The raw rectangle depends only on σ, J and the choices on J. A label selects the entries for its own B. Even if D meets the omitted set, its two choices can coexist: either rejecting arm suffices to certify a gate false. The [Lean prefix theorem](../../../../lean/PEqualNP/PaidDepth/MatchedPrefix.lean) checks this equivalence for arbitrary acyclic wiring on S and an independent E, arbitrary output demands on S, and even overlapping kept and omitted demands on E. Its raw predicate is general; here its failure is a rectangle.

Intersect the suffix rectangle with its selected free union, paying one more gate per label, then freely union the results. An accepted pair certifies every demanded gate false by topological induction. At a rejecting cell, choose true rejection witnesses by marking all false S gates and selecting an actually false operand wherever required. All parts then pass. The gate count is the size of the shared bank plus at most twice the number of suffix labels.

## A dictionary that survives mandatory demands

For n coordinates there is a family of retained subsets with these two properties:

1. Every demand A contains some retained B at distance |A∖B|≤n/10+O(1).
2. For every mandatory set D, the sum of 2^|J| over the **distinct** sets J=D∪B is at most poly(n+1)·2^(27n/20).

Each term counts all choices of rejecting arms on J. Uniformity over D lets the same retained B be selected before σ is known. Pad to a multiple of ten with at most nine unused coordinates. Taking B inside A ensures a demand on real gates always retains only real gates. Padding changes bounds by absolute factors.

Here is a proof. Let R=n/10. Treat each demand size a separately; there are n+1 sizes. For a≤9n/20, take all t-subsets where t=max(0,a−R). For d=|D|, let j count the elements of B outside D. There are at most binom(n−d,j) distinct projections of size j. Their total weight at that size is at most 2^(d+j)·2^(n−d)≤2^(n+t)≤2^(27n/20). Sum over j.

For larger a take t=a−R. Retain every t-subset independently with probability p=min(1,10(n+1)/binom(a,R)). When p<1, a fixed a-set is missed with probability at most exp(−10(n+1)); with p=1 coverage is certain. For fixed D and j, the number X of distinct j-subsets J₀ outside D that are projections B∖D is a sum of independent indicators: different J₀ use disjoint candidate t-subsets. Its mean is at most

    binom(n−d,j) · min(1, p binom(d,t−j)).

Invalid binomial indices count as zero. The exponential moment satisfies E[exp X]≤exp((e−1)E[X]). Except with probability exp(−10(n+1)), X≤(e−1)E[X]+10(n+1). A union bound over demands, mandatory sets and j gives positive probability that coverage and all bounds hold together, for each a. Summing over a preserves the polynomial prefactor. This is an asymmetric covering argument; the weighted bound after adjoining every D is the additional requirement here.

The additive term in X costs only poly(n+1)·2^n, because d+j≤n. For the mean use min(1,u)≤u^λ for 0<λ≤1. Write x=a/n, ρ=1/10, and put z=τ^P and λ=P/Q. The coefficient bound binom(n−d,j)(2z)^j≤(1+2z)^(n−d) and binom(d,t−j)^λ z^(t−j)≤(1+τ^Q)^(λd) give the following upper bound on the base-two log of the weighted mean, divided by n, up to O(log(n+1)/n):

    max(log₂(1+2z), 1+λ log₂(1+τ^Q))
        −(x−ρ)log₂ z −λ[x log₂ x − (x−ρ)log₂(x−ρ) − ρ log₂ ρ].

Here binom(a,R)≥2^(a H₂(R/a))/(a+1), from the modal term of the binomial distribution with probability R/a. For fixed P,Q,τ the displayed expression is convex in x, since the bracket is concave. The following two intervals therefore require only endpoint checks.

| x | P | Q | τ | Bound at both endpoints |
| --- | --- | --- | --- | --- |
| [9/20, 4/5] | 5 | 9 | 49/50 | < 27/20 |
| [4/5, 1] | 3 | 5 | 1 | < 27/20 |

Both branches of the maximum at each endpoint are checked by clearing denominators and comparing integers. The [exact certificate](check_unrestricted.py) performs all eight comparisons. This proves the dictionary lemma.

## Balance the two layers

The bank uses at most poly(k+1)·2^(3h+27n/20) entries: there are 8^h signatures, with the weighted dictionary bound for each. Put W=2h+9n/10. The bank exponent is 3W/2 and the suffix exponent is k−W. When a scanned vertex remains unmatched, W increases by 9/10. When it matches an old unmatched vertex, h increases by one and n decreases by one, so W increases by 11/10. It starts at zero and ends at least at 9k/10. Choose the first prefix with W≥2k/5. Both exponents are then at most 3k/5+O(1), proving the claim. Empty sources and empty banks admit the same bounds using constants.

The exact numerical comparisons and the semantics of the transformation have independent replays. The probabilistic existence and gate-count analysis above are written mathematics. This upper bound leaves open whether reuse can raise the worst exponent above the 1/2 attained by parallel sources and arbitrary formulas.

Pjscruggs provided the project’s star-intersection atlas. Cavalar and Oliveira established the inequality complexity used on the lower-bound side. Asymmetric binary covering codes have a classical literature, including work by Cooper, Ellis and Kahng; the projection-weighted property above is proved directly. Historical priority for this specific star-model exponent has not been established. [Atlas](https://github.com/pjscruggs/pequalnp-proofs/tree/7da7d81614b93ea808c11ac27f27136942fec385/notes/star-intersection-atlas) · [Cavalar and Oliveira](https://eccc.weizmann.ac.il/report/2025/033/) · [Cooper, Ellis and Kahng](https://arxiv.org/abs/math/0309081) · [Replay](REPLAY.md)
