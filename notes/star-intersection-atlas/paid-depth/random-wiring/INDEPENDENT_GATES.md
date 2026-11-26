# When gate reuse can increase the complement exponent

Suppose H is an undirected graph on the k ordered paid gates of a star-intersection diagram. For every edge {i,j} with i<j, gate i must occur on at least one arm of j. All other wires are optional, even reverse wires and self-loops under least-fixed-point semantics. Let α be the largest number of pairwise nonadjacent vertices of H.

Fix paid target depth D≥1, write m=2^(D−1) and a=2^(1/m). For **every** such diagram, every choice of raw inputs, and every output, its complement has an acyclic formula of cost at most

    3m · a^k · (1−1/a)^(−α).

The previous equality lower bound gives Ω_D(a^k) for the worst choice of masks and outputs on every fixed wiring. Thus α=o(k) forces the sharp exponent 1/m. Bounded α gives sharp order up to a constant factor. At depth two any fixed excess over exponent 1/2 requires a linear number of pairwise unwired gates in the forward graph. For an ordinary acyclic source one can take the entire paid dependency graph in topological order. For example, wiring every earlier gate to either arm of every later gate gives maximum treewidth yet α=1. Even arbitrary choices of arm placement and extra feedback then leave the worst cost within a constant factor of a^k.

The proof also gives an output-specific test. If every rejecting cell admits o(k) true gates that directly feed all its other true gates, the exponent is at most 1/m, whatever the topology. This condition can hold even if the wiring has a large independent set.

## Reducing a diagram after choosing true gates

Fix a set A of gates called anchors. Calculate auxiliary signals as follows. Force every gate in A true. At any other gate, for each arm that directly contains an anchor, propagate the opposite arm into the gate using free union. If neither arm contains an anchor, hold the auxiliary signal false. Take the least solution of these free-union rules. This is a system of unions of row stars, column stars, constants and other signals. Even with cycles, its least solution at each gate is a union of raw row and column masks, plus a possible true constant. Following all reachable seeds in its finite propagation graph computes these unions. Equivalently, compute the row and column contributions separately and unite them. The constant can be put on both sides.

For this A, require that all auxiliary output gates and raw output stars are absent. This is one rectangle. For each nonanchor gate neither of whose arms mentions an anchor, require at least one of its two arms to be absent when evaluated on the auxiliary signals. This is a union of at most two rectangles. No other checks are necessary.

For soundness, denote the set of true auxiliary signals at a cell by T. The anchors belong to T. If both arms of a touched gate are true on T, the free-union propagation rule puts that gate in T. At every untouched nonanchor the imposed test forbids both arms from being true. Hence T is closed under the original firing rule, so the least original state is contained in T. Absence of the outputs in T implies actual rejection. This direction requires no assertion that the guessed anchors really fire.

For completeness at a rejecting cell let X be the actual least state. Choose anchors in X such that every gate of X outside A has an arm mentioning A. Then X contains every auxiliary signal because it contains the anchors and satisfies every auxiliary propagation rule. In each rule the arm that mentions an anchor is already true. For each untouched nonanchor the actual gate is false, so at least one arm is absent on X and also on the smaller T. The output test passes. The [Lean reduction](../../../../lean/PEqualNP/PaidDepth/AnchorReduction.lean) checks both implications for a monotone arm operator with the stated least-closure hypotheses.

If there are b untouched nonanchors, distribute their tests evenly among m groups. Each group is a free union of at most 2^ceil(b/m) rectangles by distributivity. Put the common output restriction into the first group by intersecting its row and column masks in each rectangle. A balanced tree of m−1 paid intersections finishes the formula. This costs at most 3m a^b, including empty groups. Costs add when different anchor sets are freely united.

## Counting anchor sets in an ordered graph

For a fixed rejecting cell, scan the true gates in increasing order. Select a gate unless it already has an edge from a previously selected gate in H. The resulting A is independent in H and directly covers all other true gates. Let N⁺(A) be all later neighbors along the edges oriented from smaller to larger index. The complement of A ∪ N⁺(A) contains every untouched nonanchor. Thus it suffices to bound

    sum_{A independent} q^(|A|+|N⁺(A)|),   q=1/a.

This sum is at most (1−q)^(−α). To see it, sample each vertex independently with probability p=1−q. Process the sampled vertices in **decreasing** order, accepting a vertex if no previously accepted neighbor blocks it. The accepted set I is independent. For any fixed independent A, if all vertices of A were sampled and no vertex of N⁺(A) was sampled, then every vertex of A was accepted. The probability of this event is p^|A| q^|N⁺(A)|. Consequently the displayed sum is at most

    E[sum_{A ⊆ I} (q/p)^|A|] = E[(1+q/p)^|I|] ≤ p^(−α).

Multiplying by 3m a^k proves the theorem. For a fixed output one may replace α by the independence number on the nondesignated gates alone. At a rejecting cell every true anchor is nondesignated. Run the sampling argument on that induced graph and drop the extra outgoing neighbors among designated gates when bounding the weights from above. Increasing order chooses a certificate at one cell. Decreasing order bounds the total cost of all certificates. No random wiring hypothesis is used.

For the output-specific test, if s anchors always suffice on rejecting cells, take only subsets of size at most s. No independence assumption is necessary in the reduction itself. The formula cost is at most 3m a^k times the sum of binom(k,j) for 0≤j≤s. The logarithm of that factor is o(k) for s=o(k). In particular an excess exponential rate forces a rejecting cell at which every one-step dominating set within the true gates has linear size.

## What the counting method misses on sparse wiring

For maximum degree Δ, take an independent set of size at least k/(Δ+1) by greedy deletion. For each of its subsets A, the closed outgoing neighborhood has size at most (Δ+1)|A|. Consequently the full normalized anchor sum in the preceding proof is **at least**

    (1+q^(Δ+1))^(k/(Δ+1)).

The same exponential overcount occurs at any fixed average degree d. At least half the vertices have degree ≤ ceil(2d), and a greedy independent set among them has size at least k/[2(ceil(2d)+1)]. The estimate only concerns the sum that enumerates all independent sets. It is not a lower bound on circuit cost. In particular, counting all such sets cannot settle the bounded-mean-degree case at the baseline exponent, even if a different choice of witnesses could do so. The output-specific test above suggests investigating which anchor sets can actually be required together.

The weighted independent-set argument and the asymptotic gate count are written proofs. [Exact finite checks](check_anchors.py) compare the constructed row and column relations to direct least-fixed-point evaluation, and compare the weighted sum, reverse-greedy expectation and independence-number bound on all ordered six-vertex graphs. The model, earlier matching lower bound, and related project work are credited in the [companion theorem](THEOREM.md). [Replay](REPLAY.md)
