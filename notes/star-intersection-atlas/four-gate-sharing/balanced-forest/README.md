# Sharing saves a vanishing fraction on every forest

In pjscruggs's bipartite star model, write C for the minimum number of binary intersections in a circuit and F for the minimum in a formula. Unions of row and column stars are free. For every finite bipartite forest, including arbitrary degrees and any number of components,

    C ≤ F ≤ C + O(√((C+1) log₂(C+2))).

The same inequality holds for all bipartite graphs of any fixed treewidth w, with a constant depending on w. Thus a sequence with growing circuit cost and a fixed positive percentage saving must have unbounded treewidth. In particular, searching larger hubs in trees cannot produce such a sequence. Whether even one tree saves two gates is open here. A bounded or an unbounded sublinear additive saving would both fit the theorem.

The geometric statement behind the bound concerns the bipartite complement. On N vertices of fixed treewidth, its edges can be covered by at most

    log₂ N + O_w(√(log₂ N · log₂ log₂ N))

rectangles as N grows. Intersect the complements of these rectangles to obtain a formula. Each factor is the free union of the row stars outside the rectangle's rows and the column stars outside its columns. Even this flat formula has leading coefficient one. The [earlier degree-bounded construction](../cube-embedding/README.md) retains a smaller additive term when both degree and treewidth are bounded. For matchings the classical middle-layer lower bound already requires an additive term of order log log N for flat covers.

## A binary tree for storing earlier neighbors

Start with a rooted binary tree decomposition of height H = O_w(log N) and constant bag size K, supplied by the balancing theorem of Bodlaender and Hagerup. One can start from a width-w decomposition with O(N) bags: in a rooted decomposition contract a child into its parent whenever the child's bag is contained in its parent's. Every remaining nonroot bag introduces a distinct vertex. Balancing at width max(2,w) suffices even for forests. [Bodlaender and Hagerup, §2, Lemma 2.2](https://ics-archive.science.uu.nl/research/techreps/repo/CS-1995/1995-25.pdf)

Give each vertex its highest bag as its home. Order vertices by home depth, breaking ties arbitrarily. Adjacent vertices appear together in a bag, so their homes lie on a single root-to-bag path. If y is an earlier neighbor of x, y occurs in x's home by the connectedness of y's bags. This includes ties, since adjacent vertices at equal home depth have the same home. Write D(x) for all earlier neighbors of x. Its size is at most K−1. Every edge is now recorded exactly once.

## Encode the branch using nearly one coordinate per bit

Let L = max(2,ceil(log₂ N)) and choose an integer a ≥ 1. Group consecutive bands of a tree levels into blocks. A block consists of a node at depth divisible by a and its descendants at distances less than a. Each block contains at most 2^a−1 bags, hence at most K(2^a−1) home vertices. Blocks themselves form a rooted tree of height at most H/a. Remove subtrees with no home vertices. Give a block P weight W(P) equal to the total number of home vertices below it, including its own. Thus the root has weight N.

For a child Q of P set s(Q) = ceil(log₂(W(P)/W(Q))). This is between 0 and L. At most 2^s siblings can have the same value s, since each has weight at least W(P)/2^s and the child weights sum to at most W(P). Write b(M) for the least d ≥ 0 with binom(d,floor(d/2)) ≥ M. There are M distinct equal-weight binary words of length b(M), and b(2^s) ≤ s+O(log(s+2)), since the largest binomial coefficient at length d is at least 2^d/(d+1).

Encode each child by concatenating two words:

1. A fixed-length middle-layer word of length b(L+1) naming its value s.
2. A middle-layer word of length b(2^s) naming that child among siblings with the same s.

Concatenate the child words along the root-to-block path. For different children the headers disagree in both directions if their s values differ. Otherwise their payloads do. Both disagreements lie within the shorter word, so any suffix preserves both. This lets one coordinate family handle both orders of incomparable blocks.

Pad every row word with zeros and every column word with ones to the maximum length d. For comparable blocks one word extends the other and the padded row is coordinatewise ≤ the padded column, whichever block is deeper. Incomparable blocks fail this test at their first differing child. Each failed bit is a rectangle. Along any path the unrounded log weight ratios telescope to at most log₂ N. Each edge adds at most O(log(L+2)) more bits from rounding, header and middle-layer redundancy. Therefore

    d ≤ log₂ N + O_w((L/a + 1) log(L+2)).

## Use short tags to test the remaining pairs

The tag of a vertex is its block depth together with a distinct slot within that block. Across the entire graph, the tag alphabet has size T ≤ (1+H/a) K 2^a, up to rounding. Within any chain of blocks, different vertices have different tags. If x and y are in comparable blocks and tag(y) occurs among the tags of D(x), then y is that earlier neighbor. Indeed, the recorded neighbor lies in x's block or an ancestor block, and its tag specifies the depth. On the chain containing the two candidates, only one block has this depth, and within it the slot is unique. The same reasoning works in the other direction. Thus a comparable pair is an edge exactly when either tag occurs in the opposite dictionary.

To realize the two membership tests together, independently mark each tag red with probability 1/2 and independently mark each tag blue with probability 1/2. One choice yields a rectangle:

* Its rows have a red own tag and no blue tag in their earlier-neighbor dictionary.
* Its columns have a blue own tag and no red tag in their earlier-neighbor dictionary.

This rectangle never contains a true membership in either direction. For any two tags and dictionaries giving two nonmemberships, the required inclusions and exclusions are consistent even when the tags coincide, because the two colors are independent. There are at most 2K prescribed bits, so success probability is at least 2^(−2K). The number of ordered configurations is at most (T+1)^(2K+2), by padding lists for the two dictionaries. A union bound over configurations gives q = O_K(log(T+1)) choices that cover every two-sided nonmembership. [Classical separating-code background](https://doi.org/10.1109/TIT.1964.1053689)

Together the d branch rectangles and q tag rectangles cover every nonedge and exclude every edge. Taking a = ceil(√(L log₂(L+2))) proves the geometric statement. This proof bounds the number of rectangles directly; a short adjacency label with an arbitrary decoder by itself gives no such count.

## Translate order into circuit cost

Restrict to one representative of every nonempty distinct neighborhood on each shore and remove isolated vertices. The resulting induced graph has at most the original circuit cost. Restriction preserves all distinctions among the chosen vertices: a deleted twin distinguishing two neighborhoods has a representative that also distinguishes them. The original graph is recovered by duplicating representatives and adding isolates. Duplication pulls each raw star back to a free union. Isolates cost at most two further intersections by masking the active rows and columns after an arbitrary extension. The edgeless case has cost zero.

Let X be a minimum vertex cover of the reduced graph and ν = |X| its matching number by Kőnig's theorem. Use a chordal completion with an elimination ordering of width at most w, so the later neighbors of any vertex form a clique of size at most w in the completion. For y outside X distinguish two cases using the **original** adjacency:

* If y has an earlier neighbor x in X, charge it to any such x. There are at most w charges per x, even counting all its later completion-neighbors.
* Otherwise N(y) is a nonempty subset of X and lies in the later-neighbor clique of y. Its earliest member x has at most w later completion-neighbors. There are at most 2^w possibilities for N(y) with this x. No two vertices realize the same such set in the reduced graph.

Consequently its order N' ≤ (1+w+2^w)ν. The elimination ordering can also be obtained from a width-w decomposition: make each bag a clique and eliminate vertices in decreasing home depth, breaking ties consistently. Every surviving neighbor is in the eliminated vertex's home bag.

The project's acyclic-to-parallel simulation covers the positive cells of a C-gate graph by at most 2^(C+1) rectangles, including the full-star terms. Each rectangle in a graph of treewidth w contains at most w independent matching edges. Otherwise it contains K_(w+1,w+1), which has K_(w+2) as a minor (contract w disjoint matched edges and retain the two endpoints of the remaining pair). Thus ν ≤ w·2^(C+1) for w ≥ 1, giving log₂ N' ≤ C + O_w(1). Substitution into the geometric estimate proves the circuit-to-formula inequality. Forests have w ≤ 1. [Parallel simulation](https://github.com/open-goat/pequalnp-proofs/discussions/19729#discussioncomment-19917939) · [Earlier matching argument](../matching-bound/README.md)

## Verification, credit and scope

The [official Mac verifier receipt](verification.txt) records ACCEPTED on Lean 4.36.0 with 1,660 constants rechecked. The 87 distinct source hashes in the manifest match the checked sources. The Lean theorem `PEqualNP.SparseSharing.BranchDecoder` proves the tag recovery and the exact d+q rectangle conclusion given the branch representation and separating palettes. The separate written argument above constructs those inputs, controls the number of coordinates and translates the result into circuit cost. The accompanying standard-library Python replay independently constructs concrete addresses, palettes and the resulting rectangles, and compares their union against the input graph on every cell. It verified 94,891 cells across all 328 labelled 3×3 forests at three block heights, larger forests including a 72-arm subdivided star, a ladder and a graph with two hubs and 80 common neighbors. Omitting the branch tests gave 26,371 false positives, while omitting the tag tests gave 12,092. A separate exhaustive check of all 4,096 labelled 3×4 graphs restored 49,152 cells and checked the individual vertex-cover charges. These are correctness controls for the construction.

```sh
python3 -I -B notes/star-intersection-atlas/four-gate-sharing/balanced-forest/replay.py
node tools/check-lean.mjs lean/PEqualNP/SparseSharing/BranchDecoder.lean notes/star-intersection-atlas/four-gate-sharing/balanced-forest/BranchDecoder.statement check
```

Pjscruggs supplied the star-intersection model. Bodlaender and Hagerup supplied the balanced decomposition. Gavoille and Labourel previously used related branch-local dictionaries for compact adjacency labels, and Jukna's degree-dependent biclique cover bound is discussed in Kowalik, Lauri and Socała. Our argument uses weighted middle-layer branch words and a simultaneous two-direction tag test to count the complement rectangles with leading coefficient one, then applies the project's ordinary-to-parallel bound. Historical priority for this combination is unestablished. [Gavoille and Labourel, §§2.2–2.4](https://dept-info.labri.fr/~gavoille/article/GL07.pdf) · [Kowalik, Lauri and Socała, Theorem 11](https://drops.dagstuhl.de/storage/00lipics/lipics-vol057-esa2016/LIPIcs.ESA.2016.58/LIPIcs.ESA.2016.58.pdf)
