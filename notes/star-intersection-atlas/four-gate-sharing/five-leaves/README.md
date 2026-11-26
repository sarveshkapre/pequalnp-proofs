# Sharing on trees with five leaves and the 25-vertex boundary

In the row/column-star model, unions are free and a binary intersection costs one. Write C for the least circuit cost with reuse and F for the least formula cost, counting each occurrence.

**If a tree has at most five leaves after duplicate leaves are removed, then C ≤ 4 implies F ≤ 5.** For arbitrary trees, a counterexample to this implication must reduce to **19 through 24 vertices**, including at least six leaves and at least 13 nonleaves. The existence of any tree with C = 4 and F = 6 remains open.

The upper endpoint takes two steps. The largest twin-reduced induced tree in the five exceptional four-gate hosts has 25 vertices. There are exactly **313 unlabeled tree shapes** of that order across the five hosts, identifying a tree with its transpose. Every one has a formula consisting of a single intersection of six free star unions. The order-25 exclusion therefore depends on formula constructions as well as the geometry of the hosts.

## From a maximum matching to a vertex bound

Deleting one of two same-shore leaves with a common neighbor preserves both costs. Restrict the input sets to delete it, then copy the other leaf's memberships to restore it. The [four-gate classification](../README.md) shows that a tree requiring six formula intersections must occur in one of five finite graphs. In each such host an edge joins words r and c when a particular monotone function f is false at r & c. The [matching normalization](../spiders/README.md) shows that the largest matching in an induced forest is 11. We use these earlier results as lemmas.

Take a reduced tree on at least three vertices. Its leaf edges are pairwise disjoint. Choose a maximum matching M covering as many leaves as possible. If a leaf is exposed, its neighbor is already matched. Switching that edge to the leaf edge gains a covered leaf, since the neighbor has no second leaf. Hence every exposed vertex has degree at least two. Exposed vertices form an independent set.

Let s = |M|. Among the 2s matched endpoints, let t count the tree edges outside M. If u vertices are exposed, the tree has 2s+u−1 edges. Exactly s+t edges lie among matched endpoints. The remaining edges are incident to just one exposed vertex each, so

    2u ≤ (2s+u−1) − (s+t),     |V| = 2s+u ≤ 3s−1−t.

For s ≤ 8 this already gives at most 23 vertices. A universal vertex is easy to handle separately. If a row is universal, any other row of degree two would form a four-cycle with it. After twin reduction the tree is a star with once-subdivided arms and at most one unsubdivided arm. It has at most 2s+1 ≤ 23 vertices. Transposition covers a universal column.

Otherwise every vertex has a nonneighbor. As in the matching normalization, enlarge each matched pair independently to (R,C) with R | C = 255 and R & C maximal among words where f is false. Both endpoint words satisfy f = true. Enlarging preserves every matched edge, keeps distinct matched vertices distinct and can only delete cross edges. The minimum cross-edge count in these normalized forests is therefore a lower bound on t in the original tree.

| Host | s = 9 | s = 10 | s = 11 | Normalized size-ten sets with four cross edges |
| --- | ---: | ---: | ---: | ---: |
| 1 | 3 | 4 | 8 | 1 |
| 2 | 3 | 6 | 9 | 0 |
| 3 | 3 | 4 | 8 | 1 |
| 4 | 3 | 4 | 8 | 5 |
| 5 | 3 | 4 | 8 | 4 |

The checker enumerates subsets of the ordered pair types. It contracts each matched edge, rejects an opposite pair of cross edges, and rejects a new vertex that hits any existing connected component twice. These are exactly the possible ways to close a cycle. Thus the respective order bounds at sizes 9, 10 and 11 are 23, 25 and 24. Host 2 has order bound 23, attained by the explicit 12-by-11 tree in the replay.

## All trees at order 25

Equality requires s = 10, exactly four cross edges, and exactly five exposed vertices, all of degree two. The four cross edges join disjoint pairs of matched edges in every extremal normalized set. The matched endpoints therefore induce four four-vertex paths and two isolated edges. Every cross edge present before normalization survives here, since the counts are equal. The five exposed vertices must connect the six components into a tree.

We recover every possible original set of matched labels. For each normalized endpoint R try every subword r of R with f(r) true. If shrinking it alone creates a forbidden edge to an opposite normalized endpoint, monotonicity rules it out. Collapse only words with identical neighborhoods on the entire 256-word opposite shore. Try every remaining joint assignment, retaining exactly those with the required matched-endpoint graph.

For each remaining assignment, try every host label on either shore as an exposed vertex. It must see exactly two matched endpoints in different components. Choose five such labels, rejecting any edge between exposed vertices or any choice that closes a cycle. This enumerates every order-25 tree. Conversely each completed selection is a connected acyclic induced restriction of the actual host. The replay checks twin reduction and computes an isomorphism key by rooting at the center or either center and sorting branches recursively.

The 11 normalized sets yield 336 matched-endpoint assignments and 439,392 completed selections after full-neighborhood type reduction. They give 313 distinct trees. Hosts 1, 3, 4 and 5 each attain order 25. For each of the 313 trees the certificate supplies six-bit row words. Give each column every bit absent from all its neighbors' row words. Checking every cell shows that its row and column share a bit exactly at nonedges. Each bit thus excludes a rectangle, and the intersection of six free star unions computes the tree with five paid gates.

## All trees with at most five reduced leaves

For any nontrivial tree the number of leaves is two plus the sum of degree minus two over branching vertices. Paths and one branching vertex are covered by the [spider result](../spiders/README.md). Two degree-three branching vertices are covered by the [two-branch result](../two-hubs/README.md). With at most five leaves there are exactly two further degree patterns: one vertex of degree four and one of degree three, or three vertices of degree three.

Suppress degree-two vertices to obtain the branching skeleton. In the second pattern the three hubs lie along a path. A reduced tree has at most one length-one outer arm at any hub. The smallest reduced representatives have outer arm lengths (2,2,1) and (2,1) in the first pattern, and (2,1), (1), (2,1) in the second. Start all inter-hub distances at one. Every other profile is obtained by successively subdividing edges of these segments. Sort indistinguishable arms and identify reversal of the three-hub skeleton. Subdivision never decreases diameter or matching number. The prior path obstruction gives diameter at most 20 in the exceptional hosts, so these cutoffs are exhaustive.

| Branch degrees | Diameter ≤ 20 and matching ≤ 11 | Remaining after earlier core and induced-subtree results | Covered by six rectangles | Excluded from all five hosts |
| --- | ---: | ---: | ---: | ---: |
| 4, 3 | 9,865 | 6,814 | 6,500 | 314 |
| 3, 3, 3 | 30,306 | 24,198 | 23,125 | 1,073 |

The replay constructs each tree and computes its matching and diameter. For old spider obstructions it takes the longest branch in each direction from a hub. For an old two-hub obstruction it retains the connecting path and the two longest outward arms at each end. Every retained shape is an induced subtree. The remaining positive certificates check all cells on a larger tree at the same inter-hub distances. Truncating its outer arms restricts its formula. Each negative uses a specified matching in an induced subtree. The previous exhaustive checker excludes that matching's pattern of absent cross edges in all five hosts. Six actual four-gate host embeddings provide positive controls across the two new families.

Combining the five-leaf theorem with the earlier twelve-nonleaf formula bound gives at least 19 vertices for a reduced counterexample. The order-25 classification gives the upper bound 24. Neither endpoint is asserted to be attainable by a counterexample.

## Replay and attribution

From this directory, with Python 3.10+ and a C++17 compiler, use:

```sh
c++ -std=c++17 -O3 -Wall -Wextra -pedantic ../spiders/matching_check.cpp -o /tmp/tree-matching-check
c++ -std=c++17 -O3 -Wall -Wextra -pedantic contacts.cpp -o /tmp/tree-contact-check
python3 -I -B extremal.py /tmp/tree-contact-check
python3 -I -B replay.py /tmp/tree-matching-check
```

These are written proofs with exhaustive finite checks and constructive certificates. The package has no Lean or official-verifier verdict. The earlier four-gate reduction, spider and two-hub results have separate replays in their linked packages.

Pjscruggs developed the star-intersection atlas. The [sharing discussion](https://github.com/open-goat/pequalnp-proofs/discussions/23239) records the three-gate forms with ChatGPT Pro and the forest question. The contribution here is the matching contact bound, the exact order-25 classification and the five-leaf theorem. The graph-from-stars model has classical antecedents in [Pudlák, Rödl and Savický](https://users.math.cas.cz/~pudlak/graph-complexity.pdf) and [Jukna](https://doi.org/10.1017/S0963548306007620). Historical priority for the exact finite results is unestablished.
