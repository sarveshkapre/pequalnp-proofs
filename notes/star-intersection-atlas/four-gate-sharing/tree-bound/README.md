# Four circuit intersections suffice to guarantee a five-intersection formula on trees

For every finite bipartite **tree** T, if a circuit for T uses at most four binary intersections, T has a formula using at most five. A circuit may reuse earlier gates. A formula pays per occurrence. Arbitrary unions of row and column stars are free in both models.

There is also an unconditional result. Every tree with at most **20 vertices after duplicate leaves are removed** has a five-intersection formula, irrespective of circuit cost. Consequently, every bipartite forest with at most 19 vertices and no isolated vertices has one. Add a single column and join it to one row in each component. The resulting graph is a tree on at most 20 vertices, and deleting the new column restricts its formula to the original forest.

The earlier [four-gate classification](../README.md) and [matching and order-25 theorem](../five-leaves/README.md) reduce the problem to connected, twin-reduced induced trees in five explicitly given hosts, on at most 24 vertices. Duplicate leaves with a common neighbor can be removed by restriction and restored by copying the other leaf’s input memberships. We close the remaining range in two different ways.

## Trees of order 24

Choose a maximum matching covering all leaves. Write s for its size, t for the number of other edges between its endpoints, and u for the number of uncovered vertices. The uncovered vertices are independent, each of degree at least two. Counting edges gives 2s + u ≤ 3s − 1 − t. The [previous contact bounds](../five-leaves/README.md) leave precisely the possibilities (s,t) = (10,4), (10,5), (11,8). A universal vertex is already covered by the previous spider theorem.

Normalize the matched pairs by increasing both endpoint words in the scalar host, preserving each diagonal edge. This can delete cross edges. For each possible normalized set, the checker tries the original graph on those endpoints. At size ten, a four-contact normalized matching can also give a **five-contact original matching**. Every oriented placement of that extra edge is tried. At size eleven there are already eight normalized contacts.

For each matched endpoint try all subwords of its normalized word. Discard a subword if it already creates a forbidden edge against an opposite normalized endpoint. Identify subwords only by equality of their full host neighborhoods. Keep joint assignments with exactly the required matched-endpoint graph. Contract the matching. Each uncovered vertex has at least two matched neighbors, which must lie in distinct current components. Try host word types on both shores, disallow adjacency between uncovered vertices and require that the last addition leaves one component. These tests give connected induced trees. Conversely, taking the chosen matching and original word types of any candidate exhibits a branch of this enumeration.

| Host | Normalized matching sets | Distinct unlabelled trees |
| --- | ---: | ---: |
| 1 | 41 | 582 |
| 2 | 0 | 0 |
| 3 | 17 | 1,316 |
| 4 | 213 | 2,855 |
| 5 | 68 | 2,309 |

Across the five hosts there are **3,155** shapes, allowing exchange of the shores. **1,840** occur only when a contact is restored. The checker computes tree isomorphism keys at the center, compares the full set with the certificate keys, checks reduction and tests every adjacency against an explicit five-intersection formula.

## All smaller orders

Enumerate *all* reduced unlabelled trees on 23 vertices by their unique centroid. Its incident branches have at most eleven vertices each. A planted branch consists of an unordered multiset of smaller branches under a new root. At each vertex at most one child is a leaf. This enforces twin reduction throughout because a parent with children is not a leaf in this centroid orientation. Integer partitions enumerate branch orders and unordered combinations enumerate equal-sized branches. The result is **528,196** trees.

As an independent count, delete all leaves to obtain the core, marking each core vertex carrying a private leaf. Every degree-one core vertex must be marked. With x counting original vertices, let A be the series of planted nonempty cores and M its multiset series. Then A = x² + (x + x²)(M − 1). Rooting the whole core at a vertex gives R = x²A + (x + x²)(M − 1 − A) for cores with at least two vertices. Subtracting directed-edge-rooted cores and adding edge-rooted cores gives R − (A(x)² − A(x²))/2. This follows by rooting each tree at its center and pairing every noncentral vertex or edge root with the first incidence toward the center. Its degree-23 coefficient agrees with the enumeration.

* **525,605** cases have six-bit row words. For each bit form the union of the column neighborhoods of rows carrying it. A cell is an edge exactly when its column belongs to every such union for the bits in its row word. Each bit gives one free union of row and column stars. Intersecting the six costs five. The checker reconstructs every row exactly.
* The other **2,591** have a specified matching. The checker verifies its edges and reconstructs all directed cross edges. Normalization preserves the diagonal and can only delete cross edges. No spanning directed subforest of the proposed pattern occurs among the interior normalized pair types in any exceptional host. This excludes a counterexample on that tree. It leaves the unconditional formula cost of those cases undetermined.

For the descent, mark as exceptional every tree lacking a constructed five-gate formula. A tree inherits such a formula if **any** reduced one-vertex extension has one. An exceptional tree of the next smaller order must therefore be a reduced leaf deletion of a previously exceptional tree: extending a terminal leaf by one edge always gives a reduced extension. Enumerate these deletions and test *all* possible reduced leaf additions, canonicalizing at the tree center. Matching exclusions alone never pass downward.

| Order | Trees still needing individual evidence | Evidence |
| ---: | ---: | --- |
| 22 | 138 | 137 forbidden matchings and one explicit nested formula |
| 21 | 9 | 9 forbidden matchings |
| 20 | 0 | Every reduced tree has an extension with a five-intersection formula |

For the nested formula split seven coordinates into blocks of four and three. A cell is included if its row and column have disjoint supports on **either** block. The two terms cost three and two intersections. Their union is free. This witness is necessary for this particular certificate set. Other formula shapes might also work for this tree. Extending a leaf repeatedly also gives the unconditional conclusion at smaller orders. The one- and two-vertex cases are immediate.

The negative evidence uses 2,649 ordered patterns, or 1,818 up to pair relabelling. The default verifier enumerates all directed forests on normalized pair types and tests possible cross-edge deletions. Its independent alternative assigns each matched pair directly to a distinct pair type, preserving every absent cross edge. Both use the pinned scalar hosts. Search heuristics were used to find positive witnesses and choose matchings. Every conclusion uses a checked witness or an exhaustive exclusion.

## Replay

Use Python 3.10 or later and a C++17 compiler. From this directory:

```sh
c++ -std=c++17 -O3 -Wall -Wextra -pedantic catalogue.cpp -o /tmp/tree-catalogue
c++ -std=c++17 -O3 -Wall -Wextra -pedantic order24.cpp -o /tmp/tree-order24
python3 -I -B replay.py /tmp/tree-catalogue
python3 -I -B replay24.py /tmp/tree-order24
```

An alternative check of the matching exclusions uses the earlier full-domain backtracking program:

```sh
c++ -std=c++17 -O3 -Wall -Wextra -pedantic ../spiders/matching_check.cpp -o /tmp/tree-matching
python3 -I -B replay.py /tmp/tree-matching --direct
```

In `order23.bin.gz` records follow centroid enumeration order. A zero tag precedes one six-bit word per row. A positive tag is the number of matching cells that follow, encoded in row-major order. The checker rejects missing or trailing bytes. The other two certificate files are JSON keyed by centered tree codes. Earlier reductions have their own replays in the linked directories.

Pjscruggs developed the star-intersection atlas. The [sharing discussion](https://github.com/open-goat/pequalnp-proofs/discussions/23239) records the three-gate forms with ChatGPT Pro and the forest question. The new contribution is the five-intersection formula bound for all connected trees with four-intersection circuits, the order-24 classification and the unconditional order-20 bound. The underlying graph-from-stars model was studied by [Pudlák, Rödl and Savický](https://users.math.cas.cz/~pudlak/graph-complexity.pdf) and [Jukna](https://doi.org/10.1017/S0963548306007620). This is a written proof with finite executable certificates. The [forest theorem](../forest-bound/README.md) extends the implication to disconnected forests. A [vertex-critical 10×10 tree](../forest-sharpness/README.md) attains the five-intersection bound. Lean formalization remains open. Historical priority has not been established.
