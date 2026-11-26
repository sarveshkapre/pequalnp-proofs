# Four intersections on a forest

**Theorem.** Every finite bipartite forest that has a circuit with at most four binary intersections has a formula with at most five. Unions of row and column stars are free. The circuit may reuse an earlier gate, and the formula pays for each occurrence. The theorem includes disconnected forests, isolated rows and columns, and repeated neighborhoods.

**A second conclusion holds without a circuit assumption.** If at least two components contain an edge, five formula intersections suffice whenever at most 22 vertices remain after deleting isolates and duplicate leaves. The count is total across both shores. The proof below preserves the bipartition of the whole forest.

## Reusing the connected case

Restricting a formula to selected rows and columns restricts its graph. A deleted twin can be restored by copying its representative's memberships in the free unions. When every remaining vertex has a nonneighbor, isolated vertices can also be restored. Give each new vertex zero membership in every raw union. At a new-row/old-column cell its input vector is coordinatewise below some old nonedge in that column. Monotonicity gives zero. The same argument works for a new column, and a new-row/new-column cell has all memberships zero. Having two edge-bearing components supplies the needed nonneighbors automatically.

First assume the forest has at least two edge-bearing components, no isolates, and no two leaves at the same neighbor. Add one new column joined to exactly one row of each component. This gives a reduced tree. The new column has degree at least two and no existing vertex becomes a leaf. We can equally use a new row. If **any** such extension has a five-intersection formula, the original forest inherits it by restriction. No assumption on the circuit cost of the extension is needed.

The [connected-tree certificates](../tree-bound/README.md) already construct formulas for every tree up to order 20 and for all but specified sets at orders 21, 22 and 23. Only the trees outside their positive certificate sets can have a forest restriction missed by this argument. Delete each eligible nonleaf of those trees, keeping reduced, isolate-free restrictions. Enumerate every connector choice on both shores for each resulting forest. The two shores can be swapped globally. Swapping just one component can change the answer and is never used to identify forests.

| Forest vertices | Supertrees outside the positive set | Distinct restrictions tested | Forests without a certified extension |
| ---: | ---: | ---: | ---: |
| 20 | 9 | 31 | 0 |
| 21 | 137 | 444 | 0 |
| 22 | 2,591 | 8,135 | 2 |

Both remaining forests have explicit seven-bit labels. A row and a column form an edge if their labels are disjoint on the first five coordinates **or** disjoint on the last two. These terms cost four and one intersections, respectively, and their union is free. The replay checks all cells of both 11-by-11 matrices. An independent forward audit deletes every eligible nonleaf of every reduced tree at each of the three orders, including the trees with positive certificates. Using component centroids to identify restrictions, it recovers all 20,365, 45,393 and 103,261 distinct reduced, isolate-free disconnected forests at orders 20, 21 and 22, respectively. Its only two uncovered keys are the ones with the explicit seven-bit formulas.

## Bounding and covering every larger forest

The [four-gate reduction](https://github.com/sarveshkapre/pequalnp-proofs/tree/637ca77a6c4c7d9ca1abbdb80ea02416134f4005/notes/star-intersection-atlas/four-gate-sharing) supplies five explicit exceptional hosts. Any graph with circuit cost at most four and formula cost above five must be an induced restriction of one of these hosts after identifying twins. In a reduced forest with no isolates and at least two edge-bearing components all vertices have distinct neighborhoods on their shore. Two nonleaf twins would create a four-cycle.

Let c be the number of components, s the size of a maximum matching covering all leaves, t the number of other edges between matched endpoints, and u the number of uncovered vertices. Such a matching exists. Among maximum matchings choose one covering the most leaves. The neighbor of an uncovered leaf must be matched, and exchanging its matching edge for the leaf edge gains a covered leaf because there are no twin leaves. A component consisting of a single edge is matched. The uncovered vertices are independent and each has degree at least two. Counting their incident edges gives 2u ≤ (2s+u−c)−(s+t), hence n ≤ 3s−c−t.

In the exceptional hosts s ≤ 11. For s = 9, 10, 11 respectively, normalizing the matched pairs gives at least 3, 4, 8 cross edges. Normalization can only delete cross edges. For s ≤ 8 the order bound is at most 24−c. Thus n ≤ 26−c. For n ≥ 23 only the three rows below remain.

| Vertices | Components | Distinct shapes | Counts in hosts 1 through 5 |
| ---: | ---: | ---: | --- |
| 23 | 2 | 1,644 | 441, 0, 695, 1,552, 1,295 |
| 23 | 3 | 83 | 31, 0, 42, 81, 79 |
| 24 | 2 | 237 | 63, 0, 122, 221, 217 |

When n+c=26 only (s,t)=(10,4) is possible. When n+c=25 the possibilities are (10,4), (10,5), and (11,8). Start from all normalized matching seeds from the [earlier census](../tree-bound/replay24.py). Lift each endpoint to every eligible subword of its normalized word, identifying only types with equal full host neighborhoods. A prescribed cross edge can be present before normalization and absent afterwards. The checker tries every placement of the one extra contact when the counts allow it. At order 23 with two components, 960 shapes occur only when that contact is restored.

Choose the u uncovered host vertices on their actual shores. They must be mutually nonadjacent and have at least two neighbors among the matched endpoints. They necessarily have distinct types on each shore because equal neighborhoods of degree at least two create a four-cycle. The first enumeration contracts each matched edge and rejects a new vertex that joins a component to itself. The second enumeration uses the same endpoint lifts but selects uncovered types by edge count. It accepts a completed graph with n−c edges exactly when traversal finds c components. The two enumerations agree on every host's shape set and on its raw completion count. For each shape in each host the audit also emits an actual host labeling. Python checks the original scalar gate definitions on all its cells and reconstructs the same colored forest.

All 1,964 shapes have explicit six-bit row labels. For bit b take the free union of the rows without b and the columns neighboring at least one row carrying b. The intersection of these six unions costs five. The replay checks its value against every cell.

## A single edge-bearing component and isolates

The empty graph is a free union. If there is just one edge-bearing component, restrict its circuit and apply the connected-tree theorem. This handles the original graph directly when there are no isolates. If the component has no universal vertex on either shore, restore any isolates by the monotonicity argument above.

Suppose the component has a universal row. Every other row has degree one, since two neighbors would form a four-cycle with the universal row. After removing twins there are therefore l private row–column pairs and at most one further column incident only to the universal row. The private pairs constitute an induced matching. If l ≥ 9, restrict to nine pairs. Each of their endpoints has a nonneighbor among the other endpoints. A normalized induced nine-edge matching inside any of the five exceptional hosts would have zero cross edges, contradicting the minimum of three. Hence a putative counterexample inside a host has l ≤ 8.

Assign the private rows distinct two-element subsets of five coordinates. Give each matched column its row's five-coordinate complement, and the possible extra column all five coordinates. Give the universal row just a sixth coordinate and every isolate on either shore all six. An edge is exactly a disjoint pair of labels. A private row is disjoint from its matched column, while every other two-element subset intersects that column's complement. The universal row sees every component column, and all labels on the old graph are nonempty. These six coordinates give a five-intersection formula, including all isolates. Transposition covers a universal column. This finishes the theorem.

## Replay and credit

Python 3.10+ and a C++17 compiler suffice. Run these commands from this directory. The earlier connected theorem and matching bounds have their own replays at the linked revisions.

```sh
c++ -O3 -std=c++17 -Wall -Wextra -pedantic ../tree-bound/order24.cpp -o /tmp/forest-boundary
python3 -I -B replay.py /tmp/forest-boundary --audit
c++ -O3 -std=c++17 -Wall -Wextra -pedantic audit_small.cpp -o /tmp/forest-restrictions
python3 -I -B audit_small.py /tmp/forest-restrictions
```

Pjscruggs developed the star-intersection atlas. The [sharing thread](https://github.com/open-goat/pequalnp-proofs/discussions/23239) records the earlier three-gate classification with ChatGPT Pro and the forest question. This proof adds the passage from connected trees to arbitrary forests at circuit budget four and the unconditional disconnected order-22 bound. The broader graph-from-stars framework goes back to [Pudlák, Rödl and Savický](https://users.math.cas.cz/~pudlak/graph-complexity.pdf). The results have written proofs and finite executable certificates. A [vertex-critical tree](../forest-sharpness/README.md) attains circuit cost four and formula cost five. Lean formalization and historical priority remain open.
