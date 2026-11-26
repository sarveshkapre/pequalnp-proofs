# A tree with circuit cost four and formula cost five

There is a bipartite tree on ten rows and ten columns whose minimum intersection counts are **four for circuits and five for formulas**. Every proper induced subgraph has a formula using at most four intersections. Together with the [four-gate forest theorem](../forest-bound/README.md), this determines the worst possible formula cost of a forest with circuit cost at most four. The witness is minimal under induced restriction. The smallest possible order among all witnesses is unknown here.

We start with the row and column stars of a bipartite graph on a fixed grid. Unions are free. Each binary intersection costs one. An intermediate result can feed several later gates in a circuit. A formula charges separately for each occurrence.

## The tree and the constructions

Number both shores from zero. The ten rows' column neighborhoods, in order, are

    {0,8}  {1,9}  {2,4,6,8}  {3}  {4}  {5,6}  {7,9}  {7}  {1,6}  {1,3}.

The graph is connected and has 19 edges. It has six leaves and three branching vertices. In the path between the outer branching vertices, the degree-four vertex r2 is adjacent to c6, which is at distance two from c1. The pendant paths at r2 have lengths 1, 2 and 3, the one at c6 has length 2, and those at c1 have lengths 3 and 5.

An arbitrary free union of stars is the complement of a rectangle. For each rectangle give every vertex a bit indicating membership in its row or column factor. The rectangle contains a cell exactly when both bits are set. In the following construction A through H denote the eight free unions, in order from the low bit of the circuit words in [witness.json](witness.json). Their zero sets are the eight rectangles. Use

    P = A ∩ B
    Q = C ∩ (D ∪ P)
    S = E ∩ (F ∪ P ∪ Q)
    T = (G ∪ P) ∩ (H ∪ Q)
    output = S ∪ T.

This is the fourth wiring in the earlier five-host classification. The six-bit words in the same file give a formula with five intersections. Intersect six free unions, one for each bit. A cell belongs to the result exactly when the row and column words are disjoint. Both constructions reproduce all 100 entries. The file also gives the shape and rectangle words of a four-intersection formula for each of the twenty possible vertex deletions. Each is checked against its own 90 cells. Restricting the labels further proves the claim for every proper induced subgraph.

## Exhausting four-intersection formulas

Take complements in the whole grid. The leaves are now arbitrary rectangles, intersection is free, and a binary union costs one. A cost-zero formula is a rectangle. A raw rectangle intersected with any formula can be pushed into every leaf by distributivity, preserving the paid operations. This uses closure of rectangles under intersection. Thus in a shape of positive cost k, a union at the root splits k−1 between its children. A free intersection at the root splits k into two strictly positive costs after raw rectangle factors have been absorbed. Conversely, each such split builds a permitted formula. Starting from one rectangle, this recurrence generates all shapes, up to sorting and flattening adjacent nodes of the same operation. Replacing a leaf R by R ∪ R pads any smaller budget to exactly four. The resulting list has nine shapes, including the nested ones.

For each shape give its s leaf occurrences distinct coordinates. Its Boolean function f acts on a cell by evaluating f(x & y), with x and y the vertex words and & bitwise AND. The original graph has an edge exactly when this value is false. Conversely every assignment of words defines rectangle labels for the shape. This produces a finite symmetric bipartite host on all s-bit words. Full neighborhoods identify interchangeable types. Constant types can be discarded since every target vertex has both a neighbor and a nonneighbor. The target's row neighborhoods are pairwise distinct, and so are its column neighborhoods. Consequently a representation must use distinct host types on each shore.

The checker assigns target rows to distinct host row types. The assignments made so far partition target columns by their responses to those rows. Host columns are partitioned in the same way. Each target group needs at least as many host columns with its response pattern as the size of the group. A new row splits every group into neighbors and nonneighbors. The search tries every unused row type consistent with both capacities. At a full row assignment the surviving groups have disjoint domains of adequate size, so an injection of all columns exists. These tests are necessary at every stage and sufficient at the leaves. The choice to branch on the row with the fewest possible types only changes search order.

All nine hosts reject the tree. As a positive control, the same search embeds the four-edge matching into each of them. The separate [SAT encoding](sat.py) lists the nine scalar functions by hand. For each edge it forbids every minimal true set in the joint row and column bits. For each nonedge it requires a joint bit outside every maximal false set. Monotonicity makes these constraints exact. Joint-bit witnesses can be chosen equal to the actual conjunctions. Adjacent coordinates with identical roles can be sorted by their row words. CaDiCaL 2.1.2 returned UNSAT on all nine formulas. The standalone enumeration below establishes the lower bound without relying on a SAT verdict.

## Exhausting three-intersection circuits

A gate has two arms. Each arm is a free union of stars and any subset of earlier gate outputs. Flattening free unions gives this description even when an earlier value is used many times. The final output is a union of selected gates and raw stars. Every star contains a full row or column, and this tree has none, so its final raw union must be empty. For three ordered gates the first gate has no possible earlier taps, the second has two choices per arm, and the third four per arm. There are eight output subsets. This yields 1 × 2² × 4² × 8 = 512 cases, including unused gates so smaller budgets are covered. Six rectangle coordinates suffice for each case. The replay computes every scalar truth table and groups only tables that agree on all 64 words. The resulting 36 distinct tables all fail to represent the tree. This gives its circuit lower bound independently of the earlier three-gate unfolding result.

## Replay, credit and scope

From this directory with Python 3.10+ and a C++17 compiler, run

```sh
c++ -O3 -std=c++17 -Wall -Wextra -pedantic profile.cpp -o /tmp/tree-profile-check
python3 -I -B replay.py /tmp/tree-profile-check
```

For the optional independent SAT check, run `python3 -I -B sat.py 0 > /tmp/tree-form.cnf` and `cadical /tmp/tree-form.cnf`. Repeat for shape numbers 1 through 8. Each UNSAT result has solver exit code 20.

Pjscruggs developed the star-intersection atlas. The [sharing discussion](https://github.com/open-goat/pequalnp-proofs/discussions/23239) records the earlier three-gate work with ChatGPT Pro and the forest question. The earlier four-gate forest proof supplied the candidate hosts and the universal upper bound. This note adds the explicit tree attaining that bound, its deletion certificates, and a direct exclusion of every smaller circuit and formula. The graph-from-stars framework appears in [Pudlák, Rödl and Savický](https://users.math.cas.cz/~pudlak/graph-complexity.pdf). Verification consists of a written reduction and an exhaustive executable proof. Lean formalization and literature priority for this exact witness are open. Whether a forest can save two formula intersections at a larger circuit budget remains a separate question.
