# Can four intersections save two gates on a tree?

Every finite bipartite graph computable with four binary intersections and free unions of row and column stars has a formula with at most six intersections. If a tree actually needs six, a smaller tree with the same gap occurs as an induced subgraph of one of the five graphs below. It needs at most **56 vertices on either side**. The same five graphs cover witnesses of every size. The subsequent [forest theorem](https://github.com/sarveshkapre/pequalnp-proofs/tree/four-gate-sharing/notes/star-intersection-atlas/four-gate-sharing/forest-bound) rules this out for every tree and disconnected forest.

The five graphs come from an exact calculation in a related model. With eight independent Boolean inputs, free AND, and binary OR charged per occurrence, five functions from the four-gate enumeration require six OR occurrences as formulas, up to permutations of the inputs. These are five different symbolic functions. A graph formula can choose arbitrary new row and column sets. Accordingly, six is an upper bound in the graph model and an attained maximum in the symbolic model. We give five concrete tree restrictions for which new rectangles bring the formula cost back down to at most five.

## Why four gates give a finite calculation

Work with the zero cells. A free union of input stars has a rectangular complement. Meets of zero sets are free and binary joins cost one. Number the paid gates in topological order. The inputs to gate i have the form

    (one raw rectangle) ∩ (the meet of any subset of earlier paid outputs).

This follows by traversing each free meet and accumulating its raw factors into one rectangle. Empty meets give the full rectangle. A gate may occur on both arms and its output may be used again arbitrarily many times. There is one further raw factor at the output, where any subset of paid outputs may be tapped. Keep this factor as a free final meet for the upper bound. Remove unused gates and swap the two arms as needed, relabeling their fresh inputs. A circuit with fewer than four paid gates can be padded by joining two identical copies of its output, keeping the final raw factor outside throughout. For a zero-cost output use the raw rectangle directly.

Treat the two fresh rectangles per gate as independent scalar letters a through h. Any symbolic identity is valid at each graph cell. The certificate provides a formula in the letters for each of 7,037 live wirings. The checker enumerates the ordered arms and output taps independently and checks all 256 truth assignments for every identity. Exactly 6,997 have a supplied formula costing at most five. The remaining 40 have cost-six witnesses and explicit renamings to the five representatives. These counts are counts of syntactic wirings after the stated normalization.

In the table an entry (u,v) gives the earlier-gate masks on the two arms. Bit 0 selects the first gate. All five representatives tap gates 3 and 4 and take their free meet.

| Class | Four pairs of arm masks | Wirings | Host order on each side | Inclusion chains | Reduced tree bound per side |
| --- | --- | ---: | ---: | ---: | ---: |
| 1 | (0,0) (0,0) (0,3) (1,2) | 10 | 70 | 26 | 52 |
| 2 | (0,0) (0,0) (1,2) (1,2) | 5 | 70 | 26 | 52 |
| 3 | (0,0) (0,1) (0,2) (0,3) | 10 | 70 | 26 | 52 |
| 4 | (0,0) (0,1) (0,3) (1,2) | 10 | 74 | 28 | 56 |
| 5 | (0,0) (0,1) (1,2) (1,2) | 5 | 74 | 28 | 56 |

## Exact symbolic lower bound

For each representative collect its minimal true inputs and maximal false inputs under bitwise inclusion. Monotonicity makes this boundary sufficient. For subsets P of the true inputs and Q of the false inputs, let D(P,Q) be the least number of binary OR occurrences in a monotone formula accepting P and rejecting Q. A zero-cost formula exists exactly when the conjunction of all bits common to P rejects every member of Q. Empty constraints have cost zero.

Otherwise minimize over all nonempty proper bipartitions of either side. Splitting Q into two sets costs the sum of their two subproblem costs with the full P, because AND is free. Splitting P costs one plus the two subproblem costs with the full Q, because OR is paid. For completeness, inspect the root of a smallest formula, breaking cost ties by taking the fewest nodes. At an OR assign each positive input to a child accepting it. Both children reject all of Q. If a child alone suffices, it replaces the root. The AND case uses a rejecting child for each negative input. Conversely each split builds a separator. This proves the recurrence in both directions. It is the monotone formula/protocol correspondence with asymmetric gate costs. The five full instances have 12 or 13 minimal true points and six or seven maximal false points. Exhaustion gives six on all five. Their distinct variable-frequency histograms on minimal true inputs certify inequivalence under renaming.

## Turning the five functions into five graphs

For each representative f, use the 256 eight-bit words as both row and column labels. Put an edge at (r,c) exactly when f(r AND c) is false, where AND is bitwise. At a cell, bit i of this word records membership in the ith rectangle. Conversely, all choices of rectangles arise by assigning words to vertices. A clipped-off row or column at the final free meet uses word zero, since f(0) is false. Thus a graph produced by that wiring is obtained by selecting row and column types and possibly duplicating them. Equal full neighborhoods may be represented by a single type in the host. The host is symmetric, and the checker gives the orders above.

Taking an induced subgraph preserves an upper bound on either cost by restricting every input star. Removing a twin (another vertex on the same side with identical neighbors) preserves both costs exactly, because any construction lifts by copying the representative's memberships back. This also proves that the representatives may be chosen simultaneously on both sides. The twin-reduced graph of a nontrivial tree is still a tree. Selecting representatives gives an induced subgraph, and projecting each path to representatives preserves connectivity.

For each host, the checker partitions its row types into the displayed number of chains ordered by inclusion of their full neighborhoods. Restricting columns preserves this order. Two selected row vertices of degree at least two cannot belong to one chain, since their two common neighbors would make a four-cycle. The same holds for columns by symmetry. In a twin-reduced tree with more than two vertices, each row leaf has a distinct neighboring internal column. This bounds each side by twice the chain count. The single edge satisfies the bound directly. The earlier three-gate classification rules out a two-gate saving at smaller circuit budgets. Hence the tree question at budget four is equivalent to finding an induced tree in these hosts with no five-intersection formula.

## Replay and controls

From this directory, using Python 3.10+ and a C++17 compiler (Clang or GCC), run

```sh
python3 -I -B check.py
c++ -O3 -std=c++17 exact.cpp -o /tmp/four-join-exact
python3 -I -B check.py --boundary | /tmp/four-join-exact
```

The Python replay checks the wiring certificates, five inclusion-chain partitions and all cells of five connected acyclic examples. Their dimensions are 10×9, 11×10, 10×9, 9×9 and 9×9. Each entry in `trees.json` contains the row/column labels for the four-gate circuit and nine rectangle masks for a five-gate formula. The largest has 20 edges. These are constructive upper-bound controls. They do not exhaust the induced trees or establish their minimum costs. In `witnesses.txt`, the first eight integers are arm masks, followed by output taps, class (-1 for an upper bound of five), a representative-to-instance variable permutation when needed, and the formula. Parentheses mean free meet, brackets mean paid join. The exact C++ replay calculates the minimum from the truth-function boundary independently of the supplied upper-bound formulas. Verification here is executable finite enumeration plus the written reductions; no Lean verdict is claimed.

pjscruggs developed the star-intersection atlas and two-gate classification. The [8×8 sharing discussion](https://github.com/open-goat/pequalnp-proofs/discussions/23239) records the three-gate forms developed with ChatGPT Pro. The [verified tree](https://github.com/open-goat/pequalnp-proofs/discussions/23239#discussioncomment-19914235) motivates the two-gate-saving question. For graph complexity see [Pudlák, Rödl and Savický](https://users.math.cas.cz/~pudlak/graph-complexity.pdf). The boundary recurrence uses [Karchmer and Wigderson's monotone formula/protocol correspondence](https://www.math.ias.edu/~avi/PUBLICATIONS/MYPAPERS/KW90/KW90.pdf). The four-gate classification, its five explicit graph hosts and the tree-size reduction are the contributions of this note. Literature priority for these exact parameters is unestablished.
