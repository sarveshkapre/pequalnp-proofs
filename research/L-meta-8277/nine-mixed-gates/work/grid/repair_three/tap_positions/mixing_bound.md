# At least eight gates in a passing 11-gate block must mix points and lines

For one output covering all three selected rows, at least eight of the eleven gates must mix point and line inputs. The first mixed gate therefore comes by gate four. First positions 5 through 11 are excluded for AND and OR in both shapes (28 of 44 position/operation/shape combinations). A wire is mixed if some point input and some line input both reach it through the wiring. Cut the output cone at the pure point and pure line wires that feed mixed gates. Only the mixed gates and these pure input wires remain. A pure input wire may originally be a primary input or a computed signal. Its value is zero when all inputs of its kind are off.

Choose a private line for each row, meaning that among the three rows only its assigned row contains it. All 120 row orders have these three lines. On singleton points and these singleton lines the required output is the three-by-three identity matrix. For two different singleton points, the two vectors of values on the pure point wires entering the cut must be incomparable bit by bit. If one were below the other, monotonicity would put the two corresponding outputs in the same order on every line. The two private lines require opposite orders. The same reasoning applies to the three private lines on the pure line wires.

Two bits cannot encode three incomparable vectors. There must therefore be at least three distinct input wires of each kind entering the mixed cone. For a connected cone with G binary gates and L distinct input wires, counting the two input edges per gate gives L ≤ G + 1. Thus at least five mixed gates are necessary. This is independent of the order of gates or the number of available pure inputs.

## What happens at five

Five mixed gates and six entering wires give equality in the edge count. The cone is a tree, each entering wire is used once, and there are exactly three point wires and three line wires. The only three-element antichains of three-bit vectors are the three unit vectors and the three vectors with two set bits. Renumber the three wires on each side independently so the codes of the chosen singleton points and private lines have the corresponding unit bit, or its complement.

The [finite checker](mixing_bound.py) enumerates all 3,086 different six-input truth tables of AND/OR trees with these labeled leaves used once and every internal gate mixed. It tests all four point/line code choices against the identity matrix, the zero point, and the zero line. For each membership pattern that actually occurs, it tries every three-bit line code and keeps those giving that membership on the three points and zero on the zero point. Every occurring pattern needs at least one possible code.

| Shape | Physical row orders | Normalized tables and code choices that pass |
| --- | ---: | ---: |
| Common line | 12 | 1 |
| Triangle | 108 | 2 |

In every surviving choice the only possible code for any singleton line is its row-membership mask itself. The three entering pure line wires therefore compute the three row masks on all kept singleton lines. The earlier [nine-gate line lower bound](../line/README.md) grants all admissible line masks for free, allows arbitrary sharing and already rules out computing these three signals in eight gates. In the present block at most six gates remain outside the five mixed gates. This proves that at least six gates must be mixed. The authority of the five-gate step is the tree argument and the Python enumeration. Lean replayed the earlier line-bound contradictions.

## What happens at six

After cutting the pure wires, a cone of six mixed gates can have six or seven distinct entering wires. Both sides still need at least three. With seven entering wires the cone is a tree on either three point and four line wires or four point and three line wires. With six it has three of each. Its twelve input edges leave exactly one node that is read twice. The subtree feeding that node is a tree. The part above it is also a tree when its two uses are counted as separate occurrences of the same truth table. This includes primary wires read twice and both copies entering the same gate.

The [six-gate checker](mixing_bound_six.py) enumerates each topology by these two tree constructions. It gives each pure point wire every possible three-bit pattern of singleton values and zero on the empty point input. Row and wire relabeling leave two patterns of assignments to a bank of three point wires, or nine to four, after requiring the three rows to be incomparable. The line side is freer still: a singleton may take any code on its three or four boundary wires that gives the required membership and rejects the zero-point input. Each membership that occurs in the physical shape must have a possible code. The all-zero line code must turn all outputs off. The three target row functions are then specified on the union of all possible codes and the empty input.

| Pure point wires | Pure line wires | Common-line profiles | Triangular profiles |
| ---: | ---: | ---: | ---: |
| 3 | 3 | 12 | 18 |
| 3 | 4 | 228 | 456 |
| 4 | 3 | 90 | 78 |

A profile in this count is a distinct suffix truth table for one representative set of point wires. For **every** remaining profile the checker builds the three row masks together with at most three more line gates from the boundary line wires, then independently replays that wiring on every retained code. The zero line signal is available in the earlier line lower bound. The six mixed gates leave at most five original pure line gates. Adding the three reconstructing gates would give all three complete row masks in at most eight line gates. The checked nine-gate bound excludes this possibility.

Hence the first mixed gate of an eleven-gate block is at position **five or earlier**. This excludes first positions 6 through 11 for both operations and both shapes. The six-gate enumeration and witness replay use Python. The line lower bound uses separate SAT certificates replayed in Lean. Run both small enumerations from the workspace root:

```sh
python3 -B work/grid/repair_three/tap_positions/mixing_bound.py
python3 -B work/grid/repair_three/tap_positions/mixing_bound_six.py
```

## Seven mixed gates

The [seven-gate checker](mixing_bound_seven.py) extends this enumeration to six, seven, or eight distinct pure inputs entering the mixed cone. A connected cone with seven gates and eight leaves is a tree. With fewer leaves some wire feeds multiple gate inputs. Choose such a node with no earlier multiple-use node in its dependency cone. Its inputs and gates form a tree, and none of the nodes strictly below it is used outside that tree. Replace the chosen node with one copy of its value for each of its uses and enumerate the smaller network above. Counting both input pins, replacing a node with k copies reduces the excess of edges over the number needed for a tree by k−1. The original excess is zero, one, or two. Recursing to a tree includes fanout of three, two separate fanouts of two, and fanouts nested inside other fanouts. A duplicated mixed signal carries both of its original source types.

Seven mixed gates leave at most four gates for preparing the pure inputs. If q of those must compute point signals, at most 4−q prepare line signals. Every distinct point-wire signature outside the zero and three raw singleton patterns requires at least one gate. A signature true on all three singleton points needs at least two gates because one binary gate can read at most two point inputs. The checker uses the larger of these two lower bounds as q.

The checker retained 16,956 common-line profiles and 21,390 triangular profiles. For every surviving suffix it constructs **one set of three line outputs** on every line code the physical columns could use. It gives this construction at most 4+q additional line gates, records the gate inputs, then independently replays the same three fixed outputs on every admissible code. Adding back the original line preparation gives at most (4−q)+(4+q)=8 gates for the three row masks. The nine-gate bound rules this out in both shapes.

```sh
python3 -B work/grid/repair_three/tap_positions/mixing_bound_seven.py
```
