# Eight mixed gates arranged as a tree

In both shapes the shared block needs more than thirteen gates if its eight mixed gates form a tree. The argument allows any of the twelve point–line positives to be covered anywhere and allows sharing throughout the pure preparation. The tree condition concerns only the mixed part and the wires entering it.

A binary tree with eight gates has nine leaves. The [previous boundary check](../../profiles/README.md) requires at least three pure point wires and five pure line wires among them. There are two possible splits. We treated both.

| Pure point wires | Pure line wires | Mixed truth tables enumerated | Residual common-line classes | Residual triangle classes |
| ---: | ---: | ---: | ---: | ---: |
| 3 | 6 | 67,872 | 7 | 7 |
| 4 | 5 | 470,500 | 146 | 7 |

The table counts different truth tables within each representative set of point singleton values. One circuit can have several descriptions. The last two columns count normalized line preparation problems; Lean replayed a contradiction in every one of them. [Line specifications](../prefix/tree-classes.json) · [Certificate hashes](../prefix/tree-results.json)

## Why the enumeration covers every tree

For a tree, line leaves are all different and each is read once. Label these wires in the order they first occur in a drawing of the tree. A state in the [enumerator](tree.py) records the multiset of point-leaf signatures and the number of line leaves. Each signature is the set of singleton point inputs on which that leaf is true. With no points selected, every pure point wire is false. The three rows must give incomparable point codes by their private lines. We allow all such signatures, including repetitions and the empty signature, and relabel the three rows and the point wires to representatives.

At the root, try every division of the point multiset and line count between its two children. Commutativity permits the two parts to be sorted. The left subtree receives the low-index line variables, and the right subtree receives the high-index line variables. This line naming is permissible because the line wires have no names before we ask how to prepare them. Both AND and OR are tried at every root. Pure internal subtrees would instead be part of the pure preparation. Induction on the number of leaves now gives a representative for every possible mixed tree. Equal truth tables may be merged because all remaining checks use the same four point settings and all binary line codes.

For each resulting table, determine all line codes producing the required outputs at zero points and the three singleton points, for each incident-row pattern. Codes for different lines of the same type can differ. Tables missing a required pattern are discarded. Multiple tables yielding the same requirements share a calculation, with the largest line preparation budget retained.

Eight mixed gates leave five preparation gates. If q gates are necessary for the point wires, only 5−q can prepare the line wires. Each different point signature other than zero or a single point needs a gate, and the all-three signature needs at least two. If the three incident-line masks can be reconstructed from the cut line wires in 3+q gates, then the three complete masks would take at most eight gates. The [certified lower bound](../../../line/README.md) is nine. Each successful reconstruction is one shared circuit for all allowed codes, checked by evaluating it on each code.

The cases without such a reconstruction are given to a SAT search for 5−q line gates, allowing arbitrary sharing, either operation, and a larger bank of line masks than the physical circuit. The 3-point/6-line split supplied 60 specifications before relabeling, and the 4-point/5-line split supplied 567. The [normalizer and solver](../prefix/solve.py) quotient permutations of the line wires and of the three rows. Contradictions on the resulting 167 classes exclude every tree in the original search.

## Controls and replay

The enumeration was checked at nine smaller input sets by expanding all line name permutations and comparing the resulting sets, table for table, against a separate enumerator that starts with fully labeled leaves. Forty larger physical circuits exercise both nine-leaf splits on all 20 row triples. They have eight live mixed gates arranged as a tree and twenty gates in their shared block. Each passes all 177 physical tests. The cut function of each appears in the enumerated set and meets the relevant line-type requirements. Some extra operands in these larger controls are redundant on grid inputs.

From the workspace root:

```sh
src=work/grid/repair_three/shared13/eight
out=$(mktemp -d)
python3 -B "$src/tree/check_tree.py"
python3 -B "$src/tree/tree.py" 3 "$out/three.json"
python3 -B "$src/tree/tree.py" 4 "$out/four.json"
python3 -B "$src/prefix/solve.py" tree-replay "$out/three.json" "$out/four.json" --cache "$out"
```

The solver writes regenerated class and result ledgers next to its source and rejects an existing label. The two raw specifications have SHA-256 hashes `e544ac004ebbc66e1bbbdd1971321718995f3d18e63e17c20fb6b32140a094b2` and `b745eb56741c4e148370dac8c5b4f5ce8e0de6321e3b93710890e800acb71912`. The physical-to-circuit reduction and the enumeration use written mathematics and Python; the individual SAT contradictions use Lean’s LRAT checker.
