# Three rows need nine line gates when each has its own point guard

Keep three of the six rows ordinary. For each of the other three, accept its point when a line signal for the row is on. Allow those three line signals to share any binary AND or OR gates. They still need **nine line gates**, whichever three rows you choose. Making the three row signals separately takes exactly nine OR gates. That circuit passes all 177 tests.

This rules out saving one gate by rearranging the line computation for any three ordinary rows. The full 28-gate question remains open. A circuit that combines points and lines before the three row signals are ready can fall outside this result.

## Why the search covers this class

1. Turn on exactly one of the three points and one line. With separate point guards, the output must equal that point’s line signal. The four incident lines must each give 1. Every other singleton line gives a legal negative and must give 0. A monotone circuit that passes the maximal negative tests also rejects their subsets.
2. Keep only lines appearing in at least one target row. Represent a wire by the set of kept singletons on which it turns on. AND becomes set intersection and OR becomes union on these inputs. Every raw line, every supplied line wire and every OR of any subset of one of the three unchanged rows meets each target in at most one singleton.
3. As an extra allowance, make **every** set with that last property available for free. This includes all the actual free wires, even if an unchanged row’s OR tree is rearranged. The resulting problem depends only on the overlaps between the three target rows. Two triples have a line shared by all three rows. The other eighteen have three distinct pairwise intersections. After relabeling the singletons there are exactly two formulas.
4. The search includes eight shared binary gates with arbitrary fanout and repeated operands. Each target chooses an output gate. Put the smaller operand first. Repeatedly choose a ready gate whose larger operand has smallest index. A newly ready gate uses the latest gate, so the selected larger operand indices are nondecreasing. This gives the order used in the search for every possible network. An output needs at least three gates because each free signal covers at most one of its four required singletons, and two gates can involve at most three distinct leaves in one output’s dependency graph. After removing unused gates, the last gate is an output. Shorter circuits can repeat that output as both inputs to an OR gate to pad to eight.
5. Both formulas are unsatisfiable. Lean 4.36.0’s standard-library LRAT checker replayed both certificates. The translation above is a mathematical and code argument. There is no Lean theorem here identifying the generated formulas with the unrestricted grid statement.

| Shape | Triples | Singletons | Free wires | CNF clauses | LRAT actions |
| --- | ---: | ---: | ---: | ---: | ---: |
| Common intersection | 2 | 10 | 65 | 24,340 | 391,529 |
| Three pairwise intersections | 18 | 9 | 36 | 13,203 | 166,873 |

## Replay

From the workspace root, with Python 3.10+ and the project's Lean 4.36.0 toolchain installed, run:

```sh
out=$(mktemp -d)
toolchain="$HOME/.elan/toolchains/leanprover--lean4---v4.36.0/bin"
python3 work/grid/repair_three/line/check_triples.py
python3 work/grid/repair_three/line/triple_line.py 012 8 "$out/concurrent" --helpers universal --proof --seconds 180
python3 work/grid/repair_three/line/triple_line.py 013 8 "$out/triangle" --helpers universal --proof --seconds 180
"$toolchain/lean" --run work/grid/bounds/CheckCover.lean "$out/concurrent.cnf" "$out/concurrent.lrat"
"$toolchain/lean" --run work/grid/bounds/CheckCover.lean "$out/triangle.cnf" "$out/triangle.lrat"
```

The check for all 20 triples rebuilds each formula and compares its SHA-256 with one of the following. It also verifies the 29-gate ordinary circuit on the full test set.

| Shape | CNF SHA-256 | Locally checked LRAT SHA-256 |
| --- | --- | --- |
| Common intersection | `3d412f81d9c6bd1786902d0f2417017e1256a0ab24d10ee018859e1287ce3dff` | `b8394007c76eb5c34ec07d95c92a34266e23c65ef54fceb45d842319abcf9400` |
| Three pairwise intersections | `eed3a00fe4dc8c1541451cadbce2dd73e45ed850248351ea49dc651d70d5b9e1` | `34f83ea1e44c0025588f23ea646b34f3ab0ac33736ecd52f91e7ecb831443b02` |
