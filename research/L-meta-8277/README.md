# Two layouts for the 28-gate grid

[Amritpal’s request](https://github.com/open-goat/pequalnp-proofs/discussions/21642#discussioncomment-19905319) specifies six points, eleven lines, and thirteen line ORs that are already available. The grid must accept 24 point–line pairs and reject 153 maximal negative inputs. The target is 28 gates. [Original Lean statement](../../lean/PEqualNP/Outside/R_meta_4893_629.lean)

| Layout | Required pairs accepted | Maximal negatives rejected |
| --- | ---: | ---: |
| [28 gates](grid28.txt) | 21/24 | 153/153 |
| [29 gates](grid29.txt) | 24/24 | 153/153 |

In the 28-gate layout, the missed pairs are (point 2, line 9), (point 2, line 10), and (point 3, line 5). Both indices start at zero. As bit masks, the inputs are `(4, 512)`, `(4, 1024)`, and `(8, 32)`.

Wire 43 is an AND that turns on for the forbidden pair (point 3, line 0). Wire 50 blocks that signal before it reaches the output. The same AND helps accept (point 2, line 0). Forcing wire 43 off makes the layout miss that required pair too. The 29-gate reference builds each point’s four-line OR, ANDs it with that point, then ORs the six results.

Each line in the gate lists gives the operation and its two input wire numbers. The first gate writes wire 30. The last wire is the output.

## Replay

From the repository root, run the following with Python 3.10 or later. It takes only the standard library.

```sh
python3 research/L-meta-8277/replay.py
```

[GridMixed.lean](GridMixed.lean) checks the shape, the exact three missed pairs, and rejection of every disjoint input for the 28-gate layout. It also checks the trace on (point 3, line 0). The experiment forcing wire 43 off is in the Python replay. [GridReplay.lean](GridReplay.lean) checks the 29-gate reference and a simpler 28-gate layout that omits one required pair.

With Lean 4.36.0 and the dependencies pinned in this checkout, run these from the repository root.

```sh
cd lean
lake build +PEqualNP.Defs
lake env lean ../research/L-meta-8277/GridMixed.lean
lake env lean ../research/L-meta-8277/GridReplay.lean
```
