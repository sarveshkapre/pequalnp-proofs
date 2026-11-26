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

## Which internal gates must turn on?

[Amritpal’s wire-43 edit](https://github.com/open-goat/pequalnp-proofs/discussions/21642#discussioncomment-19907634) recovers two required pairs. Only point 3 with line 5 is still missing. Every AND on a path to the output stays off on all 112 forbidden inputs with exactly two bits on.

Any passing 28-gate circuit must behave differently on at least one of those inputs. An AND on a path to the output must turn on for a nonincident point and line, or there must be AND activations on both a two-point input and a two-line input. Different gates may supply these last two activations. A later AND must block the signal on the same input for the final output to be correct. Whether a passing 28-gate circuit exists remains open.

The [checked Lean file](L_meta_8277_side_witness.lean) proves the condition for the grid in the merged reduction and checks the exact wire-43 edit. The main declarations are `GridSideWitness.kinds_required`, `GridSideWitness.fires_is_filtered` and `GridPublishedRepair.clean`. The source SHA-256 is `aba2f86bff6d6a6bdd79f62f22d0f22543907c052e13a243bb169ebfa4e63529`.

From this checkout’s repository root, replay with its pinned Lean 4.36.0 toolchain.

```sh
proof_dir="$(pwd)/research/L-meta-8277"
build_dir=$(mktemp -d)
cd lean
lake build +PEqualNP.Outside.L_meta_6973 +PEqualNP.Outside.L_meta_8029 +PEqualNP.Outside.R_meta_4893_629
lake env lean -R "$proof_dir" -o "$build_dir/L_meta_8277_side_witness.olean" "$proof_dir/L_meta_8277_side_witness.lean"
lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; leanchecker -v L_meta_8277_side_witness' sh "$build_dir"
```
