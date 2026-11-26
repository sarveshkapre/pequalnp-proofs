# Eight gates must mix point and line information

Keep three ordinary rows, turn their points off for the lower-bound tests, and examine the live part of the block producing the shared output. For **each** of the twelve- and thirteen-gate budgets, at least eight gates must have both a selected-row point input and a line input among their ancestors. At least five distinct line-only wires must enter those mixed gates. The twelve positive pairs can be produced anywhere in the circuit.

The two shapes have either a line shared by all three active rows or three different pairwise intersections. Both bounds apply to all 20 choices of the active rows. The [projection](../../tap_positions/physical_masks.py) checks all 120 ways of ordering them. Pinning the frozen points and unused lines to zero can remove gates; simplify zeros and copies before counting. Doing so cannot add a mixed gate. Every available point-free input on the retained singletons is included by allowing any line mask that meets each row at most once. This also includes the ORs prepared by the three frozen rows, whatever their association.

## Counting the mixed gates

Cut the circuit immediately before its mixed gates. Its inputs are now pure point wires and pure line wires. On the three private lines and their respective points the output must be the identity matrix. The three point inputs give incomparable codes on the point wires, and the three private lines give incomparable codes on the line wires. Each side needs at least three wires. A connected binary circuit with six entering wires needs at least five gates.

With exactly five mixed gates this circuit is a tree; the [five-gate enumeration](../../tap_positions/mixing_bound.md) forces the three entering line wires to equal the complete row masks on the singleton lines. Preparing those three masks costs at least nine gates by the [certified line bound](../../line/README.md). Five plus nine already exceeds thirteen.

At six and seven mixed gates the [suffix enumeration](../../tap_positions/mixing_bound_seven.py) covers trees and shared wires. It enumerates possible truth tables, identifying duplicates for each fixed set of point signals. For each table and each line type, record all line-wire bit patterns that give the required responses on zero points and the three single points. Private lines in the same row can take different patterns. If nothing is allowed for one type, discard the table.

| Mixed gates | Shape | Tables passing these first tests | Pure line problems left at size 12 | Pure line problems left at size 13 |
| ---: | --- | ---: | ---: | ---: |
| 6 | Common line | 330 | 0 | 2 |
| 6 | Triangle | 552 | 0 | 1 |
| 7 | Common line | 16,956 | 4 | 21 |
| 7 | Triangle | 21,390 | 0 | 3 |

These are counts of tables over the cut wires; a table can represent many circuits. For each table, lower-bound the pure point preparation cost by the number of distinct non-primary point signatures, with at least two gates for a signature containing all three points. If this costs at least q and the mixed part has g gates in a block of size K, at most K−g−q line gates can precede it. Whenever we can reconstruct all three row masks from the cut line wires using at most 8−(K−g−q) more gates, we contradict the nine-gate line bound. The reconstruction is one circuit for all allowed line codes. Its wiring is evaluated separately on each code.

For every table left over, permute the three row names and the line-wire names to group identical requirements on the pure line circuit. This grouping is valid because the enlarged input bank and the multiplicities of the physical singleton types are symmetric in the rows. The point signatures impose only their lower bound on preparation cost at this stage. For each class, let each cut line wire choose any free or computed signal. Enforce the recorded code constraints on each physical singleton, with all possible AND/OR circuits within the remaining line budget. Within one row-membership class, physical singleton names are interchangeable. The numeric operand order ties raw inputs. Sorting raw-operand columns and swapping two raw operands admits a lexicographic maximum of the combined symmetry orbit.

All 31 line problems were unsatisfiable. Lean 4.36 replayed every LRAT contradiction. A separate control explicitly constructs a larger line circuit by ORing singletons for one permissible code per line. For all 31 classes, the same encoder returned a model for that planted circuit, and the decoded masks matched the requirements. The reduction from physical circuits and the enumeration of mixed functions use written arguments and Python. [Six-gate counts](six.json) · [Seven-gate counts](seven.json) · [Six-gate certificates](six-prefix.json) · [Seven-gate certificates](seven-prefix.json)

## How many different line wires must reach the mixed part?

Fix one point. If its row contains line A but omits B, at least one entering line wire must be on for A and off for B. Otherwise every mixed gate is monotone in inputs that stay the same or increase when changing A to B, while the required output falls. The zero-line code must also differ from every nonempty retained line code. The following are exact minima for this separation test in the enlarged bank. A passing separation test supplies no circuit for the mixed part.

| Gates available for preparing line signals | Minimum entering line wires, either shape |
| --- | ---: |
| 0 or 1 | 7 |
| 2 | 6 |
| 3, 4 or 5 | 5 |

The [encoder](boundary.py) permits unrestricted taps, tied or copied wires, and arbitrary subsequent monotone decoding in this test. The data include Lean-replayed contradictions below each threshold and decoded source masks meeting it. More gates can always be left unused, and more wires can always repeat an existing tap. [Cases for 0, 3 and 5 preparation gates](boundary.json) · [Cases for 1, 2 and 4](boundary-mid.json) · [Raw-input controls](boundary-raw.json)

Thus an eight-mixed-gate candidate needs at least five pure line wires and three pure point wires entering its mixed part. Eight two-input gates have sixteen input edges. With eight entering wires, exactly one wire among those or the internal wires is used twice. With nine entering wires all uses form a tree. These two forms give a smaller next search with arbitrary coverage of the twelve pairs.

## Replay

From the workspace root, using Python 3.11+ and the Lean 4.36.0 tools installed under elan:

```sh
d=work/grid/repair_three/shared13/profiles
scratch=$(mktemp -d)
python3 -B work/grid/repair_three/tap_positions/mixing_bound.py
python3 -B "$d/profiles.py" 6 "$scratch/six.json"
python3 -B "$d/profiles.py" 7 "$scratch/seven.json"
cmp "$scratch/six.json" "$d/six.json"
cmp "$scratch/seven.json" "$d/seven.json"
python3 -B "$d/line_prefix.py" "$scratch/six.json" "$scratch/L-meta-8277-shared13-prefix6" "$scratch/six-results.json"
python3 -B "$d/line_prefix.py" "$scratch/seven.json" "$scratch/L-meta-8277-shared13-prefix7" "$scratch/seven-results.json"
python3 -B "$d/boundary.py" "$scratch/L-meta-8277-shared13-line-boundary" "$scratch/b.json" --gates 0 3 5 --width 3 4 5 6 --seconds 60
python3 -B "$d/boundary.py" "$scratch/L-meta-8277-shared13-boundary-mid" "$scratch/m.json" --gates 1 2 4 --width 5 6 7 --seconds 60
python3 -B "$d/boundary.py" "$scratch/L-meta-8277-shared13-boundary-raw" "$scratch/r.json" --gates 0 --width 7 8 9 --seconds 60
python3 -B "$d/check.py" "$scratch"
```

The final check compares regenerated formulas and certificates against the recorded hashes from the pinned solver version, replays them and exercises the positive controls. Use a fresh cache directory for regenerated proofs.
