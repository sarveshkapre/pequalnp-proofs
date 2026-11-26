# Rebuilding two rows of the 28-gate grid

In Amritpal Nijjar’s grid, keep four ordinary rows in the part of the circuit that can reach the output. For each of those rows, three ORs join its four raw incident lines and an AND joins the result to its point. All other wiring is free. The four row outputs may feed ANDs, feed ORs, or be read multiple times. The two remaining rows may share their entire computation.

The table gives the minimum total gate count to reject every required negative and accept at least the indicated number of required pairs. In the last column the circuit must also accept the input with all six points and no lines. That extra input is outside the posted tests.

| Required pairs accepted, out of 24 | Posted tests | Also accept all six points with no lines |
| ---: | ---: | ---: |
| 21 | 26 | 28 |
| 22 | 27 | 29 |
| 23 | 28 | 30 |
| 24 | 29 | 31 |

Every entry is attained for all 15 choices of the rebuilt rows. With the extra input required, a 28-gate design that covers 22 pairs must therefore change the ordinary computation for at least three rows, or disconnect an ordinary row from the output. Without the extra condition, a 28-gate design that passes the full grid must also have at most three live ordinary rows. Whether such a circuit exists is open.

Amritpal supplied the [grid and its reduction](https://github.com/open-goat/pequalnp-proofs/discussions/21642#discussioncomment-19905319). His [22-pair bound](https://github.com/open-goat/pequalnp-proofs/discussions/21642#discussioncomment-19910118) assumes six private line computations and a different internal-gate condition. The previous two-row search gave the 29-gate minimum with four final ORs and no extra input. The argument below also allows the four fixed row outputs to be used anywhere. The input-counting argument used here also appears in [bolitow’s star proof](https://github.com/open-goat/pequalnp-proofs/discussions/21642#discussioncomment-19908568).

## Why four intact rows cost at least 20 gates on this test

Sixteen gates form their four ordinary rows. These gates are distinct. Any two rows meet in only one line, and every intermediate line OR in a three-OR tree for four distinct lines contains at least two of them. Move these independent row computations to the beginning and give all of their wires to the remaining circuit. Set their four final AND outputs to zero. This preserves all required pairs of the two rebuilt rows and the extra zero-line input. It can only turn other outputs off, so all required negative tests still pass.

At least four more gate positions disappear. Mark the four zeroed inputs and every gate whose two inputs are marked. Such a gate is zero. Every gate with a marked input can be removed: an AND becomes zero and an OR becomes its other input. First discard wires outside the output’s dependency graph. The output is unmarked because at least one required pair survives. Every marked wire therefore has a reader. If there are h marked gates and b additional gates with one marked input, there are 4+h marked wires and 2h+b marked input slots. Hence 4+h ≤ 2h+b, so h+b ≥ 4. This argument allows reuse, gates with repeated operands and any choice of final operation. [Wire semantics and gate count in Lean](GuardRestriction.lean)

The other inputs now available are six raw points and line ORs. On the seven lines of the rebuilt rows, each line OR contains at most one line of each row. This is true for the public input bank and for every subset of a fixed row’s lines. The four old point-gated outputs can be replaced by the freely available zero. Of the 24 required pairs, at most 16 lie in the fixed rows. Write k for the number required from the other two.

## The two-row calculation

The two rows, A and B, share one line and each has three private lines. Offer the circuit every line mask containing at most one line from each row. This includes zero, each of the seven singleton lines, and all nine ORs of one A-private and one B-private line.

We use two sets of tests.

- In the ordinary test, the only raw points are A and B. The circuit must accept k selected incident pairs and reject disjoint inputs with at most two of the seven lines.
- In the second test there is one more point Q. With Q off, impose the ordinary tests. With Q on, require acceptance at A=B=1 and no lines. Require rejection whenever at most one of A and B is on, at most two private lines are selected, and none meets a selected row. Only the maximal such negatives need to be tested, by monotonicity.

For 5 ≤ k ≤ 8 the ordinary test needs at least k+1 gates and the second test needs at least k+3. Each AND or OR reads two earlier wires. Any wire may be reused.

**Five pairs.** There are 56 ways to choose five of the eight flags. Permuting the three private lines within each row and swapping whole rows gives six cases. For every case, a five-gate ordinary circuit and a seven-gate circuit with Q were both impossible. All twelve contradictions replayed in Lean’s LRAT checker. At the next gate count all twelve formulas have solutions. Each decoded positive control was evaluated separately. The encoding permits copies, unused gates, free zero and arbitrary reuse. The compact representation of lines, gate order and proof receipts are described below.

**Six to eight pairs.** Suppose the assertion holds for k−1. A live gate that reads a private line by itself disappears when that line is switched off. On every remaining port, erase that line from its mask. This leaves a legal smaller circuit with at least k−1 covered pairs. Required negatives still pass because only values have decreased. The zero-line input keeps its value. The induction bound proves the claim in this case.

Otherwise all reads of a private line are through masks that pair it with a private line of the other row. Consider a covered pair A with line a. If a occurs with at most two B-private lines, select those partners in place of a, keeping A on. Every input available to the live circuit that was on before is still on. Yet this new input is a required negative. The same argument applies to B. Consequently each covered private flag requires all three of its cross masks. With six, seven or eight covered pairs, at least eight, nine or nine distinct cross masks must be read, respectively. Both raw points are necessary, as seen by turning the point off in a covered singleton. In the second test Q is necessary as well. A live binary circuit of g gates can read at most g+1 distinct input wires: its 2g input slots must already read at least g−1 non-output gate wires. These counts give the claimed bounds. [Finite cross-mask count in Lean](GuardRestriction.lean)

## Why the extra test applies to physical circuits

In the smaller block, first switch off all four other raw points. This leaves the ordinary problem. If at least two of those points occur in the live circuit, at least two gates disappear by the marked-wire count above. Thus the original block already needs k+3 gates. This argument also covers any pair of rebuilt rows on opposite sides when a full side of points is necessary at zero lines.

If at most one other raw point occurs, take the all-points, no-lines input. All line masks and all fixed row guards are off. Switching off every other unused point cannot change the answer. An accepted zero-line input must contain all three points of one side: otherwise it is a required negative. Thus the two rebuilt points are on the same side, and the single other point that occurs must be their third point Q. Their shared line is the only line from either rebuilt row incident to Q. On the second test’s negative inputs that line is absent, so its fixed row guard is also off on the original physical input. This gives exactly the necessary tests stated above, even for circuits that use Q many times. The earlier deletion of the four fixed guards preserves or decreases the output on each of them.

## Constructions and replay

Keep the four fixed rows. At each rebuilt point, OR together its selected lines and AND the result with the point. Both rows have a selected pair since k ≥ 5. OR the two results, then join the four fixed outputs. The whole circuit has 21+k gates. To accept all six points with no lines, choose either rebuilt point. Take the AND of the other two points on its side and OR it into that point’s line signal before its point guard. This costs two more gates and adds exactly the full three-point term on that side. All required negatives reject that term. For all 15 pairs and all selected subsets at sizes 5 through 8, both constructions were tested on every one of the 131,072 physical inputs. This covers 2,790 circuits.

The [encoder](two_rows_sat.py) chooses a line mask, a raw point or an earlier gate at each operand. The masks are constrained exactly by the per-row membership rule. The AND/OR truth table is imposed at each gate on each signed test. The final gate is the output; an earlier output can be copied to pad the size. Each gate is ordered by its later operand’s dependency rank, with all primary sources tied. Scheduling an available gate of least such rank preserves that ordering: a gate made available by the choice reads the newest wire. The two pins commute. Among equivalent orders of private lines with the same row and coverage status, the lexicographically largest operand mask matrix has sorted columns and sorted pairs of line operands. The formulas use these symmetries and impose no minimality or liveness constraint.

From the package root, these scripts need Python 3.10+ and Lean 4.36.0 (including its bundled CaDiCaL). The first command checks the supplied contradictions and controls without invoking a solver. The second independently recomputes the grid tests and sharp constructions. The third exhausts small gate lists as a check of the marked-wire argument.

```sh
python3 -B work/plane-matching/row-cut/check_two_row_receipt.py evidence
python3 -B work/plane-matching/row-cut/check_two_row_grid.py
python3 -B work/plane-matching/row-cut/check_guard_removal.py
```

To regenerate the search and its controls in a fresh directory, run the following, supplying the directory containing the pinned Lean and CaDiCaL executables if they are outside the default elan location.

```sh
python3 -B work/plane-matching/row-cut/replay_two_rows.py /tmp/fresh-two-row-proofs --bin /path/to/lean-4.36.0/bin
```

The gate-rewrite semantics, its counting bound and the finite cross-mask inequality are Lean theorems. The twelve contradiction certificates have separate LRAT replays. The physical reduction, the map from a circuit into the emitted SAT clauses, and the induction linking the pieces are written proofs. The unrestricted 28-gate problem remains open.

To compile the three Lean source files and recheck the resulting module with the kernel, supply the built upstream Lean project with its Mathlib dependency.

```sh
python3 -B work/plane-matching/row-cut/check_guard_lean.py /path/to/pequalnp-proofs/lean
```
