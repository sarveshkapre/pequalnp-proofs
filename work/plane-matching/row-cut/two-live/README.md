# Two ordinary rows force 29 gates in Amritpal Nijjar’s grid

A passing circuit that keeps any two ordinary rows connected to its output needs exactly **29 gates**. An ordinary row ORs its four raw incident lines with three gates and ANDs that result with its point. The other four rows can share wires freely. The two fixed outputs can feed ANDs or ORs and can have any number of readers. All 15 choices of the two rows are covered. A 28-gate solution would have to redesign or disconnect at least five rows. The cases with one or zero ordinary rows remain open.

Amritpal supplied the [grid, free inputs and parent reduction](https://github.com/open-goat/pequalnp-proofs/discussions/21642#discussioncomment-19905319). The [three-row proof](https://github.com/sarveshkapre/pequalnp-proofs/blob/c7da2bdb6cd1c9ed43024afbfa4c44591aaabad6/work/plane-matching/row-cut/THREE_ROWS.md) supplies the gate-deletion argument. The new calculation handles four freely sharing rows and includes all the surviving choices of line inputs.

## Why only 18 gates remain

The two ordinary rows use eight distinct gates. Their sets of four incident lines meet in only one line, so none of their intermediate ORs can be the same gate. Move the eight to the front and make every intermediate result available for reuse. Keep only wires on paths to the output. On inputs with only the other four points selected, both fixed guards are zero. Both guards had a reader, and setting them to zero eliminates at least two further gate positions.

More generally, mark *r* distinct live source wires set to zero, then mark gates with two marked operands. The final output is unmarked whenever a required positive survives. If *h* gates have two marked inputs and *b* have one, every one of the *r + h* marked wires has a reader among the *2h + b* marked slots. Thus *h + b ≥ r*. Every touched gate simplifies to zero or to its other input. This is the previously [Lean-checked count and rewrite](../GuardRestriction.lean).

A proposed 28-gate circuit therefore leaves at most 18 gates. Switch off lines touching none of the four active rows. The remaining sources are the four active point bits and line masks. A line mask is one wire that ORs a specified set of lines. Grant every raw line, the supplied line ORs, and every subset OR from either fixed row, projected onto the active lines. This even allows some combinations of masks that a particular pair of ordinary OR trees could never supply together.

Each active point is necessary. Switching it off in one of its required pairs gives a required negative. A live circuit with *g* binary gates can read at most *g + 1* distinct sources, since its *2g* slots must read all *g − 1* non-output gates. Hence the residual circuit can read at most **15 distinct line masks**.

## The two smaller grids

Keep only lines incident with at least two active rows. Turn every other line off. A source vanishes if its entire mask is outside the kept lines. For each distinct vanishing source actually read, at least one gate disappears by the same count. The signed tests below are exact projections of the original 24 positives and 153 maximal negatives. Intersect each negative with the kept inputs, remove duplicates and keep maximal negatives. Every resulting negative is legal by downward closure.

| Active points on the two sides | Row choices | Kept lines | Incidences | Exact minimum on the kept inputs | Vanishing sources allowed in 18 gates |
| --- | ---: | ---: | ---: | ---: | ---: |
| Three on one side and one on the other | 6 | 4 | 9 | 12 | At most 6 |
| Two on each side | 9 | 6 | 12 | 15 | At most 3 |

In the first shape every nonzero source projects to one line. In the second shape there are also three free ORs, each joining two lines that meet disjoint pairs of active points. The search covers all eight choices of which free ORs are read. Every raw point and raw line in each smaller grid has a positive and negative comparison that no other available source separates. The usual row construction attains both minima. The replay verifies the geometry by comparing the full signed test lists and banks under relabeling for all 15 choices.

## Finishing the four-row search

For each required pair, compare it with a legal negative containing the same point. At least one line input used by the circuit must be on in the positive and off in the negative. Otherwise monotonicity makes the two required answers impossible. Enumerate source sets that meet these comparisons and the two bounds above. Across the 15 choices, **494 sets** survive, counting the same set separately for different physical choices of rows.

For each set, search circuits of at most 18 AND/OR gates on the four active points and precisely those line inputs. Impose the full projected physical tests, including negatives with several selected points. No set passes. The first implementation visited 171,224 search states in this final stage and the second visited 184,741. These counts exclude the earlier searches for the two smaller grids.

## Why the circuit enumeration covers arbitrary sharing

At any stage keep the list of wires with at least one future read. Choose two as operands and choose AND or OR. For **each operand separately**, branch on whether it has another reader. Append the new gate and continue. Every live circuit gives such a sequence by listing its gates in dependency order and marking the last read of every wire. A repeated operand is an identity and can be removed. With *n* live wires, reaching a single output still costs at least *n − 1* gates. Both implementations may order ready gates by the larger operand index. A gate that becomes ready through the latest addition necessarily reads that new, higher-indexed wire. The first implementation also orders ties by the smaller index.

If a live wire is the only one distinguishing a positive from a negative, its last read must pass that distinction to the new gate. Future monotone gates cannot restore it. The two implementations check this in different ways. The first counts uniquely covered comparisons. The second intersects truth columns before and after the wire. A gate that is always zero on positives or always one on negatives can be replaced by that constant and simplified. A gate can also be bypassed if an earlier wire is at least as good on every signed test. Replacing it can only increase accepted positives and decrease accepted negatives. The second implementation applies this last shortcut only to the gate’s own operands. In each search it suffices to consider a smallest solution across all allowed input sets. Its actual used inputs are among the sets searched.

## Verification and replay

Two separately implemented C++ enumerators ruled out both smaller budgets and all 494 full source sets. They share the physical projections and the list of sets. A separate encoding reconstructs all 1,072 legal physical negatives and certifies that no possible input set was missed. Lean 4.36.0’s LRAT checker verified one contradiction per physical row choice, with **13,224 proof actions** in total. These certificates concern the completeness of the source-set list. The gate searches are exhaustive computations and the link from physical circuits to them is a written argument. There is no end-to-end Lean theorem for the 29-gate bound.

The ordinary 29-gate circuit was checked on all 131,072 physical inputs. Deleting one line from one ordinary row gives 24 different 28-gate controls. Each missed exactly its deleted pair and passed every maximal negative. A separate small control compares both search implementations with brute-force truth-table generation through five gates.

Run the following from this directory with Python 3.10+ and a C++17 compiler supporting unsigned 128-bit integers. The Lean command defaults to the local elan installation of Lean 4.36.0 and accepts `--bin` for another installation.

```sh
python3 -B replay.py
python3 -B replay.py --independent
python3 -B small_controls.py
python3 -B source_audit.py --replay evidence
```

To generate new source-set certificates, run `python3 -B source_audit.py --evidence /path/to/fresh-directory`. The [verification receipt](receipt.txt) records both search totals and the formula and certificate hashes. The original 177-test table has SHA-256 `0309a50b7f4f33cc532ce313030c40d77220335cc93d1e921e55618f8c154699`.
