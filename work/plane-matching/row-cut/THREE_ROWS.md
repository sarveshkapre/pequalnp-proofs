# Three ordinary rows force 29 gates in Amritpal Nijjar’s grid

In [Amritpal’s six-row grid](https://github.com/open-goat/pequalnp-proofs/discussions/21642#discussioncomment-19905319), an ordinary row first combines its four raw incident lines with three OR gates, in any order. It then ANDs that result with its point. If three such row outputs have paths to the final output, a circuit passing the grid needs **at least 29 gates**. The usual six-row circuit attains 29. This covers all 20 choices of three rows. Intermediate wires can be shared, the fixed row outputs can feed ANDs or ORs, and the other three rows can distribute their pairs anywhere.

Consequently a 28-gate solution must change or disconnect at least four of the six ordinary rows. Whether it exists remains open. This strengthens the [four-row bound](https://github.com/open-goat/pequalnp-proofs/discussions/21642#discussioncomment-19928951) and answers the open 13-gate shared-block question in [the earlier three-row note](https://github.com/open-goat/pequalnp-proofs/discussions/22682#discussioncomment-19909709).

## From 28 gates to 13

Call the three other rows active. The fixed rows use 12 distinct gates. Two rows share exactly one line, whereas each intermediate OR in an ordinary row contains at least two of its lines. Move the fixed gates to the front and retain every intermediate as an available input. Work in the part of the circuit with a path to the output. Set the three fixed point guards to zero. At least three further gate positions can be removed, even when a guard is read multiple times.

Here is the counting argument for either restriction used below. Suppose we set r distinct live input wires to zero. Mark them and every gate with two marked inputs. All marked wires are zero. The output is unmarked because some required positive survives. If h gates have two marked inputs and b have one, the r + h marked wires must all be read. There are 2h + b marked input slots. Thus h + b ≥ r. Every one of those h + b gates can be deleted. A touched AND is zero, and a touched OR copies its unmarked operand or is zero. After constant propagation only the surviving binary gates need to be built. [Lean proof of the rewrite and count](GuardRestriction.lean)

Set the three fixed raw points to zero and discard lines incident to none of the three active rows. The remaining circuit has at most **28 − 12 − 3 = 13 gates**. Its three raw points are necessary: switching the point off in any required pair turns the answer off. On the projected inputs, all other sources are line masks. We grant every raw line, every supplied line OR, and every subset OR from each fixed row. This includes all the actual intermediate wires, even subsets that could not be built together by one choice of fixed OR trees. Merge identical projected inputs and prune unused gates. A connected circuit with g binary gates reads at most g + 1 distinct inputs, since its 2g slots must also read its g − 1 earlier gate outputs. A 13-gate circuit therefore reads **at most 11 distinct nonempty line masks** alongside the three points.

## Six more gates must disappear

Compare the required positive consisting of one active point and one incident line with a legal negative having the same point and other lines. The circuit must read a line mask that is on in the positive and off in the negative. Otherwise monotonicity gives the wrong answer. For each comparison this specifies a short list of possible input masks. Disjoint lists require distinct wires. The [comparison data](ThreeRowData.lean) give actual point and line indices. [Lean’s check](ThreeRowSources.lean) reconstructs the allowed input bank, verifies each physical comparison and checks the overlap between the lists.

* **Three different pairwise intersections (18 choices).** Keep the three lines where pairs of active rows meet. There are six comparisons for which the only distinguishing masks avoid all three kept lines. No mask serves two comparisons. Hence at least six distinct live sources switch off. Every other mask projects to at most one kept line. Each active point meets two of the three kept lines, leaving a six-cycle of required pairs.
* **One common line (2 choices).** There are ten active lines. Every singleton line mask must be read. For each proposed missing singleton, the evidence gives a comparison no other source can distinguish, or twelve comparisons that need twelve different other sources. The latter exceeds the budget of eleven. Besides the ten singletons the circuit can therefore read at most one more mask. Each free mask meets each active row in at most one line. Keep the common line and choose one of each row’s three private lines outside that extra mask, if it exists. The three private groups are disjoint. Six singleton sources switch off, and every remaining source projects to at most one kept line. Each point now meets the common line and its own private line, again leaving six required pairs.

The gate-deletion count leaves **at most seven gates** in either case. After simplifying zero and merging copies, the only inputs are three points and the individual surviving lines. Crucially, the six vanished sources are distinct *inputs actually read* by the live circuit. Merely switching off six available lines would not justify deleting six gates.

## The two seven-gate exclusions

The small circuits must accept all six incident pairs and reject disjoint inputs having at most two points and two lines. These negatives are always admissible on the physical grid. The [projection check](replay_three_rows.py) also compares the necessary tests with the original 177-entry boundary table for all 72 embeddings used here.

| Remaining incidences | Seven-gate formula | LRAT actions checked by Lean | Eight-gate control |
| --- | ---: | ---: | --- |
| Common line plus three private lines | 5,338 clauses | 141,592 | Satisfying circuit decoded and tested |
| Six-cycle | 4,863 clauses | 141,790 | Satisfying circuit decoded and tested |

The [encoder](three_rows_core.py) permits AND or OR of any two earlier wires, including repeated operands, unused gates and arbitrary fanout. It uses the final gate as output. A shorter circuit can append OR copies of its output. Smaller negative tests follow from the maximal ones by monotonicity. Each pin chooses one earlier wire, and the clauses fix the truth table of each gate on each test. Pins can be sorted because both operations commute. Ready gates can be ordered by their larger operand index: choose the least such index next. Every gate made ready by this choice reads the newly assigned wire, which is later than either operand of the chosen gate. This yields nondecreasing larger operand indices. Apply this ordering to the live circuit before padding it at the end. Neither symmetry requires a tree or distinct readers.

The two contradictions rule out the remaining seven gates. An eight-gate control is also apparent in each shape: for each of the three points, OR its two kept lines and AND with its point, then join the three terms using two ORs. For the original grid, the 29-gate ordinary construction was evaluated on all 131,072 physical inputs.

## Offline replay

From the package root, with Python 3.10+ and Lean 4.36.0 installed:

```sh
python3 -B work/plane-matching/row-cut/replay_three_rows.py evidence --bin /path/to/lean-4.36.0/bin
```

This regenerates the 38 comparison families, compiles and kernel-rechecks the Lean geometry and comparison theorems, verifies both CNF and certificate hashes, replays both supplied LRAT contradictions, and decodes both eight-gate controls. The physical reduction and its connection to the emitted CNFs are written proofs. There is no single end-to-end Lean theorem for the physical 29-gate bound in this package.

The included gate-deletion proof can be rechecked separately against the pinned upstream Lean project with its built Mathlib:

```sh
python3 -B work/plane-matching/row-cut/check_guard_lean.py /path/to/pequalnp-proofs/lean --bin /path/to/lean-4.36.0/bin
```

Amritpal supplied the grid and its parent reduction. His [22-pair result](https://github.com/open-goat/pequalnp-proofs/discussions/21642#discussioncomment-19910118) assumes six private line computations and an additional internal-gate condition. The earlier four-row argument supplies the gate-deletion lemma. The new steps here are the comparison families that force six more gates to disappear and the two six-incidence exclusions.
