# Exact gate counts for Boolean tables

A row input and a column input turn on together. The circuit must return the bit in that cell. What is the cheapest way to compute the whole table? The following results count each AND or OR as one gate, with at most two input wires per gate. Circuits may read any earlier wire more than once. A formula pays for each separate occurrence. In the signed model a NOT also costs one. Inputs outside the one-row, one-column promise may take any output.

## One table, two exact costs

For every side length n ≥ 3, put ones in the upper-left (n−1) × (n−1) block, erase its bottom-right one, and put a single one at the bottom-right of the full table. All remaining cells are zero. The exact minimum is **2n circuit gates and 3n−3 formula gates**. For n = 5 the same table takes 10 gates with sharing and 12 as a formula.

```text
11110
11110
11110
11100
00001
```

The circuit builds the OR of the first n−2 columns once and passes it to two readers. The lower bound explains why a cheaper formula cannot recover the saving. Each of n−2 distinct rows and columns meets at a corner of a two-by-two block containing three ones. For each of those corners either the row wire or the column wire must appear twice. Counting these forced repeats gives the matching lower bound. The argument uses the communication protocol for monotone formulas of Karchmer and Wigderson. [Lean theorem](proofs/FormulaGap.lean) · [Exact statement](statements/FormulaGap.statement) · [Karchmer and Wigderson](https://www.math.ias.edu/~avi/PUBLICATIONS/MYPAPERS/KW90/KW90.pdf)

## Copies, twins and the 104 desk statements

**Copying circuits.** Suppose every row has an accepting cell whose column contains a zero elsewhere, and every column has an accepting cell whose row contains a zero elsewhere. Keep one representative of each and make any number of additional copies, in any order. Each added row or column raises the optimum by exactly one gate. One OR pools a new copy with the old input. Restricting away that copy eliminates a gate in any circuit computing the expanded table. [Copy theorem](proofs/CircuitCopies.lean)

**Copying formulas.** Collapse groups of identical rows and columns. Weight each leaf of a formula on the smaller table by the number of copies of its input. If at least one promised cell is accepted, the minimum weighted leaf count is exactly the minimum number of ordinary leaves on the expanded table. For the seed with rows `110 / 100 / 001`, let T be the expanded row count plus column count, a the multiplicity of row one and c the multiplicity of column one. The exact circuit cost is T and the exact formula cost is T + min(a,c) − 1. Here row one and column one mean the first of each, in the displayed order. [Weighted reduction](proofs/TwinReduction.lean) · [Seed theorem](proofs/TwinTable.lean)

**A dated census.** Of 104 distinct monotone desk statements recorded on November 26, 2026, 42 expand the three-by-four seed `0001 / 1010 / 1100` or its transpose, and 62 expand the three-by-three seed above. The three-by-four seed has optimum seven. Its four-by-five instance L-meta-20937 has optimum nine. All 104 recorded questions ask whether one fewer gate suffices. Their exact circuit minima and the associated row and column labels are checked in Lean. An earlier 49-row census checked both formula and circuit minima for the three-by-three seed. Forty-seven rows occur in both snapshots. Nine of the earlier 49 save one gate through reuse. [104 recorded statements](data/desk-statements.json) · [104-case proof](proofs/CopyDeskCensus.lean) · [49 recorded statements](data/desk-matches.json) · [49-case proof](proofs/TwinDeskBatch.lean) · [Desk example](https://pequalnp.com/desk/row?gap=L-meta-20937)

The counts describe mathematical answers in two dated public snapshots. Bolitow had already reported optimal circuits for a related 33-mask series, including L-meta-20937, and Zigler had independently excluded the smaller budget there. Errornesttorn used a three-corner obstruction on a four-by-four graph. The general copying theorem builds on the project's induced-restriction argument and prior duplicate-deletion work. [Bolitow’s results](https://github.com/open-goat/pequalnp-proofs/discussions/21642#discussioncomment-19928311) · [Zigler’s results](https://github.com/open-goat/pequalnp-proofs/discussions/21642#discussioncomment-19929108) · [Earlier corner argument](https://github.com/open-goat/pequalnp-proofs/pull/11469) · [Induced restriction helper](https://github.com/open-goat/pequalnp-proofs/blob/e6bfe1a56efc768d244627b78f175b18de1acd6f/lean/PEqualNP/MetaComplexity/Helpers/RepInduced.lean) · [Earlier duplicate deletion](https://github.com/open-goat/pequalnp-proofs/pull/14259)

## Disjoint forbidden pairs

Start with an all-ones table and erase s disjoint row–column pairs. If s ≥ 2 and there is at least one spare row and one spare column, exactly **2s gates** suffice and are required when NOT is allowed. The opposite function, which accepts exactly the erased pairs, takes **2s−1 positive gates**. Each pair costs one AND, their union costs another s−1 gates and one NOT reverses the answer. A lower bound counts the input wires needed to distinguish the exceptional rows and columns. [General matching theorem](proofs/MissingMatching.lean)

For exactly three missing pairs on R ≥ 4 rows and C ≥ 4 columns, the original table takes **R+C+1 positive gates**, **six gates with NOT**, and its complement takes **five positive gates**. On a square this attains a difference of 2n−4 between the two positive costs. The universal complement bound proposed on the desk remains a separate problem. [Three-pair theorem](proofs/ThreeMissing.lean) · [Exact statement](statements/ThreeMissing.statement) · [Desk conjecture](https://pequalnp.com/desk/row?gap=L-meta-19384)

MrMaleficus’s square construction already has 2n+1 gates. Willakone established the earlier positive lower bound of 2n. Willakone and edmoreno supplied the six-gate constructions with NOT. The rectangular optimality proof uses the upstream six-cycle theorem proved by BastianMIllan. [Earlier gate list](https://github.com/MrMaleficus/pequalnp-proofs/blob/24c5d7e9fccb676ddb604e4a967e58a0a021f777/lean/PEqualNP/Outside/L_meta_25442.lean#L290) · [Earlier lower bound](https://github.com/open-goat/pequalnp-proofs/pull/37814) · [Willakone’s construction](https://github.com/open-goat/pequalnp-proofs/pull/37799) · [Edmoreno’s construction](https://github.com/open-goat/pequalnp-proofs/pull/37832) · [Six-cycle proof](https://github.com/open-goat/pequalnp-proofs/blob/e6bfe1a56efc768d244627b78f175b18de1acd6f/lean/PEqualNP/Outside/L_meta_6158.lean)

## Verification and replay

All ten Lean modules matched their checker-recorded source hashes and passed the upstream checker locally at the pinned revision. The checker compared each module’s exported theorem against its separate statement and reported only `propext`, `Quot.sound` and `Classical.choice`. These are local verification results. The proofs and dated desk data are provided here for independent replay.

Prepare a disposable checkout of [the upstream project at revision e6bfe1a](https://github.com/open-goat/pequalnp-proofs/tree/e6bfe1a56efc768d244627b78f175b18de1acd6f) with Node.js, Python 3, Lean 4.36.0 and its pinned mathlib dependencies available. The pinned [project checker](https://github.com/open-goat/pequalnp-proofs/blob/e6bfe1a56efc768d244627b78f175b18de1acd6f/tools/check-lean.mjs) requires the prebuilt mathlib cache. In the checkout’s `lean/` directory, `lake exe cache get` prepares that cache. From this package directory, substitute the checkout’s path in the first command. The runner copies the ten modules into that checkout and checks them in dependency order. With dependencies installed, verification can run offline.

```sh
python3 -I -B replay.py /path/to/upstream-checkout
python3 -I -B checks/check_copies.py
python3 -I -B checks/check_twins.py
python3 -I -B checks/check_sharing.py
python3 -I -B checks/check_missing.py
```

The Python controls independently reconstruct all 104 desk statements, compare 6,948 small table and multiplicity combinations, test the square construction at 32 sizes and evaluate explicit gates on 140 rectangular forbidden-pair instances. The all-sizes lower bounds are the Lean theorems.
