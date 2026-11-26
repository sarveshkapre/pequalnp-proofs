# Nine mixing gates in the three-row replacement for L-meta-8277

Keep three ordinary four-gate rows of the six-row grid. Give the other three rows a single replacement block and join its output to the fixed rows with three ORs. A 28-gate candidate then has at most 13 gates in the block. It may share wires and distribute its twelve required point–line pairs anywhere in the block. After setting the three fixed points to zero and removing unused gates, every passing block requires **at least nine gates with both a point input and a line input among their ancestors**. This holds for all 20 choices of active rows. At most four gates remain for pure point or pure line preparation in this architecture. Existence of such a block and the unrestricted 28-gate question both remain open. [Original grid task and discussion](https://github.com/open-goat/pequalnp-proofs/discussions/22682)

The [counting argument](work/grid/repair_three/shared13/profiles/README.md) rules out seven or fewer mixed gates and establishes the minimum numbers of entering pure wires. At eight mixed gates, the sixteen input pins force either [a tree](work/grid/repair_three/shared13/eight/tree/README.md) or [one repeated wire](work/grid/repair_three/shared13/eight/fan/README.md). The enumeration covers both, including repeated reads of a point, a line, or an intermediate mixed signal. It uses the [separate bound of nine gates for the three line masks](work/grid/repair_three/line/README.md). Project contributors supplied the original grid and circuit question. This hand-back supplies the restricted search and its certificates.

The enumerations and their connection to physical circuits are written mathematical arguments with executable checks. Lean 4.36.0's standard LRAT checker verified the residual formulas from both lists. The full implication from the grid definition to the bound has no end-to-end Lean proof here. There are 167 tree entries and 29 repeated-wire entries, with 175 distinct formulas. The original run included 100 larger physical control circuits across all row choices, each passing the 177 grid tests. [Counts and evidence](work/grid/repair_three/shared13/eight/README.md)

## Replay the residual certificates

From this directory, Python 3.11 or later can check the archived certificates offline with no packages or solver installation. The command normalizes the saved enumeration outputs, rebuilds each CNF, verifies its identity against the archive, then derives the empty clause by following the LRAT unit-propagation hints. Keep Python assertions enabled.

```sh
python3 -B replay.py
```

The expected final line is `196 entries, 175 distinct formulas. Each derived the empty clause.` The archive contains only numeric DIMACS and LRAT text with SHA-256 names. To rerun the Lean checks and planted controls, use a new directory named `cache` and the Lean 4.36.0 toolchain with its bundled CaDiCaL under elan. Set `LEAN_BIN_DIR` to its `bin` directory if installed elsewhere.

```sh
python3 -B replay.py --cache cache
d=work/grid/repair_three/shared13/eight
python3 -B "$d/prefix/verify.py" tree "$d/tree/three.json" "$d/tree/four.json" --cache cache
python3 -B "$d/prefix/verify.py" fan-verify "$d/fan/prefixes.json" --cache cache
```

The tree and repeated-wire notes link the original enumeration code so the starting ledgers can be regenerated. The repeated-wire positive controls also require a C++17 compiler. The prerequisite bounds have their own regeneration commands and certificate fingerprints. The archive supplied here contains the eight-mixed-gate residual certificates.
