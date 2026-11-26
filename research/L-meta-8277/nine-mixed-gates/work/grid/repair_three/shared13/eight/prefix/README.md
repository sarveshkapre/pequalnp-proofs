# Checking the line circuits for the eight-gate split

Each remaining mixed circuit specifies what its incoming line wires must do. For example, if only one physical line is selected, those wires must produce a bit pattern that gives the correct answer for each of the three points. Each line can choose any pattern allowed for it. The question is whether the remaining pure gates can prepare all those wires together.

| Mixed circuit | Common line | Triangle | Total cases |
| --- | ---: | ---: | ---: |
| Tree | 153 | 14 | 167 |
| One wire read twice | 20 | 9 | 29 |

All 196 entries have checked contradictions. The two branches share 21 formulas, leaving 175 distinct formulas by SHA-256. A larger planted circuit also passed for each entry. The [tree enumeration](../tree/README.md) and [repeated-wire enumeration](../fan/README.md) explain which cases reach this check.

The [normalizer](solve.py) renames the three rows and the entering line wires. Row renaming preserves the number of physical lines of each membership type in both shapes. Wire renaming merely permutes the positions in each permitted bit pattern. After renaming, identical constraints with the same gate budget use the same result. The [line encoder](../../profiles/line_prefix.py) allows all earlier line gates to be shared. Its free inputs include every singleton-line mask meeting each row in at most one line, which includes every physically available free mask. A contradiction in this larger search rules out a physical preparation.

## Replay

From the workspace root, with Python 3.11+ and the Lean 4.36.0 toolchain under elan, the following rebuilds the raw tree cases and checks the certificate files in `./cache` (created by the root replay command). The repeated-wire enumeration has its own instructions for rebuilding `prefixes.json`.

```sh
d=work/grid/repair_three/shared13/eight
scratch=$(mktemp -d)
python3 -B "$d/tree/tree.py" 3 "$scratch/three.json"
python3 -B "$d/tree/tree.py" 4 "$scratch/four.json"
python3 -B "$d/prefix/verify.py" tree "$scratch/three.json" "$scratch/four.json"
python3 -B "$d/prefix/verify.py" fan-verify "$d/fan/prefixes.json"
```

To generate the proofs from scratch, use fresh run names. The solver writes the class and result ledgers alongside its source and keeps the larger formulas and proof files under `--cache`. The example compares both regenerated ledgers with the recorded ones, then replays each proof and decodes its larger passing control.

```sh
python3 -B "$d/prefix/solve.py" new-tree "$scratch/three.json" "$scratch/four.json" --cache "$scratch"
python3 -B "$d/prefix/solve.py" new-fan "$d/fan/prefixes.json" --cache "$scratch"
for part in classes results; do
  cmp "$d/prefix/new-tree-$part.json" "$d/prefix/tree-$part.json"
  cmp "$d/prefix/new-fan-$part.json" "$d/prefix/fan-verify-$part.json"
done
python3 -B "$d/prefix/verify.py" new-tree "$scratch/three.json" "$scratch/four.json" --cache "$scratch"
python3 -B "$d/prefix/verify.py" new-fan "$d/fan/prefixes.json" --cache "$scratch"
```

The [tree ledger](tree-results.json) and [repeated-wire ledger](fan-verify-results.json) record the formula and proof hashes and the number of checked LRAT actions. Lean checks those individual contradictions. The physical reduction, the two topology enumerations, and the translation into formulas are described and tested separately.
