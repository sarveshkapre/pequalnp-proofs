# At least nine gates must mix points and lines

Keep three ordinary rows and give the other three a single block of at most 13 gates. Each row's four required pairs can be covered in different places. Any passing block must use at least **nine gates that have both a point and a line among their inputs or earlier ancestors** after the three frozen points are set to zero and unused gates are removed. This leaves at most four gates to work on points alone or lines alone. The result covers all 20 choices of three rows. Whether a block of 12 or 13 gates can pass is still open.

The [previous bound](../profiles/README.md) rules out seven or fewer mixing gates. At eight, sixteen pins have to read seven earlier mixed outputs and at least eight distinct incoming wires. Nine incoming wires give a tree. With eight incoming wires, exactly one wire feeds two pins. That wire can carry points alone, lines alone, or an earlier mixed result.

| Shape of the three rows | Tree | One wire read twice |
| --- | --- | --- |
| All three meet on one line | Ruled out, 153 residual checks | Ruled out, 20 residual checks |
| Each pair meets on a different line | Ruled out, 14 residual checks | Ruled out, 9 residual checks |

For each wiring pattern, the search asks what its line inputs would have to say when only one physical line is on. Many patterns cannot distinguish all three rows. Others would let us construct the rows' three full line signals in eight gates, contradicting the [known nine-gate minimum](../../line/README.md). For the remaining patterns we tested whether the available gates could prepare suitable line signals. Every case was impossible, even allowing additional free line inputs beyond those supplied by the grid.

The topology arguments and enumeration are documented and executable. Lean's LRAT checker verified all 196 entries in the two case lists. The lists share 21 identical formulas, leaving **175 distinct formulas**. A second checker derived a contradiction for each using its listed clauses alone. Each entry also accepted a planted line circuit at a larger budget. Across all 20 row choices, 100 full-grid controls exercised both tree splits and each kind of repeated wire. All passed the 177 physical tests with a block larger than 13 gates. [Tree enumeration and controls](tree/README.md) · [Repeated-wire enumeration and controls](fan/README.md) · [Residual checks and replay instructions](prefix/README.md)

The following two additional checks use Python 3.11+ from the workspace root. The first reads the formula and proof directories described in the [replay instructions](prefix/README.md). The second takes the five-line enumeration produced by the [repeated-wire run](fan/README.md).

```sh
d=work/grid/repair_three/shared13/eight
cache=./cache
python3 -B "$d/check_certificates.py" --cache "$cache"
python3 -B "$d/check_repeated_line.py" "$cache/L-meta-8277-eight-fan/raw.tsv"
```

At nine mixing gates, ten incoming wires would give a tree, nine would allow one extra read, and eight would allow two extra reads. These are open cases. The general 28-gate grid also remains open.
