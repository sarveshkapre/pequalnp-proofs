# Eight mixed gates with one wire read twice

In both grid shapes a shared block of at most thirteen gates cannot pass if exactly eight of its gates mix point and line information and one wire in that mixed part is read twice. The four pairs belonging to each row may enter the answer through different gates.

| Shape | Expressions passing the first singleton tests | Distinct constraints before relabeling | Classes after relabeling | Classes needing SAT | Verified contradictions |
| --- | ---: | ---: | ---: | ---: | ---: |
| Common line | 5,983 | 1,113 | 197 | 20 | 20 |
| Triangle | 5,892 | 1,048 | 167 | 9 | 9 |

The first column counts representative pairs of AND/OR expressions with a marked shared wire. Different expressions can calculate the same function. [Enumeration counts](counts.txt) · [Profile counts](classes.txt) · [Line cases](prefixes.json) · [Certificate hashes](../prefix/fan-verify-results.json)

## Why the enumeration covers the branch

The eight mixed gates are the live gates reached by both a point and a line. Cut at each pure point or pure line signal entering these gates. Sixteen operand pins are filled by the seven mixed gates below the output and by the entering signals. If exactly one wire feeds two pins, there are eight distinct entering signals. At least three are point wires and at least five are line wires, so those counts are exact. The preceding [pure-line separation bounds](../../profiles/README.md) apply even if the circuit uses fewer than thirteen gates.

The three singleton points need incomparable three-bit codes on the point wires. Up to renaming the points and wires, the only choices are the three unit vectors or their complements. In the complementary assignment, each of the three point wires accepts two singleton points. None can be a raw point, so preparing them takes at least three gates. That leaves at most two line gates. The separation bound then requires at least six entering line signals, while this branch has five. For unit vectors we allow five line gates and impose no further cost for the point signals. Multi-point behavior is unrestricted.

Choose the unique wire read twice. Below it lies a tree; every other wire is read only once. No proper descendant feeding it can also feed the outside. Divide the circuit into a lower expression computing the shared wire and an upper tree using its output twice. A shared boundary point or line is a single-leaf lower expression. The upper tree uses two occurrences of a special leaf with that same value. This also permits both occurrences to enter the same gate. The lower and upper trees partition the three ordinary point leaves and five ordinary line leaves.

The [generator](enumerate.cpp) partitions each tree's leaves between its two children and tries AND and OR for every internal node that contains both input kinds. A shared mixed wire supplies both kinds to its upper tree. Children are ordered once using commutativity. All assignments of distinct point names differ only by renaming the three rows; all assignments of distinct line-wire names differ only by permuting the five cut wires. Thus the three point leaves and five line leaves can be numbered as they are encountered, with the lower tree visited first. Both original shapes have the same multiplicities under every row permutation, and the enlarged line-source bank and preparation rules respect this symmetry. These steps yield 1,160,032 expression pairs.

For all 32 line codes, evaluate the expression with zero points and then with each singleton point. For an incident-row set M, record all codes giving exactly M and giving zero with no points. A physical singleton line of that type could use any recorded code, even a different code from another line of the same type. The unselected line input must give zero for every point choice. Every type occurring in the physical shape needs a nonempty code set.

The [classification](classify.py) replays each distinct constraint's representative with separate scalar Boolean evaluation, then relabels rows and wire names. If all three row line masks can be recovered from the five cut wires in three additional line gates, the hypothetical five-gate preparation would give row masks in eight gates. The [earlier nine-gate lower bound](../../../line/README.md) excludes that. Every such recovery uses one wiring on all allowed codes and is independently evaluated. The 29 classes left after recovery are passed to the five-gate line-prefix search, which grants any free mask meeting each row in at most one line. Lean checked every residual contradiction. The topology coverage, projection, and classification are written arguments and executable enumerations.

## Checks and replay

An independent labeled DAG enumerator from the previous six- and seven-mixed-gate runs reproduces the complete canonical class sets when the line width is reduced to three and four. For all 20 physical triples we built larger controls with exactly eight mixed gates, three point and five line wires, and one repeated wire. The first kind repeats the point across two branches covering different pairs. The second kind repeats the output of an AND, then divides its pairs between those branches. All 40 circuits pass all 177 tests. These controls use seventeen block gates and sit outside the thirteen-gate lower-bound budget. [Checks](check.py) · [Output](controls.log)

From the workspace root with Python 3.11+ and a C++17 compiler:

```sh
d=work/grid/repair_three/shared13/eight/fan
scratch=$(mktemp -d)
c++ -std=c++17 -O2 "$d/enumerate.cpp" -o "$scratch/fan"
"$scratch/fan" 5 "$scratch/raw.tsv"
python3 -B "$d/classify.py" "$scratch/raw.tsv" "$scratch/prefixes.json"
cmp "$scratch/prefixes.json" "$d/prefixes.json"
python3 -B "$d/check.py" "$scratch/fan"
python3 -B "$d/../prefix/verify.py" fan-verify "$d/prefixes.json"
```

The final command uses the unpacked certificate directory `./cache` described in the root README. The [prefix solver](../prefix/solve.py) can produce the certificates on a fresh machine.
