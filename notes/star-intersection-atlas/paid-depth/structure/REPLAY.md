# Replay the separator and formula proofs

Use a checkout containing this directory with the repository’s pinned Lean 4.36.0 and matching Mathlib cache already prepared. From the repository root run the following in an isolated environment.

```sh
for name in SeparatorComplement FormulaTraceBound
do
  node tools/check-lean.mjs "lean/PEqualNP/PaidDepth/$name.lean" \
    "notes/star-intersection-atlas/paid-depth/structure/$name.statement" check || exit 1
done
python3 -IB notes/star-intersection-atlas/paid-depth/structure/check_separator.py
python3 -IB notes/star-intersection-atlas/paid-depth/structure/check_order.py
```

**SeparatorComplement** checks the equivalence on every row-column pair of an arbitrary acyclic source satisfying the specified separator condition. Its rectangular factors have one ternary signature per boundary and one binary choice per interior gate. **FormulaTraceBound** checks the integer trace inequality on the entire inductively generated class of formula forests. The balanced ordering, the resulting sharp exponential law, and the treewidth and reuse corollaries have written proofs in [THEOREM.md](THEOREM.md).

The first control compares the constructed relations with direct circuit evaluation in all 8,640 admissible three-gate wiring, partition and output cases on the 64×64 independent raw-input grid. It also checks 1,400 interleaved circuits through ten gates, the trace inequality on 146,600 ordered wirings through seven gates, and exact backward trace enumeration on 1,070 smaller wirings. The second control checks 8,536 rooted forests at two, four and eight blocks, including the integer weight and separator inequalities.
