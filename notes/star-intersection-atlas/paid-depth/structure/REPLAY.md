# Replay the complementation proofs

The proof sources and the controls are pinned to commit `ed2ef8e56e017d9e6b939f79d2ecdc5e70746eae` on the fork’s `paid-depth-tradeoff` branch. In a dedicated local checkout, select that revision and prepare the repository’s pinned Lean 4.36.0 toolchain and matching Mathlib cache. Run the checks from the repository root in an isolated environment with the network disabled.

```sh
for name in SeparatorComplement FormulaTraceBound MatchedPrefix
do
  node tools/check-lean.mjs "lean/PEqualNP/PaidDepth/$name.lean" \
    "notes/star-intersection-atlas/paid-depth/structure/$name.statement" check || exit 1
done
python3 -IB notes/star-intersection-atlas/paid-depth/structure/check_separator.py
python3 -IB notes/star-intersection-atlas/paid-depth/structure/check_order.py
python3 -IB notes/star-intersection-atlas/paid-depth/structure/check_unrestricted.py
```

**SeparatorComplement** checks the equivalence on every row-column pair of an arbitrary acyclic source satisfying the specified separator condition. Its rectangular factors have one ternary signature per boundary and one binary choice per interior gate. **FormulaTraceBound** checks the integer trace inequality on the entire inductively generated class of formula forests. The balanced ordering, the resulting sharp exponential law, and the treewidth and reuse corollaries have written proofs in [THEOREM.md](THEOREM.md).

The first control compares the constructed relations with direct circuit evaluation in all 8,640 admissible three-gate wiring, partition and output cases on the 64×64 independent raw-input grid. It also checks 1,400 interleaved circuits through ten gates, the trace inequality on 146,600 ordered wirings through seven gates, and exact backward trace enumeration on 1,070 smaller wirings. The second control checks 8,536 rooted forests at two, four and eight blocks, including the integer weight and separator inequalities.

**MatchedPrefix** checks the local equivalence that moves a selected group of rejection requirements to a suffix label. Its quantifiers allow arbitrary reuse, overlapping kept and omitted sets, and both possible directions of dependency between the independent vertices and the other prefix gates. The probabilistic dictionary, counting and final 3/5 exponent appear in the [unrestricted proof](UNRESTRICTED.md). The last script checks eight rational endpoint inequalities using exact integer powers, exhausts the small-set projection expectations, and compares the construction against direct evaluation on 2,048 complete three-gate cases and 2,400 larger random cases.


## Official verification

The project verifier on macOS returned `ACCEPTED (check)` for each statement at the proof revision above, using Lean 4.36.0 with outbound networking disabled.

| Theorem under PEqualNP.PaidDepth | Kernel-rechecked constants | Axioms |
| --- | ---: | --- |
| SeparatorComplement | 1,672 | propext, Classical.choice, Quot.sound |
| FormulaTraceBound | 1,667 | propext, Quot.sound |
| MatchedPrefix | 1,660 | propext, Classical.choice, Quot.sound |

The verifier reported 87 source digests per check. All 89 distinct module digests across the three checks matched the pinned revision. The verdicts cover the three formal statements. The upper bounds on asymptotic cost also use the linked written proofs.
