# Two touching residual edges and one separate edge

Amritpal Nijjar asked whether repeated operand reads pay for the last three residual edges in the project's circuit-counting argument. The inequality holds when those edges are `ab`, `bc`, and `de` on five distinct vertices. Combined with the connected case, this leaves three pairwise vertex-disjoint residual edges as the only possible shape of a three-edge counterexample. [Amritpal’s question](https://github.com/open-goat/pequalnp-proofs/discussions/21642#discussioncomment-19908366) · [Earlier connected-case hand-back](https://github.com/open-goat/pequalnp-proofs/discussions/21642#discussioncomment-19909693)

## Exact scope

Let `G` be any finite bipartite graph without a four-cycle and `C` a smallest fan-in-two monotone AND/OR circuit for its graph function, in the project's top form. A residual edge is one whose two endpoints do not reach opposite sides of any top AND through ORs alone. The three specified edges exhaust the residual set. Other edges, vertices and wire reuse in the circuit are allowed.

Count every operand occurrence of every gate, including repeated uses of the same wire. For **every** matching in the question,

```text
number of edges + matching size − number of distinct raw inputs read
    ≤ number of operand occurrences − number of distinct operand wires read.
```

The Lean statement uses natural-number subtraction. Its two conclusions are `DisjointEdgeBound.two_touching_and_one_separate` and `DisjointEdgeBound.failure_requires_three_disjoint`. [Final declarations](projection/TwoTouching.lean)

## Proof

1. Suppose a matching violates the inequality. Earlier counts force exactly two AND gates that can fire on an edge-free input and exactly two exceptional OR gates. Equality in the matching count gives each top AND a distinct centre and a distinct matched neighbour. After exchanging the two path tips if necessary, the matching includes `ab` and `de`. [Matching argument](geometry/PrivateMatching.lean)
2. Restrict inputs to the five vertices. A direct input or an ordinary gate operand can carry one vertex, no vertex, or one of three pairs, `ad`, `cd`, `be`. For example, a star outside the path reaching both `a` and `c` would create a four-cycle through `b`. Only `c` can be a chosen centre among the five vertices. If it is a centre, the additional graph edge `ce` may be present. This gives three graph configurations. [Geometry](projection/ProjectionGeometry.lean) · [Orientation](geometry/NormalizeTips.lean)
3. A test input containing a residual edge must be accepted. An independent set must be rejected, including when it can be extended by a matched neighbour. Those extensions constrain what the two exceptional ORs can supply to top ANDs. Ten inputs suffice. Lean maps the gates and their operands in an arbitrary putative counterexample to fixed choices on these ten inputs, retaining direct reads, sharing and repeated reads. [Test inputs](projection/FiveFacts.lean) · [Circuit-to-test proof](projection/Realizability.lean)
4. In each configuration the two ANDs and two ORs have six possible orders. All 18 Boolean problems are impossible. Each of the 18 frozen LRAT certificates is converted to a Lean proof for the actual selector expression. Combining the exclusions with the circuit-to-test implication gives the inequality. Combining that theorem with the earlier connected result forces all three edges of a failure to be pairwise disjoint. [Finite exclusion](search/ProjectionExclusion.lean) · [Final theorems](projection/TwoTouching.lean)

For a concrete example of why the extra inputs matter, consider `b OR (d AND e)`. It accepts all three required edge inputs, and it rejects the two previously used independent sets `{a,c,d}` and `{a,c,e}` when `ce` is absent. Yet it accepts `{b,d}`, which contains no edge in any of the three configurations. The ten-input proof catches this error while also allowing valid uses of a shared intermediate wire.

## Replay

On macOS, use Python 3.9 or later, the Lean 4.36.0 toolchain and a **prebuilt** upstream checkout at `e6bfe1a56efc768d244627b78f175b18de1acd6f`, including its pinned Mathlib. Use two checkouts. Keep the published proof on the fork’s research branch, and pass the separate pinned upstream checkout to the replay script. Run the commands below from `research/L-meta-17625/overlap-next/disjoint` in the fork.

```sh
python3 -B replay.py /path/to/pequalnp-proofs
python3 -B audit/verify.py
```

The first command builds all local Lean dependencies from source in an empty scratch directory, with warnings treated as errors. It runs the standalone kernel checker on the 18 certificate modules and the final theorem module. Each Lean process sees only scratch, the prebuilt libraries, the toolchain and system libraries, with network access disabled. The pinned upstream imports are prerequisites. The expected axioms for both final declarations are `propext`, `Classical.choice`, and `Quot.sound`. [Replay log](verification.log)

The second command checks an independently written Boolean encoding with Python's standard library. It replays 18 contradictions and verifies three satisfying assignments with one extra OR, one for each graph configuration. A separate C++ implementation also exhausts all six orders on all 32 input subsets. The larger controls apply to the projected models. [Independent encoder](audit/encode.py) · [Enumeration and controls](search/enumeration.log)
