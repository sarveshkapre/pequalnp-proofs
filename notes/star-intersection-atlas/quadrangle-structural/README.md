# Why the 5×6 quadrangle needs four intersections

Pjscruggs found this graph, gave a four-intersection circuit, and supplied a SAT encoding and LRAT certificate ruling out three. He asked for a structural explanation of the same lower bound. This proof keeps his circuit model: a circuit starts with row and column stars, may take arbitrary unions for free, and pays one gate for each binary intersection. An earlier gate may feed both inputs of later computations. [Original discussion and construction](https://github.com/open-goat/pequalnp-proofs/discussions/19729) · [Earlier Lean replay of the SAT proof](https://github.com/open-goat/pequalnp-proofs/discussions/19729#discussioncomment-19910317)

[QuadrangleStructural.lean](QuadrangleStructural.lean) proves the following statements about pjscruggs’s graph, including the duplicate row in his square-grid definition.

```lean
QuadrangleStructural.lower_bound :
  ¬ QuadrangleHandoff.Represents 3 QuadrangleHandoff.graph

QuadrangleStructural.exact_minimum :
  QuadrangleHandoff.Represents 4 QuadrangleHandoff.graph ∧
    ∀ k, k < 4 → ¬ QuadrangleHandoff.Represents k QuadrangleHandoff.graph
```

## Why the shared gate fails

The proof works with the cells where a wire is zero. In this description a free union of input stars gives a rectangle, and taking a paid intersection of wires forms the union of their zero sets. The three-gate classification has five shapes. Four also occur as formulas. The fifth feeds the same intermediate result into two later gates. This distinction matters because the shared gate saves an intersection on a different 8×8 graph. [Three-gate classification and example](https://github.com/open-goat/pequalnp-proofs/discussions/23239)

In that fifth shape the shared result is the union of two rectangles. Fix the outer rectangle on each arm. The target graph then determines a set of cells the shared result must contain and a set it must avoid. Two required cells conflict if putting them in the same rectangle would force it to include a forbidden cell. Assigning the required cells to two rectangles is equivalent to coloring this conflict graph with two colors, provided the outer rectangles have a valid overlap. The reverse direction takes the rectangular hull of each color class and reconstructs both arms. The rectangle-cover/coloring correspondence is classical. [Exact reduction](QuadrangleSharedReduction.lean) · [Two-color equivalence](QuadrangleSharedColoring.lean) · [Pourmoradnasseri and Theis, Proposition 1.1](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v24i2p37/pdf/#page=2)

For this quadrangle, every admissible outer pair leaves three pairwise conflicting cells. Two rectangles can cover at most two of them. Lean checks a geometric certificate with 1,644 leaves. Of these, 1,401 exhibit a conflicting triple and 243 rule out an invalid outer overlap. The other four shapes are excluded separately, which completes the lower bound for arbitrary three-gate circuits. The argument uses no SAT or LRAT input. A geometric condition forcing these conflicts across a family of graphs remains open. [Geometric checker](QuadrangleSharedFinite.lean) · [Certificate](QuadrangleSharedFiniteData.lean) · [Final proof](QuadrangleStructural.lean)

## Replay

Use a checkout of this fork’s `quadrangle-5x6-structural` branch, Git, Python 3, and the Lean 4.36.0 toolchain selected by the repository. From its `lean/` directory, populate the pinned Lake dependencies and Mathlib cache if needed. Then run the proof replay.

```sh
lake exe cache get
python3 ../notes/star-intersection-atlas/quadrangle-structural/replay.py
```

With the dependencies cached, the second command works offline. It checks the Lean and Mathlib versions, builds all 20 modules in a fresh directory, checks their printed axiom reports, and runs Lean’s standalone kernel checker on each module. Six modules come from the earlier commits on this branch, including pjscruggs’s original handoff and two-intersection theorem. [Pinned contributor sources](https://github.com/pjscruggs/pequalnp-proofs/tree/7da7d81614b93ea808c11ac27f27136942fec385/notes/star-intersection-atlas)

ChatGPT Pro developed this structural proof. Codex independently replayed it offline on a Mac for Sarvesh Kapre. All 20 source builds, 20 standalone kernel checks, and 70 axiom reports passed. The final lower bound and exact minimum use only `propext`, `Classical.choice`, and `Quot.sound`. [Mac replay log](mac-replay.log)
