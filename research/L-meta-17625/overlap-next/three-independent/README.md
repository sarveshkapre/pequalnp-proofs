# The repeated-read bound for three disjoint residual edges

Amritpal Nijjar asked whether wire reuse could defeat the proposed count when three graph edges remain after accounting for the ordinary top gates. The new case consists of three edges on six distinct vertices. Combining it with the earlier connected and two-touching cases gives the inequality for **every shape of exactly three residual edges**. [Amritpal’s question](https://github.com/open-goat/pequalnp-proofs/discussions/21642#discussioncomment-19908366) · [Final Lean statements](ThreeMatchingBound.lean)

## Concurrent public proof

Amritpal Nijjar posted the first public proof of the disjoint-edge theorem while our independent proof was being rebuilt. His reduction uses four six-bit masks and two reachability flags. The proof in this directory uses six gate orders and explicitly models which earlier wires each gate reads. Both routes close the same case. His pinned theorem `matching_forces_three_or` is stronger in another direction. At any residual size, if there are exactly two ANDs that can fire on an edge-free input, every top has a centre, and the residual set contains three disjoint edges, then at least three exceptional ORs are necessary. His team subsequently showed that, with exactly two dirty ANDs, no centreless top and exactly two exceptional ORs, a four-edge residual must be a star. Whether a least circuit realizes that star and the full repeated-read inequality remain open. [Four-edge update](https://github.com/open-goat/pequalnp-proofs/discussions/21642#discussioncomment-19912596) We separately checked his published CNF and certificate with a local proof checker. It derived the empty clause at step 8,847 from 5,832 clauses on 1,633 variables. His team reports replaying his physical circuit reduction in Lean. Our end-to-end Lean replay below checks the independently developed reduction in this directory. [Amritpal’s public hand-back](https://github.com/open-goat/pequalnp-proofs/discussions/21642#discussioncomment-19911352) · [His pinned sources and replay](https://github.com/Amritpal-Nijjar/pequalnp-proofs/tree/694c3b11cae7c3b398821d768ea817e933719114/research/disjoint-edges-and-five-inputs/disjoint)

[Independent check of Amritpal’s certificate](search/contributor-certificate.log)

## What is counted

Let $G$ be a finite bipartite simple graph with no four-cycle. The circuit is a smallest fan-in-two monotone AND/OR circuit computing whether the selected vertices contain an edge of $G$, in the project’s top form. An edge is *residual* if its endpoints never reach opposite inputs of the same top AND through ORs alone. The matching in the inequality may use any edges of $G$. The graph can have arbitrarily many other vertices and ordinary edges.

```text
number of graph edges + matching size − distinct raw input wires read
    ≤ total operand occurrences − distinct operand wires read
```

Lean uses natural-number subtraction. Both sides count across the entire circuit. On the right, a wire read three times contributes two repeated reads, including when a gate reads the same wire twice. The conclusions are `ThreeMatchingBound.pairwise_disjoint` for the new shape and `ThreeMatchingBound.all_three` for all shapes. The case of more than three residual edges in the general repeated-read question remains beyond these theorems. [Counting definition](../../cover/GeneralThree.lean)

## Why six vertices suffice

1. An earlier counting result forces any failure to have exactly two ANDs that can turn on for an edge-free selection, two exceptional ORs, and an ordinary star at every top. At least two matched residual edges avoid all the chosen star centres. Label the three disjoint edges $L_0R_0, L_1R_1, L_2R_2$, with the first two avoiding the centres and the letters giving the bipartition. [Counting result](../../cover/GeneralThree.lean) · [Labelling](geometry/MatchingLabels.lean)
2. Every ordinary edge touches a chosen centre. Among the six vertices, any ordinary edge must therefore meet $L_2$ or $R_2$. For each $i=0,1$, the possibilities are $L_iR_2$, $L_2R_i$, or neither. Having both would form a four-cycle with the two diagonal edges. This leaves **nine labelled graphs**. The no-four-cycle assumption also limits which vertices an ordinary gate can collect through ORs. For example, if $L_2R_0$ exists, $L_0$ and $L_2$ already share neighbour $R_0$. Putting them in the same ordinary star would require a second common neighbour, since $L_0R_0$ is residual. [Graph and raw-input restrictions](geometry/MatchingBridge.lean)
3. Turn off all vertices outside the six. For each diagonal edge choose one top AND that accepts its two endpoints. The same top can be chosen more than once. Each chosen top must reject every independent selection of the six vertices. The circuit reduction keeps direct reads, shared earlier gates and repeated operands. It also records when a wire receives a raw input outside the six, even though that input is zero on these tests. [Gate representation](circuit/MatchingPhysical.lean) · [Accepting tops](MatchingTerminals.lean)
4. The two ANDs and two ORs have **six possible operation orders**. For each order, one Boolean contradiction covers the graph choices and all permitted operands. Three positive pairs and ten candidate negative selections suffice. A negative test applies only when its selection is independent in the particular graph. For each order, Lean translates the Boolean test on its actual operands to clauses and checks an LRAT contradiction certificate. The finite result therefore applies directly to the circuit reduction. [Test selections](search/MatchWindow.lean) · [Finite exclusion](search/MatchExclusion.lean) · [Physical circuit reduction](ThreeMatchingReduction.lean)

## Controls

One control drops the common-neighbour restriction on two raw operands. With those operands available, the four-gate arrangement reproduces all 64 inputs of the graph with the single extra edge $L_2R_0$. This identifies a geometric restriction the proof needs. A second control uses three ANDs and three promotion ORs and computes the projected matching on all 64 inputs when there are no extra edges. Both constructions live in the six-vertex model. [Control statements and constructions](search/MatchControls.lean)

## Sources and replay

The proof builds on the project’s circuit definitions and routing lemmas, Amritpal’s matching question, and the earlier hand-backs. The earlier modules are included on this branch. Their previous publication is pinned at commit `8ad50440ecd2520a5e3c727f7b1a19f079cac700`. The current addition supplies the six-vertex reduction, finite exclusion and the final exactly-three conclusion. [Earlier proof sources](https://github.com/sarveshkapre/pequalnp-proofs/tree/8ad50440ecd2520a5e3c727f7b1a19f079cac700/research/L-meta-17625) · [Earlier hand-back](https://github.com/open-goat/pequalnp-proofs/discussions/21642#discussioncomment-19910607) · [Upstream routing proof](https://github.com/open-goat/pequalnp-proofs/pull/14942)

Use a prebuilt upstream checkout at `e6bfe1a56efc768d244627b78f175b18de1acd6f` with its pinned Lean 4.36.0 toolchain and Mathlib. From `research/L-meta-17625` on this branch, run the following on macOS

```sh
python3 overlap-next/three-independent/replay.py /path/to/prebuilt-upstream ThreeMatchingBound MatchControls
```

The clean local replay rebuilt all 86 research modules from source against the pinned prebuilt upstream imports. The standalone checker replayed the 24 certificate modules, the final theorem module and the control module. Both final theorems use only the following axioms. [Complete replay log](verification.log)

```text
'ThreeMatchingBound.pairwise_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'ThreeMatchingBound.all_three' depends on axioms: [propext, Classical.choice, Quot.sound]
```
