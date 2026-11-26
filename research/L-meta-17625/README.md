# A partial answer to the repeated-wire question

*Written by GPT-6.2 Astra in Codex on behalf of Sarvesh Kapre.*

Amritpal asked whether a circuit can reuse an OR gate in a way that defeats a count of repeated wire reads. His first open case had three residual edges. We get two results. The Lean sources use the project's circuit and graph definitions throughout. [Amritpal's question](https://github.com/open-goat/pequalnp-proofs/discussions/21642#discussioncomment-19908366) · [Upstream definitions](https://github.com/open-goat/pequalnp-proofs/blob/e6bfe1a56efc768d244627b78f175b18de1acd6f/lean/PEqualNP/Defs/TopForm.lean)

## Every graph with no four-cycle

With exactly three residual edges, the proposed inequality holds for every matching except possibly in one gate configuration. A matching is a set of edges with no shared endpoint. A residual edge is one that no top AND recognizes directly by receiving its two endpoints on opposite inputs through OR gates alone.

For the inequality to fail, **all** the following must hold.

- Exactly two AND gates turn on for some input containing no edge. The project calls these dirty ANDs.
- Every top AND has a raw input vertex on both sides. Exactly two OR gates belong to the exceptional set that the project's counting argument keeps separately, `orN ∖ lam`.
- As Amritpal observed, the matching uses at least two residual edges. If there are *t* top AND gates, the matching and a smallest vertex cover both have size *t* + 2. The circuit has exactly the number of graph edges plus *t* gates.

These are necessary conditions. Whether such a circuit and matching can violate the inequality remains open. The theorem allows arbitrary sharing and applies to least circuits in the project's top form. The number of ordinary vertices and the total number of gates are unrestricted. [Exact theorem and tight counts](cover/GeneralThree.lean)

The counting idea is to test the shared circuit on whole inputs. The upstream 11-vertex proof already uses eight independent inputs for an induced matching. Here the graph argument constructs the needed inputs under a minimum-cover hypothesis on an arbitrary graph with no four-cycle. [Earlier 11-vertex proof](https://github.com/open-goat/pequalnp-proofs/pull/11107)

In the case where a cover needs one extra vertex for every residual edge, take all eight ways to choose one endpoint from each of three edges. The graph argument produces an independent input containing each choice. For a gate that is off, record which input keeps it off. Reusing a wire then uses the same recorded decision everywhere. Too few different records contradict the fact that the circuit accepts each edge. One exceptional case with a centreless top uses a stronger version in which a recorded bit is forced. When a cover has one spare vertex the eight tests need not exist. A checked graph example shows exactly where that argument stops. [Cover argument](cover/ExtremalCover.lean) · [Shared-wire argument](shared/README.md) · [Example with one spare vertex](cover/SlackExample.lean)

## The full order-three projective plane

This graph has 13 points, 13 lines, and 52 incidences. If at most four incidences are residual in a smallest circuit in top form, the circuit needs **at least 64 gates**. In particular, an arbitrary circuit of 63 gates or fewer computing the full incidence function could be put in least top form only with at least five residual incidences. The original circuit may have AND/OR gates with at most two inputs and any amount of wire sharing. The project's normalization puts it in the exact-two-input model before counting residual incidences. The unrestricted 63-gate existence question remains open. [Full theorem](plane/PlaneBound.lean) · [Exact coordinate and circuit-model checks](plane/PlaneDesk.lean) · [Upstream normalization theorem](https://github.com/open-goat/pequalnp-proofs/blob/e6bfe1a56efc768d244627b78f175b18de1acd6f/lean/PEqualNP/Outside/L_meta_4181.lean)

Robert Penner's merged reduction already handled up to three residual incidences and singled out four or more. Our extension closes the entire four-incidence case, including the star. A later plane proof also handles a weighted gate budget of at most three. The critical four-edge arrangement has budget four. The general routing arguments reuse the upstream proof filed under an 11-vertex question. [Previous plane reduction](https://github.com/open-goat/pequalnp-proofs/pull/12606) · [Earlier budget bound](https://github.com/open-goat/pequalnp-proofs/pull/22541) · [Upstream routing proof](https://github.com/open-goat/pequalnp-proofs/pull/14942)

With three or fewer residual incidences, at least 49 incidences remain. Each point or line meets only four, so covering them takes at least 13 vertices. With four residual incidences spread over more than one point or line, a checked list of matchings gives the same bound. The upstream gate accounting finishes both cases. [Degree argument](cover/ResidualDegree.lean) · [Matching proof](plane/FourEdges.lean)

The difficult arrangement has all four residual incidences at one point, or all four at one line. A budget of 63 gates would force twelve ordinary stars, two dirty ANDs, and two exceptional ORs. The remaining 48 incidences determine the twelve stars. Each of the four missing incidences must turn on a dirty AND that was off with just their common vertex selected. Under the available OR budget, two different incidences cannot have the same first such AND. Four distinct gates are needed, and only two are available. [Gate budget](plane/PlaneBudget.lean) · [Twelve forced stars](plane/StarGeometry.lean) · [OR budget](plane/StarPromotions.lean) · [First changing gate](plane/StarGrowth.lean)

## Replay

Use upstream commit `e6bfe1a56efc768d244627b78f175b18de1acd6f`, its pinned Lean 4.36.0 toolchain and dependencies, and Python 3.9 or later. Download this directory from the fork. From that copy, run the command below with a separate checkout of the pinned upstream commit.

```sh
python3 replay.py /path/to/pequalnp-proofs
```

The script builds the upstream imports, compiles the local proofs into an empty temporary directory and runs Lean's standalone kernel checker on the named conclusions. For just the two main results, append `PlaneDesk GeneralThree` to the command. The axiom audits of both conclusions list only `propext`, `Classical.choice`, and `Quot.sound`. The full statement of L-meta-17625 remains open in this work. [Verification log](verification.log) · [General desk entry](https://pequalnp.com/desk/row?gap=L-meta-17625) · [Related upstream reduction](https://github.com/open-goat/pequalnp-proofs/pull/22707)
