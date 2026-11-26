# Vertex covers, residual edges, and the matching inequality

A residual edge has no top AND with its two endpoints in opposite raw-input sides. In this note a top means an AND whose output always implies that the graph contains an edge. When a top has nonempty raw inputs on both sides, the absence of four-cycles forces at least one side to be a singleton. Its vertex can serve as a center for the old edges, the edges left after deleting the residual ones.

**The order-three plane.** The at-most-three boundary here is prior work from [PR #12606](https://github.com/open-goat/pequalnp-proofs/pull/12606). The [four-edge extension](../plane/PlaneBound.lean) includes the full-star case. A least top-form circuit for the 26-vertex incidence graph with at most three residual edges needs at least 64 gates. This covers arbitrary sharing, any number of dirty AND gates and all choices of the three edges. There are 52 incidences and each vertex meets four. At least 49 incidences survive three deletions, so at least 13 vertices are needed to cover them. The upstream gate count then pays for all three residual edges when there are at least two dirty AND gates. A nonempty residual set supplies a centreless top or an eligible OR. If there is only one dirty AND, an earlier theorem already supplies the required cover. With zero dirty ANDs the residual set is empty. The proof uses the exact order-three graph from the upstream reduction and specializes directly to the matching inequality. [General and plane proofs](ResidualDegree.lean) · [Repeated wire reads](RepeatCharge.lean) · [Upstream gate count](https://github.com/open-goat/pequalnp-proofs/blob/e6bfe1a56efc768d244627b78f175b18de1acd6f/lean/PEqualNP/Outside/L_meta_1491.lean) · [One dirty AND](https://github.com/open-goat/pequalnp-proofs/blob/e6bfe1a56efc768d244627b78f175b18de1acd6f/lean/PEqualNP/Outside/L_meta_8103.lean)

**Any graph with no four-cycle.** Suppose there are three residual edges and all tops have centers. Write J for the number of dirty ANDs and B for the number of OR gates in `orN ∖ lam`. Both assignments (J,B) = (2,3) and (3,2) satisfy the desk's exact repeated-wire inequality for every matching. In either case failure would force the minimum vertex-cover size to be the number of tops plus three. Then every choice of one endpoint per residual edge, together with the top centers, gives a minimum cover. Removing any center exposes an old edge unique to its top. As a result, the complementary independent input contains a leaf of every top. This step works for any number of residual edges. The [routing argument](../shared/ExtremalRouting.lean) uses these inputs to contradict the stated gate counts. [Extremal cover lemma](ExtremalCover.lean) · [Matching-to-cover transfer](MatchingTransfer.lean) · [Exact wire inequality for both cases](ThreeBranches.lean)

**One centreless top.** With three residual edges, two dirty ANDs, one centreless top and one eligible OR, the desk inequality holds for every matching. The proof handles the case in which several tests depend on the same eligible OR. [Repeated-read inequality](../routing/CentreTransfer.lean) · [Routing proof](../routing/README.md)

The combined theorem proves that failure on three residual edges requires exactly two dirty ANDs, zero centreless tops, and two eligible ORs. [Remaining case](GeneralThree.lean)

**One eligible OR.** If a bipartite graph has no four-cycle and all tops have centers, one eligible OR permits at most one residual edge, regardless of how many dirty ANDs there are. The common-neighbor construction from L-meta-5869 only uses the uniqueness of this OR after the initial resource count. The separate graph argument rules out both disjoint and intersecting pairs of residual edges under that routing condition. [Unrestricted dirty-AND count](OneExceptionalOr.lean) · [Graph argument](../routing/README.md)

**Limit of the cover argument.** With one unit of slack, there may be no protected pair of residual edges. The example has 18 vertices, minimum degree two, and two six-cycles. Its minimum cover has size nine. After deleting three disjoint residual edges, seven centers suffice and seven are necessary. The two remaining residual edges avoiding all these centers are 1–10 and 2–11. Both vertices 1 and 2 can be selected together, but any independent set containing them must avoid 10 and 11, the only leaves of center 0. Thus the proof using transversals needs additional circuit information in the (2,2) case. [Graph and checked obstruction](SlackExample.lean)

## Replay

Use upstream commit `e6bfe1a56efc768d244627b78f175b18de1acd6f` and its Lean 4.36.0 toolchain. Run the following in the upstream checkout’s `lean` directory, with `src` set to this project's `research/L-meta-17625` directory. The checked source does not require temporary compiled files from our machine.

```sh
src=/path/to/research/L-meta-17625
dest=$(mktemp -d)
lake build +PEqualNP.Outside.L_meta_1491 +PEqualNP.Outside.L_meta_8005 \
  +PEqualNP.Outside.L_meta_8103 +PEqualNP.Outside.L_meta_5869 +PEqualNP.Outside.L_meta_7465
lake env sh -eu -c '
  export LEAN_PATH="$2:$LEAN_PATH"
  for entry in cover/ResidualDegree cover/RepeatCharge cover/MatchingTransfer \
               cover/ExtremalCover shared/SwitchCore shared/SharedSwitch shared/ProtectedTriple \
               shared/ExtremalRouting cover/ThreeBranches routing/RoutingThree \
               cover/OneExceptionalOr cover/SlackExample shared/CentreSwitch \
               routing/CentreSeparation routing/OrdinaryExtremal routing/CentreTransfer \
               shared/SourceBudget cover/GeneralThree; do
    mod=${entry##*/}
    source_dir=$1/${entry%/*}
    lean -R "$source_dir" -o "$2/$mod.olean" "$source_dir/$mod.lean"
    leanchecker -v "$mod"
  done
' sh "$src" "$dest"
```

The local source compilation and standalone replay succeeded. The printed axiom audits list only `propext`, `Classical.choice`, and `Quot.sound`.
