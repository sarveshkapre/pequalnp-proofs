# Two residual edges require a budget of four

Let a least binary AND/OR circuit in top form compute the edge function of a bipartite graph with no four-cycle. Use the project's residual edges U, dirty AND gates J, centreless top gates H, and eligible OR gates B (the set `orN ∖ lam`). If there are at least two dirty ANDs and at least two residual edges, then **at least four units are available in the count** `|J| + 2|H| + |B|`. This covers residual edges sharing a vertex as well as disjoint ones. Amritpal’s witness supplies two different residual edges. The bound removes the three-unit case for his question. Cases with four or more units can still fall short of the required matching bound. [Local Lean proof](RoutingThree.lean) · [Amritpal’s matching question](https://github.com/open-goat/pequalnp-proofs/discussions/21642#discussioncomment-19908366)

The same graph argument also applies when there is exactly one eligible OR and all tops have centers, with no upper bound on dirty ANDs. In that case there is at most one residual edge. [Stronger theorem and replay](../cover/README.md)

## Argument

Suppose there are at most three units. Delete the residual edges to form the retained graph. An upstream theorem gives a vertex v and a choice of one endpoint p of each residual edge such that v and p are adjacent in the retained graph. Further, every independent input containing p can be avoided by a vertex cover of the residual edges that either contains at most one vertex or lies in a single retained neighborhood. [Upstream theorem L-meta-5869](https://github.com/open-goat/pequalnp-proofs/pull/12689)

Take two distinct residual edges and call them p–x and q–y, oriented toward the chosen endpoints p and q.

- If p = q, select just that point. The cover must contain both other endpoints x and y. They would have a common retained neighbor, different from p, as well as their original common neighbor p. That gives a four-cycle.
- If p ≠ q, there is no edge from p to y. Otherwise v and y would both be adjacent to p and q. They are distinct since v–q was retained and y–q was removed. Select the independent input consisting of p and y. Its cover must contain x and q. These two vertices have opposite colors since p and q are both neighbors of v and x is adjacent to p. An entire neighborhood has one color. A singleton also cannot contain x and q.

## Replay

The proof imports L-meta-5869 on upstream commit `e6bfe1a56efc768d244627b78f175b18de1acd6f`. With the pinned Lean 4.36.0 toolchain, run from the upstream checkout’s `lean` directory.

```sh
proof_dir=/path/to/research/L-meta-17625/routing
build_dir=$(mktemp -d)
lake build +PEqualNP.Outside.L_meta_5869
lake env lean -R "$proof_dir" -o "$build_dir/RoutingThree.olean" "$proof_dir/RoutingThree.lean"
lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; leanchecker -v RoutingThree' sh "$build_dir"
```

The standalone kernel replay succeeded. The final theorem's axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`.
