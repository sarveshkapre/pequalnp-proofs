# The matching bound for three connected residual edges

**Question.** Amritpal asked whether the circuit's repeated wire reads can pay for all three edges left over after the ordinary top gates are counted. A residual edge is one whose two endpoints reach no top AND on opposite sides through ORs alone. The relevant circuits are smallest fan-in-two AND/OR circuits in the project's top form, on bipartite graphs without four-cycles. [Amritpal’s question](https://github.com/open-goat/pequalnp-proofs/discussions/21642#discussioncomment-19908366)

**Result.** If the three residual edges form a connected graph, the matching inequality holds. Equivalently, every failure would need one residual edge sharing no endpoint with the other two. [Connected-case theorem](matching/PathRemainder.lean)

**Path case.** Suppose the three edges are a–b, b–c, c–d on four distinct vertices. The matching inequality holds for every matching in the question, regardless of graph size or how often a wire is reused. In plain terms, the circuit must reuse enough wires to account for the graph edges and the size of the matching after crediting the distinct input wires it has read. The previous reduction allowed a failure only with two dirty ANDs, two exceptional ORs and no centreless top. Here a dirty AND is one that can fire on an input containing no edge. The two exceptional ORs are the ones still charged separately by the project's counting argument. [Theorem](matching/PathConclusion.lean) · [Previous reduction](../cover/GeneralThree.lean)

## Why the path matters

Select only from a, b, c and d. The circuit must accept whenever both ends of one of the three edges are selected. The three largest path selections containing no edge are {a,c}, {a,d} and {b,d}. The proof extends each of them to a negative input for the full graph. On these extensions the far input of every top AND is already on, so its center input has to stay off. On the three edge inputs, at least one center input must turn on. The same set of exceptional ORs feeding the centers therefore distinguishes the path's positive and negative inputs. [Graph argument](matching/PathGeometry.lean) · [ORs feeding the centers](matching/PathPromotion.lean)

In a failing circuit an ordinary OR used as an input to a charged gate could read at most one path vertex through ORs alone. An outside center touching two vertices on the same side of this path would make a four-cycle. The two-coloring rules out the other pairs. We can therefore replace each ordinary port by that one literal (possibly absent) together with any permitted earlier exceptional ORs. The encoding records whether a wire also reaches a raw vertex elsewhere in the graph. An input outside the path looks false on all 16 tests but can still supply that vertex. [Circuit ports](circuit/P4Ports.lean) · [Physical circuit encoding](path/PathSchedule.lean)

The finite calculation tries all six orders of the two ANDs and two ORs. It allows direct reads of earlier gates, including repeated reads. No order realizes the required values on all 16 inputs. A positive control shows the one-gate difference in this model. With a third OR, form a OR c, intersect it with b, separately form c AND d, OR the answers, then OR the result with an outside input. The last step supplies the outside raw vertex. [Finite proof](path/PathSearch.lean) · [Independent enumeration and control](path/test_model.py)

## Remaining shapes

A failing matching needs at least two disjoint residual edges. With three edges in a bipartite graph the other two possibilities are a pair of edges sharing an endpoint plus a separate edge, and three mutually disjoint edges. The proof above does not settle them. [Which edges can meet](matching/PathRemainder.lean) For the first shape the leaf input at a top can genuinely reach two selected vertices. Consider the six-vertex path c–b–a–x–d–e with residual edges ab, bc, de. The two edges incident to x can be covered by one star whose other side contains both a and d. This example shows why the one-vertex restriction in the path proof fails here.

There is also a way to fool the two negative tests available from minimum covers for this second shape. The expression b OR (d AND e) accepts every required edge and rejects both {a,c,d} and {a,c,e}. It also accepts b on its own. This is a witness in the projected model. An argument for this shape needs to explain how the actual circuit rejects b alone, or derive another test that catches the same mistake. There is a bound to use in that argument. In a bipartite graph, a vertex cover with one vertex more than the minimum can have at most two vertices with no neighbor outside the cover. If there are two, they must be adjacent. [Checked graph examples, test witness, and cover bound](circuit/DisconnectedGeometry.lean)

For three disjoint residual edges, a separate checked argument also rules out hiding either exceptional OR behind the other one. Each needs a path through ordinary ORs alone to a top AND input. Whether those two paths can coexist in a failing circuit remains open. [Proof for three disjoint edges](circuit/ActiveOr.lean)

## Replay

Use the upstream checkout at `e6bfe1a56efc768d244627b78f175b18de1acd6f`, Lean 4.36.0, the pinned Mathlib, and Python 3.10 or later. In a checkout of this fork, run the following from `research/L-meta-17625/overlap-next`. Pass a separate upstream checkout at the revision above, with its pinned dependencies available. The earlier proof modules are in the parent directory.

```sh
python3 replay.py /path/to/pequalnp-proofs PathRemainder
python3 path/test_model.py
```

The first command rebuilds the local dependencies and runs Lean's standalone kernel checker on the conclusion. The second uses only Python's standard library. The two earlier results have a [public reply](https://github.com/open-goat/pequalnp-proofs/discussions/21642#discussioncomment-19909204) and a [pinned proof package](https://github.com/sarveshkapre/pequalnp-proofs/tree/190e1dfe79b9e79336aa5a03ef871d6b06362b55/research/L-meta-17625). The clean rebuild and standalone kernel replay passed for this local follow-up. [Verification log](verification.log)
