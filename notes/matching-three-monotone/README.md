# Three-by-three bipartite perfect matching needs 14 monotone gates

A circuit deciding whether a 3×3 bipartite graph has a perfect matching needs **at least 14 binary AND/OR gates**, even when earlier gates can be reused without charge. Expanding along one row gives 14, so the bound is exact. The input consists of all nine edge bits, with all 512 graphs allowed. Circuits allowing NOT are a separate question. This finite result answers the mathematical question in the opposite direction to the posted search. [Exact desk statement](https://pequalnp.com/desk/row?gap=L-meta-17390)

The project supplied the upper construction. Kr1tya3 reported an inconclusive 13-gate search. An independent team verified the upper construction and reported progress on smaller circuits. Our contribution is a computer-assisted lower bound using restrictions of the input graph. The argument below and two independent Python implementations establish the lower bound. Lean checks the upper construction. An end-to-end Lean proof of the lower bound is still open. [Earlier search](https://github.com/open-goat/pequalnp-proofs/discussions/21642#discussioncomment-19924862) · [Independent research report](https://imd-explorer.up.railway.app/jobs/71f09f9e-5878-4ff3-bfb7-97af5d716e09)

## Why fixing one edge suffices

Fix any edge as present. The remaining eight-input function still needs **12 gates**. This is the main finite calculation.

In a minimum circuit, some raw edge must feed at least two distinct gates. Otherwise the first gate would be the only reader of its two input edges. Swapping those two inputs would preserve every circuit output. No pair of edges has this property. Take a perfect matching containing the first edge and omitting the second. Such a matching exists for every pair. Replacing just that edge by the other one destroys the matching. The two graphs have opposite answers.

Now fix a repeatedly read edge to one. Each gate directly reading that edge simplifies to a constant or to its other operand. This deletes at least two gates. All nine choices of the fixed edge are equivalent by row and column permutations. The original size is therefore at least 12 + 2.

## How the finite lower bound works

Work with the truth table of a monotone function f. Discard unused gates and inputs irrelevant to f. A nonconstant minimum circuit can be written as a list of useful binary gates on earlier wires. Empty AND and OR gates are constants. A one-input gate is a copy. The project's unavailable-wire reads give false. Propagating these values, removing copies and merging identical truth tables cannot increase the cost. This converts the desk's full semantics to the model searched here. [Circuit semantics](https://github.com/open-goat/pequalnp-proofs/blob/25c55a36c4067dc5502519907ec2a1c393f9e8f3/lean/PEqualNP/Defs/CircuitLowerBounds.lean) · [Monotone gate definition](https://github.com/open-goat/pequalnp-proofs/blob/25c55a36c4067dc5502519907ec2a1c393f9e8f3/lean/PEqualNP/Defs/MetaComplexityLgpMono.lean)

The verifier inducts on the number of essential input variables. A function depending on n inputs already needs at least n−1 binary gates. Its output dependency graph must connect all n input vertices. To improve this bound, enumerate every possible beginning of a minimum circuit, up to four gates. Stop a branch as soon as a restriction of one or two inputs certifies the desired lower bound. If an unexplained prefix survives to depth four, the verifier declines that improvement. If the output appears earlier, it checks the actual prefix length.

For a fixed prefix and a restriction that leaves a nonconstant function, three contributions add.

1. The restricted function has a lower bound already established on fewer essential inputs. Further irrelevant inputs may be fixed arbitrarily.
2. Count prefix gates whose restricted truth tables are constants, raw wires or duplicates of earlier restricted signals. Each such gate can be removed.
3. Count how many distinct wires that become constant must pass from the prefix or raw inputs into the remaining circuit. Each such wire guarantees at least one more removable gate in the remaining circuit.

For the third count, any prefix gate with no reader inside the prefix must be read later. In addition, the wires read by the remaining circuit must distinguish every minimal positive input from every maximal negative input of the **original** function. For each such pair, at least one crossing wire must take value one on the positive input and zero on the negative input. Otherwise monotonicity of the remaining circuit gives a contradiction. Allow every nonconstant crossing wire for free, include all mandatory constant wires, then try every small subset of optional constant wires. If none separates every pair, more constant crossing wires are necessary.

Here is why two constant wires feeding the same gate are counted correctly. Mark one live occurrence to follow for each distinct required constant wire. Process the remaining gates in order. A gate reached by one mark disappears under constant propagation and pays for that mark. A gate reached by two marks also disappears. Its output is constant, so it pays for one mark and carries the other to a later reader. A live intermediate wire has such a reader. A nonconstant final output cannot carry a mark. Every mark therefore pays for a different removed gate. These gates are disjoint from the eliminated prefix gates.

The first implementation groups restrictions related by permutations of rows and columns or by transpose. The second visits every labeled function and enumerates separating subsets independently. Neither needs symmetry or memoization of gate prefixes. The known upper bound uses four binary gates for each first-row choice, then two OR gates to join the three possibilities.

## Reproduce the result

With ordinary Python 3.10 or later, run these files from this directory. Both use only the standard library and have no network or external solver dependency.

```sh
python3 -I verify.py
python3 -I independent.py
```

The first visits 56 restriction classes. The second visits 1,665 labeled restrictions. Both report lower bounds of 9 with one edge absent, 12 with one edge present, and 14 for the full function. The upper circuit passes all 512 inputs. As a separate control we compared the restriction method with exhaustive gate enumeration for all 168 monotone functions on four inputs. It never exceeded the independently computed minimum.

[Primary verifier](verify.py) · [Independent verifier](independent.py) · [Four-input control](control.py) · [Upper construction in the project model](Upper.lean)

## Lean verification and remaining work

Lean 4.36.0 and the upstream checker at revision `e6bfe1a56efc768d244627b78f175b18de1acd6f` accepted the 14-gate construction against the [exact statement](Upper.statement). The checker rechecked 1,680 constants and reported `propext` and `Quot.sound`. To reproduce that local harness verdict in a pinned checkout with its ordinary dependencies available, copy `Upper.lean` into `lean/PEqualNP/Outside/` and run the following from the repository root, substituting the location of this note for `NOTE`.

```sh
node tools/check-lean.mjs lean/PEqualNP/Outside/Upper.lean "$NOTE/Upper.statement" check
```

The key counting step also has a generic Lean proof. [Frontier.lean](Frontier.lean) proves the Boolean simplifications and counts eliminated gates. [Discharge.lean](Discharge.lean) proves that the marks are exhausted for a live, well-ordered circuit whose restricted output is nonconstant. Lean and the separate kernel checker replayed `RestrictedGateFrontier.live_frontier_bound` using only `propext`, `Classical.choice` and `Quot.sound`. With pinned Lean on the path, run the following from this directory.

```sh
LEAN_PATH=. lean -o Frontier.olean Frontier.lean
LEAN_PATH=. lean -o Discharge.olean Discharge.lean
LEAN_PATH=. leanchecker Discharge
```

For a single kernel theorem refuting the desk statement, the outstanding work is to connect the project's circuit representation and the finite prefix-and-restriction checker to this accounting lemma. The published Python checks already cover circuits with sharing. This packaging step matters for official submission.
