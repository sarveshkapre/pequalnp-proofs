# Projecting the path and isolated edge

Write the residual as `ab,bc,de`. In the tight counterexample regime the matching pairs `ab,de` can be chosen after exchanging `a,c`. Its remaining edges match the distinct chosen top centres `z` to distinct private leaves `y_z`. The centres avoid `a,b,d,e`. Orient the isolated edge so `a,c,d` have the same color. We use three modes. Either `c` lies outside the centres, or `c` is a centre and the extra edge `ce` is absent or present. Every nonresidual edge has a chosen centre as endpoint, so these modes exhaust the induced graph on the five vertices.

## From physical ports to the finite calculation

1. A charged gate is a dirty AND or an exceptional OR below an AND. Its operands may read earlier charged gates directly. Every other operand has nonempty global raw support. It computes its raw literals together with a fixed subset of earlier, globally raw-bearing exceptional OR signals whose raw supports are contained in that operand. This follows by the physical OR-path decomposition used for the connected path. The top operands themselves have nonempty raw support and use the same decomposition, including an operand that is itself exceptional.
2. On the five vertices, an ordinary charged-gate input is either a variable or supported within one ordinary star leaf. Such a leaf lies in one color class. It cannot contain both `a,c`: any common neighbor besides `b` makes a four-cycle, and a raw star at `b` containing either of those endpoints would make its edge ordinary. The possible projected ordinary supports are empty, any singleton, or any of `ad,cd,be`. The code grants all nine choices even when a particular graph forbids more.
3. The centre-side raw support of the top labelled `z` is the singleton `z`. If `z` is outside the five vertices its value on these rows is a union of exceptional ORs, each with nonempty global raw support contained in that singleton. An exceptional OR of this kind can promote only one centre. At most two outside-centred tops can therefore contribute. A physical top is clean, so its two operands together reject every independent input.
4. If `c` is outside the centres and (y_z
e c), the private leaf lies outside all five vertices. Adding it to an independent five-vertex input preserves independence because its edges to noncentres could only be residual. The centre operand must reject that input. If its source instead accepts a negative, the private leaf must be `c`, and its projected leaf raw mask is `c` or `cd`.
5. If `c` is a centre, every private leaf lies outside the five and has no neighbor among `a,b,d,e`. Every outside-centred source must reject every independent assignment with `c=0`. A private leaf may neighbor `c`, so other independent assignments are checked on the actual two-operand top. The top labelled `c` has raw centre `c` and raw leaf empty or `e` when `ce` is present, and empty otherwise. A raw `b` would make edge `bc` ordinary. This single top must keep both operands fixed across all assignments.

These are implications from circuit structure to a larger finite search space. A witness to the search need not lift to a circuit. Excluding every choice suffices once the physical implications are supplied.

## Standalone C++ enumeration

`project.cc` tests the full truth tables on all 32 projected inputs. A wire records its 32-bit table, 5-bit projected raw support, and whether the global raw support is nonempty. Ordinary input choices, direct earlier wires, repeated reads, gate order, and inactive gates are all allowed. Outputs with identical triples can share a branch of the enumeration. Different earlier gates remain available for reuse.

For an outside-centred top the centre operand is a disjunction of raw-bearing exceptional sources. Distribution across its leaf reduces each accepting contribution to one such source. The enumerator grants every already-safe source all of its positives. For others it unions the positives of every individually correct guarded term, even when several choices would require different leaves on the same top. The single `c`-centred top, when present, keeps fixed operands for all rows. The algorithm checks all required minimal edges against the union and rejects guarded terms with any false positive.

From this directory, using a local C++17 compiler, one can reproduce the counts in `enumeration.log`.

```sh
c++ -std=c++17 -Wall -Wextra -pedantic -O3 project.cc -o /tmp/disjoint-project
/tmp/disjoint-project controls
for mode in outside inside cross; do
  for order in AAOO AOAO AOOA OAAO OAOA OOAA; do
    /tmp/disjoint-project "$mode" "$order" || exit 1
  done
done
```

All three graph modes reject all six orders, each with 8,734,823 distinct terminal histories across its six orders. A third exceptional OR yields passing controls in all three modes. The negative control accepts `b` alone and demonstrates why the two minimum-cover complement tests alone cannot suffice.

## Lean selector model

`ProjectedSchedule.lean` describes two outside-centred tops with fixed operands and a single optional `c`-centred top. Its ten row masks, in order, are 3, 6, 24, 20, 10, 13, 18, 21, 9, 17. These include each minimal positive, all maximal independent sets, and all four maximal independent sets on `a,b,d,e`. The `P` selectors route an earlier charged gate directly or attach eligible earlier ORs to a permitted raw support. The top selectors choose raw leaves and their sets of exceptional ORs. The definitions allow irrelevant sharing and direct empty wires. A physical gate history is representable by choosing its actual ports and exceptional subsets.

The selector variables describe the finite search interface. They do not themselves construct a project circuit, a maximum matching, a system of private leaves, or a witness to the existing Lean theorem about the original counting inequality.

### Kernel proof and replay

`DisjointProjected.no_four_selectors` quantifies over all selectors, all six gate orders, and all three graph modes. Its two hypotheses say that the four positions contain precisely two ORs and that the extra edge requires `c` to be a centre.

`SelectorBits.lean` proves the bitwise expansions used to express each case as a Boolean formula. `KernelProp.lean` builds a Tseitin encoding and a Lean proof of each truth-table clause. It reads the recorded LRAT data, uses mathlib's proof-producing LRAT checker, and instantiates the refutation with the actual selector expressions. The routine emits a Lean proof term that the kernel checks. The eighteen ASCII certificates are in `certificates/` with hashes in `certificates.sha256`. Replay reads local files and does not invoke a SAT solver.

Use an installed Lean 4.36.0 toolchain and the mathlib package cache from the pinned project checkout, inside the project's offline replay environment. From this directory:

```sh
python3 replay_selectors.py /path/to/lean-4.36.0/bin /path/to/checkout/lean/.lake/packages
```

The expected axiom output for the combined theorem is:

```text
'DisjointProjected.no_four_selectors' depends on axioms: [propext, Classical.choice, Quot.sound]
```
