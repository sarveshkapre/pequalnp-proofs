# Replay the sparse-wiring complement result

Use a checkout of the fork at the commit shown on this page, on branch `paid-depth-tradeoff`. The parent of the release is `c5e6d91ebd7581fc3b03b66044b832813f2c3aeb`. The project uses Lean 4.36.0. With the pinned Lean and Mathlib dependencies already available, these commands run from the repository root in an isolated offline checkout.

```sh
for name in LeafTraces ReservePacking
do
  node tools/check-lean.mjs "lean/PEqualNP/PaidDepth/$name.lean" \
    "notes/star-intersection-atlas/paid-depth/sparse-wiring/$name.statement" check || exit 1
done
python3 -IB notes/star-intersection-atlas/paid-depth/sparse-wiring/check_sparse.py
```

**LeafTraces** converts binary reader and private-input choices into a rectangle cover indexed by ternary digits. It handles arbitrary row predicates, column predicates and demand sets as in the statement. **ReservePacking** produces an assignment to integer-capacity bins, including every reserved unit, and bounds the load of every bin. Identifying these predicates in a wired circuit, counting random marked stars, coupling the two-arm laws and combining those facts into an asymptotic theorem are written proofs. [Theorem and attribution](THEOREM.md)

The Python replay uses the standard library. It compares the compressed rectangles to direct least-fixed-point evaluation on every output of all 4,096 ordered four-gate wirings and 256 additional wirings with feedback. It also checks the explicit six-gate component, the two marked-star moments on all 32,768 labeled six-vertex graphs, 1,035 exact combinations of a correlated arm law and its sampling probability bound, and the numerical inequalities at 57/40 using rational arithmetic.

| Input | SHA-256 |
| --- | --- |
| LeafTraces.lean | `025d8865d75a5566ae59fe7e05ce1e29e5dc786894db78a1c4fdefa7b086c4b9` |
| ReservePacking.lean | `08b54ac1cd379fb7c5c884a43a24c3c40ad6813962604e2bb0f4b2e4bc20433b` |
| check_sparse.py | `fb37c6ff5d4b78146e0622425926d415e15797d87c95e4dd3c81c1f15adb51cf` |
| Project verifier driver | `c8fc4b209e678f76adc3cf4e988be55675ef9384e44cd388203c95c6afb68846` |

Both official runs returned `ACCEPTED (check)` on macOS with Lean 4.36.0. The kernel rechecked 1,660 constants for LeafTraces and 1,675 for ReservePacking. Each verdict listed only `propext`, `Quot.sound` and `Classical.choice`. The finite replay also passed in the network-disabled environment.
