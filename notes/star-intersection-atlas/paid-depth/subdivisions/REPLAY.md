# Replay the subdivision bound

Use the commit containing this version of the page on the fork’s `paid-depth-tradeoff` branch. Its parent is `d6ff22bd6bb5068ce5e772945bb29fc60597dfcf`. The proof uses the project’s pinned Lean 4.36.0 and Mathlib cache. Run the following from the repository root in an offline checkout with those dependencies already present.

```sh
for name in ReaderBypass ReaderBypassSharp
do
  node tools/check-lean.mjs "lean/PEqualNP/PaidDepth/$name.lean" \
    "notes/star-intersection-atlas/paid-depth/subdivisions/$name.statement" check || exit 1
done
python3 -IB notes/star-intersection-atlas/paid-depth/subdivisions/check_subdivisions.py
```

**ReaderBypass** certifies that r ordinary binary choices and h disjoint two-reader triples need at most 2^r · 7^h rectangles. Its statement starts from arbitrary seeded, closed rejection certificates on a gate graph. Feedback and dependencies into the centers are allowed. **ReaderBypassSharp** constructs the actual three-gate circuits whose rejecting cells are equality on seven and eight labels. The separator cost, the use of 49 inserted gates, the matching lower bound application and the random-marks extension are written mathematical arguments. [Theorem and attribution](THEOREM.md)

The official Mac verifier returned `ACCEPTED (check)` on both statements. It re-checked 1,665 constants for `ReaderBypass` with `propext`, `Quot.sound` and `Classical.choice`, and 1,662 constants for `ReaderBypassSharp` with `propext` alone. Each run recorded 87 distinct project-source digests.

The independent Python control compares fixed-point evaluation of the unmodified wiring against certificate enumeration after output clamping, seven-state compression and separator conditioning. It exhausts all single-arm reads from one center to two readers and arbitrary reverse and inter-reader wires, totaling 2,304 three-gate wirings, every output and all 64 raw assignments. Another 32 six-gate layouts test every output and all 4,096 raw assignments with a separator. The topology controls inspect 75 subdivisions on 745 gates with 231 intact paths across the trials, then four 14,900-gate mixed layouts with exceptional links and 24 large components placed whole across the four runs. A double-arm relay on a seven-cycle checks all 16,384 label pairs with one designated output. The depth-two charge and the illustrative cubic binomial tail are compared as integers.

| Input | SHA-256 |
| --- | --- |
| ReaderBypass.lean | `4e833eb6479b3e0ed060240e7f35caf6cd82f01d9e747ae10e750d366e5a1df5` |
| ReaderBypassSharp.lean | `2e9a9182cef2fe26c770f880aa52d72372d0c3b369b662ccf7a90491f0c06f56` |
| check_subdivisions.py | `c55b3cc590402e2a9e7c498eef63d4eea853270acb6da4510a1c05c51698789d` |
| Project verifier driver | `c8fc4b209e678f76adc3cf4e988be55675ef9384e44cd388203c95c6afb68846` |
