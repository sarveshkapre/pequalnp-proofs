# Replay the relay subdivision results

Use the revision containing this page on the fork’s paid-depth-tradeoff branch. Its parent is fe16e06386eb71546c19678fe80f18797cf7dcc3. From the repository root, use the pinned Lean 4.36.0 toolchain and its cached Mathlib dependencies. These checks require no network once the checkout and dependencies are present.

~~~sh
for name in RelaySubdivision OptionalEqualityBank
do
  node tools/check-lean.mjs "lean/PEqualNP/PaidDepth/$name.lean" \
    "notes/star-intersection-atlas/paid-depth/relay-subdivisions/$name.statement" check || exit 1
done
python3 -IB notes/star-intersection-atlas/paid-depth/relay-subdivisions/check_relay.py
~~~

**RelaySubdivision** combines the seven-code rectangle cover for whole removable regions with the two-branch equivalence for a mandatory path. Its rejection predicates allow feedback and arbitrary input bans. The path dichotomy, separator packing, chain-width and signal-pattern refinements, and global asymptotic bound are written mathematical arguments. [Subdivision proof](THEOREM.md)

**OptionalEqualityBank** proves the minimum number of rectangles for all optional-coordinate equality requests, at every uniform alphabet size of at least two. The written argument also covers unequal alphabets and arbitrary subfamilies of requests. [Counting proof](OPTIONAL_BANK.md)

Both official runs completed on the Mac in the offline sandbox.

| Theorem | Official verdict | Constants re-checked | Axioms | Distinct project-source digests |
| --- | --- | --- | --- | --- |
| RelaySubdivision | ACCEPTED (check) | 1667 | propext, Quot.sound, Classical.choice | 87 |
| OptionalEqualityBank | ACCEPTED (check) | 1661 | propext, Quot.sound, Classical.choice | 87 |

The independent Python replay reproduces these checks.

- Of all 4,096 directed four-gate path layouts, 3,367 have at least one double read. A bit-parallel least-fixed-point evaluator and a separate certificate evaluator agree on the two branches for all 53,872 output/layout combinations and all 256 raw settings in each. The 127 layouts containing a mandatory run the full length of the path are included.
- With two disjoint two-gate regions in an eight-gate circuit, all 256 output/layout combinations agree on all 65,536 raw settings. Exactly $2^2 7^2=196$ orientations are retained in each layout.
- All mandatory-direction patterns on the tested windows of four, six and eight vertices obey the dichotomy. The 6,731 windows lacking a sufficiently long directed run admit 63,294 compatible seed patterns in total.
- Across twelve subdivisions of the complete bipartite graph $K_{3,3}$, every one of 768 combinations of mandatory-path decisions separates the original vertices and preserves the retained regions.
- The bank control enumerates all 225, 65,025 and 261,121 nonempty rectangles respectively for alphabet/coordinate counts $(2,2),(2,3),(3,2)$. It checks witness labels and every request of the matching construction. The respective minima are 9, 27 and 16.
- All 4,096 directed graphs on four pivots satisfy the weighted chain bound. Minimum chain cover and maximum antichain agree, including with cycles after tying mutually reachable pivots.
- All 65,535 nonempty families of binary signals on four pivots satisfy the weighted shattering bound for weights 1/2, 1/3, 1/5 and 1/7. Some families attain equality at every possible dimension.

| Replay input | SHA-256 |
| --- | --- |
| RelaySubdivision.lean | `f3c911311aef85c9ec5aef58362d1af8784439becb96005db1b1f9139957292a` |
| OptionalEqualityBank.lean | `c4dc8f33382e12118bbbb47d3947bcd68c000b28a2298f0653fd333d4dd33cab` |
| check_relay.py | `8938ad21a781b744e97c6e2691e8da56e18e64a9157121787f7276912a5f204f` |
| check-lean.mjs | `c8fc4b209e678f76adc3cf4e988be55675ef9384e44cd388203c95c6afb68846` |
