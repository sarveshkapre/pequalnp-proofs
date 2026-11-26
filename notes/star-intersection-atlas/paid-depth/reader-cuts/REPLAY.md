# Replay the reader proofs

Use this revision of the paid-depth-tradeoff branch. The parent is b515c62b295bbd844cf1dd479b1982856def0d49. From the repository root, with pinned Lean 4.36.0 and Mathlib cached, run these commands offline.

~~~sh
for name in ReaderCut PrivateReaders
do
  node tools/check-lean.mjs "lean/PEqualNP/PaidDepth/$name.lean" \
    "notes/star-intersection-atlas/paid-depth/reader-cuts/$name.statement" check || exit 1
done
python3 -IB notes/star-intersection-atlas/paid-depth/reader-cuts/check_readers.py
~~~

| Formal theorem | Official Mac verdict | Constants rechecked | Distinct project source hashes |
| --- | --- | ---: | ---: |
| [ReaderCut](ReaderCut.statement) | ACCEPTED (check) | 1,661 | 87 |
| [PrivateReaders](PrivateReaders.statement) | ACCEPTED (check) | 1,661 | 87 |

Both official runs reported `propext`, `Quot.sound` and `Classical.choice`. ReaderCut proves that all rejected inputs are exactly the union of the prefix and forced-gate branches. PrivateReaders proves the guarded reduction and the existence of a guess with a private reader per sender even with cycles. The gate accounting, resulting asymptotic bounds, and random-cut estimates have written proofs. [Balanced cuts](THEOREM.md) · [Private readers](PRIVATE_READERS.md)

The standard-library control first evaluates the original circuit one cell at a time by monotone iteration. A separate evaluator handles all cells in parallel and reconstructs both reductions. [Control source](check_readers.py)

- The check covers all 256 two-gate feedback wirings for the private-reader theorem and all 64 ordered three-gate acyclic wirings for both theorems, with every raw input, output selection and eligible cut threshold.
- Another 128 four-gate diagrams allow feedback inside each side of a one-way cut. Both reductions agree on all 256 raw settings and 16 output selections per diagram.
- Dropping the predecessor guard gives a false positive on two gates. All 512 binary three-by-three read relations also pass a comparison of irredundant neighborhood generators with an independent search for permutation submatrices.
- A rectangle constructor evaluates the two explicit depth-one banks for 9,600 prefix-guess/output combinations on 64 cells each. All answers and the stated bounds on both bank sizes agree.

| File | SHA-256 |
| --- | --- |
| ReaderCut.lean | `af486aa0f1a03536bb70e7b3ab4ed14f9c4e2a5f95b6d8812bcfd9fff3c55f82` |
| PrivateReaders.lean | `de605456ddcee585532fcbe2ea7d7581cbb25036552eef323447ce49bab6a643` |
| check_readers.py | `78dbc30b3ba366b4a2296045694fe4a27e5df58f5478b254294bc385c2cc2c2f` |
| check-lean.mjs | `c8fc4b209e678f76adc3cf4e988be55675ef9384e44cd388203c95c6afb68846` |
