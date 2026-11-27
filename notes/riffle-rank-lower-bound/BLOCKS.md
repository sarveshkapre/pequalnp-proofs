# At least 93 terms for the two-block identity on 32 symbols

**Theorem.** Over every field, an exact two-block riffle dictionary on 32 symbols has at least 93 terms. The decoders may overlap and can depend on the target. The proof gives no construction at 93.

Over the rationals, 64 columns really do allow six-target quotients with different geometry from the optimal 63-column example. The obstruction to width 90 comes from decoding all the targets in the original dictionary. To prove the stronger bound we combine the earlier rectangular bounds with Mirandola and Zémor's theorem on products of linear codes. The proof of 93 is independent of the previous classification of optimal rational quotients. [Rossman's model](https://users.cs.duke.edu/~br148/riffle-rank.pdf) · [Prior rectangular bounds](DYADIC.md) · [Mirandola and Zémor, Theorem 3.3](https://arxiv.org/pdf/1501.06419)

## A six-target dictionary in which the extra column is essential

Take the 64 sign vectors in six dimensions and subtract the same vector (2, 4, 8, 16, 32, 64) from each. For any target coordinate, the 32 pairs that differ in that sign have difference twice its basis vector. Assign one pair to each diagonal entry of the output and divide each difference by two. This gives an exact decoder. This example is also the image of the seven-target columns (1, signs) under the single linear map (a, x) ↦ x − a(2, 4, 8, 16, 32, 64).

Every column is nonzero in all six coordinates. Deleting any column therefore leaves 63 columns and still no column on any coordinate line. The target-line bound at width 63 requires at least one position on **each** target line. Thus even with freshly chosen decoders, every deletion fails. In fact, the 64-column example has no dependent triple, whereas the optimal 63-column configuration has 301. An exact integer Gram-determinant check covers all 41,664 triples. [Checker](check_90.py) · [63-column argument](NINETY.md)

## A block inequality for an unrestricted decoder

Fix output size 32. Write D(k) for the minimum width with k independent targets. The first columns form a surjection A from the coordinate space of r positions onto the k-dimensional target space. The columns span that space because a functional vanishing on all columns decodes zero and therefore vanishes on every basis target. Quotienting by a subspace of dimension t spanned by m positions kills all m of them. The images of some k−t original targets form a basis and retain their decoders. Consequently

    D(k−t) ≤ r−m,       D(k+1) ≥ D(k)+1.

We use D(0)=0. The second inequality follows by contracting one nonzero column. Starting bounds for k=1,…,7 are 32, 48, 56, 60, 62, 63, 64, from the rectangular theorem and shortening.

Fix one target b. Among the subsets of dictionary positions supporting an exact decoder for b, choose one of minimum cardinality a. This choice concerns this one decoder only. Let C be the row space of its left matrix and E the column space of its right matrix, both in the coordinate space of those a positions. Both have dimension 32 since a functional taking value one on b decodes the identity. Let P be the span of their coordinatewise products. The shared matrix A sends P into the line through b. Indeed, a left row times a right column, coordinate by coordinate, maps to b on diagonal output entries and zero on off-diagonal entries. Since a subset of columns has nullity at most that of the whole dictionary, dim P ≤ r−k+1.

Mirandola and Zémor's Theorem 3.3 says that dim P ≥ dim C + dim E − dim St(P), where St(P) consists of coordinate multipliers preserving P. This is the theorem for coordinatewise products of codes; it applies over arbitrary fields. The stabilizer is the algebra of functions constant on each block of a partition. To see this, put coordinates in the same block if all stabilizer elements agree there. For any fixed block and each other block, choose an element separating the two, subtract its value on the other block and normalize its value on the fixed block to one. Multiplying these elements gives the fixed block's indicator. Hence P splits as a direct sum of its block restrictions Pᵢ. With q blocks,

    q ≥ 64 − (r−k+1),       64 ≤ dim P + q.

Each A(Pᵢ) is the entire target line. If it were zero, the original decoder could discard that entire block: every row–column product restricted to the block contributes zero to the vector it decodes. This would contradict the choice of a. In particular every block spans b. Write mᵢ for a block's size and tᵢ for the rank of its first columns. Rank-nullity on that block gives dim Pᵢ ≤ mᵢ−tᵢ+1. This proves the necessary inequality

    64 ≤ Σᵢ (mᵢ−tᵢ+2),       Σᵢ mᵢ = a ≤ r.                     (1)

This partition is a consequence of the theorem on codes. The riffle model places no partition requirement on a decoder.

## The width-90 contradiction directly

By the earlier rational eight-target bound D(8) ≥ 66, any 25 columns in a proposed width-90, 32-target dictionary are independent. Otherwise extend a basis of their span to 24 independent columns and contract them. At least one further position vanishes, leaving at most 65 positions for eight targets. Two distinct decoder blocks each span b and hence their union is dependent, so their sizes must sum to at least 26. Their ranks are at least their sizes capped at 25. Capping preserves that pair-sum inequality since each size is positive. Thus the sum of the block ranks is at least 13q. But q ≥ 5 and (1) gives 64 ≤ 90−11q ≤ 35. This already answers the width-90 question. [Earlier eight-target obstruction](NINETY.md)

## A stronger bound in four steps

The following proof starts from the all-field rectangular bounds alone. In each row we exclude width r at k targets. The last column bounds the ratio (m−t+2)/m for an individual block of size m ≥ 3 and rank t.

| Targets k | Width r to exclude | Minimum blocks q₀ | Largest possible block M | Verified upper ratio N/B |
|---:|---:|---:|---:|---:|
| 8 | 65 | 6 | 51 | 9/10 |
| 11 | 69 | 5 | 58 | 7/8 |
| 14 | 73 | 4 | 65 | 5/6 |
| 17 | 77 | 3 | 72 | 4/5 |

In each row the previous bound at k−3 is at least r−3. A dependent set of four positions would have rank at most three. Extending its basis to three independent columns and contracting those columns would therefore erase at least four positions and contradict that bound. All four-element subsets are independent, so each block has rank at least min(4,m). As any two blocks span the same nonzero b, their union is dependent. Their sizes sum to at least five. At most one block has size at most two. Any ℓ ≥ 2 blocks occupy at least 3ℓ−1 positions: a minimum size of two forces all others to have size at least three, a minimum of one forces at least four, and otherwise all have size at least three. Taking the other q−1 blocks gives M = r−3(q₀−1)+1.

For reproducibility, the last column of the table uses only the following integer test. The entries of L at indices 0,…,16 are

    0, 32, 48, 56, 60, 62, 63, 64, 66, 67, 68, 70, 71, 72, 74, 75, 76.

In the row for k, only indices below k are used. After each exclusion set L(k)=r+1 and fill intermediate dimensions by single-column shortening. For every 3 ≤ m ≤ M and min(4,m) ≤ t ≤ min(k,m), keep the pair if L(k−t)+m ≤ r. All such pairs satisfy B(m−t+2) ≤ Nm. The exact peak ratios in the four rows are 15/17, 49/58, 53/65 and 19/24. For m=1 or 2 the block is independent and its contribution to (1) is exactly two.

Summing the ratios and allowing the single small block gives

    B Σᵢ (mᵢ−tᵢ+2) ≤ Nr + (2B−N) < 64B

in each of the four rows. This contradicts (1). Padding a representation by zero terms is allowed, so excluding r excludes every smaller width. The last row gives D(17) ≥ 78. Fifteen further applications of shortening give **D(32) ≥ 93**.

## Verification and credit

The checker constructs the six decoders and verifies the translated cube by exact integer arithmetic. It checks the four ratios and independently optimizes (1) over all admissible integer block sizes by dynamic programming, obtaining maximum sums of 55, 57, 59 and 61, respectively. [Exact output](block-check.txt)

The accompanying Lean file checks the map from decoder products to the target line, the four per-block inequalities, and summation with one exceptional small block. The code-product theorem and the passage from a general decoder to its block structure are used in the written proof. An end-to-end Lean theorem for the bound 93 remains open. [Lean components](SchurBlockCaps.lean) · [Mac kernel and leanchecker replay](block-lean-replay.txt)

From the fork root, the first command requires only the Python standard library. The second requires the pinned macOS Lean toolchain and prebuilt Mathlib dependencies.

```sh
python3 -I notes/riffle-rank-lower-bound/check_90.py
python3 -I notes/riffle-rank-lower-bound/replay.py .
```

Benjamin Rossman introduced riffle rank. Diego Mirandola and Gilles Zémor proved the code-product theorem used here. Tomatotomata previously connected disjoint-recovery codes to riffle upper bounds. The application here is to arbitrary overlapping decoders, using the rank of shortened dictionaries to bound their product-code blocks. Whether 93 terms suffice, and whether a uniform linear upper bound exists over the rationals, remain open. [Rossman](https://users.cs.duke.edu/~br148/riffle-rank.pdf) · [Mirandola and Zémor](https://arxiv.org/abs/1501.06419) · [Upstream discussion](https://github.com/open-goat/pequalnp-proofs/discussions/26249)
