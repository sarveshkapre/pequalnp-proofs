# Fourteen rectangles cover 334 of 336 required cells

The [L-meta-9348 board](https://pequalnp.com/desk/row?gap=L-meta-9348) has 21 rows and 21 columns. A zero is a cell to cover. A legal rectangle is any set of rows crossed with any set of columns, provided every cell in that product is a zero. The rows and columns may be nonconsecutive. Can fourteen legal rectangles cover every zero?

| Construction | Rectangles | Required cells covered | Uncovered cells, zero-based (row, column) |
| --- | ---: | ---: | --- |
| [Starting arrangement](Desk9348Partial.lean) | 14 | 334 | (6, 17), (10, 13) |
| [Rearranged](Desk9348Rearranged.lean) | 14 | 334 | (12, 13), (14, 17) |
| [Full control](symmetry/SymmetricPlane.lean) | 15 | 336 | None |

Lean checks the actual union of each rectangle list against all 441 cells, including the 105 forbidden entries. Both fourteen-rectangle arrangements have two holes. The fifteen-rectangle control keeps twelve rectangles from the starting arrangement and covers both holes. A [prior full fifteen-rectangle construction](https://github.com/open-goat/pequalnp-proofs/pull/13338) was already public.

## What a successful repair must change

A specific correspondence between rows and columns makes the board symmetric. Under that correspondence, transposition takes a rectangle to its reflected partner. The starting fourteen rectangles are closed under this operation. An exhaustive search gives exactly 334 as the maximum for fourteen rectangles with this symmetry. Even twelve rectangles closed under that transposition plus two arbitrary legal rectangles cannot finish the board. A full fourteen-rectangle cover must consequently have at least three rectangles whose reflected partner is absent.

The explicit witnesses are Lean theorems. The symmetry bound uses written case reductions and machine-checked propositional contradictions. It applies to the specified symmetry; the unrestricted fourteen-rectangle question is unresolved by this work. [Read the argument and replay the two searches](symmetry/README.md). [Replay the witness proofs](../README.md).
