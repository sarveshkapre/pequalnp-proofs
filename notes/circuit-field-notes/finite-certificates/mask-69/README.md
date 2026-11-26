# Five points need seven gates. Six points need eight.

Light up one or two points. The circuit should return true for point 0 alone, point 1 alone, or points 0 and 2 together. All other promised inputs must give false. On the other inputs the circuit may return either answer. The allowed gates are AND, OR and NOT with fan-in at most two, and any earlier wire may be reused.

| Points | Desk encoding | Gate minimum | Construction | Lower bound |
| --- | --- | --- | --- | --- |
| 5 | [Mask 69](https://pequalnp.com/desk/row?gap=L-meta-23714) | 7 | [SevenGates.lean](SevenGates.lean) | [Refutation.lean](Refutation.lean) |
| 6 | [Mask 133](https://pequalnp.com/desk/row?gap=L-meta-24241) | 8 | [SixPoints.lean](SixPoints.lean) | [SixPoints.lean](SixPoints.lean) |

In this encoding the bit for an unordered pair of indices i and j sits at position n × min(i,j) + max(i,j). Taking the two indices equal represents a singleton. The two constructions are the gate lists supplied by the desk. Earlier [independent solver results](https://github.com/open-goat/pequalnp-proofs/discussions/33097#discussioncomment-19932662) also reported the five-point optimum. These files give formal lower bounds and verify both gate lists.

## Why one fewer gate fails

Take the five-point board. With only point 0 lit the answer is true. Adding point 4 changes it to false. Yet with point 4 held off, the board still gives different answers on singletons 0 and 2. Fixing input 4 to false therefore lets at least one gate be eliminated. The same argument eliminates a gate when fixing point 3 to false. The proof adapts the project’s [gate-elimination argument](https://github.com/open-goat/pequalnp-proofs/blob/e6bfe1a56efc768d244627b78f175b18de1acd6f/lean/PEqualNP/MetaComplexity/Helpers/Elim.lean).

A six-gate solution would now give a four-gate circuit on three inputs. Each wire has a six-bit truth table on the remaining three singletons and three pairs. Lean checks every way at most four gates could add another table to the available wires. Both constants and all earlier wires remain available. The target table is absent. The formal result is `Mask69.no_six`.

In the six-point version, the new point 5 never belongs to a positive test. Fixing it to false leaves exactly the five-point board, and eliminates another gate by the same argument. A seven-gate circuit would contradict the five-point lower bound. Lean checks this as `SixPointMask133.no_seven`, alongside the eight-gate construction.

[Replay the proofs](../README.md). The constructions cover all 25 and 36 ordered pairs, respectively; reversing a pair represents the same input.
