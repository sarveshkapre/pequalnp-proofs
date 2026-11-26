# The six-residual-edge plane case

This package concerns the order-three projective plane with six residual incidences, one ordinary top AND at each of the 13 lines, no centreless top, two dirty ANDs, and three exceptional ORs. A residual incidence is a point–line pair whose endpoints never reach opposite ports of an ordinary top through ORs alone.

## Lean results

- `case_covered` maps the charged gates of a least top-form circuit to one of the 34 pairs of gate-order and centre-route masks. In a centred circuit a dirty AND must have a later charged reader. An exceptional OR before the first dirty AND adds nothing to a top operand beyond its raw literals.
- `matches_ports` gives the search's two operand forms. An operand is a prior charged wire, or it is the OR of a nonempty set of raw literals and compatible earlier exceptional ORs. The raw set fits in a singleton or in one of the 13 leaves. `residual_card` identifies the encoder's count of missing raw pairs with the circuit's residual count.
- Lean verifies the coordinate relabellings used to fix an incidence or two specified lines, the order change putting raw-only ORs first, the shape of an active first dirty AND, and the test-preserving step that mutes a first dirty AND which stays off on the residual incidences.

## Certificate coverage

The Lean table contains 95 distinct certificate keys covering all 34 mask pairs. Each formula uses the 52 required incidences and 80 selected edge-free inputs. The replay verifies the key list against Lean, regenerates the DIMACS input, checks its full SHA-256 digest, and replays the contradiction in Lean's LRAT checker.

On November 25, 2026 (Pacific time), the clean Lean rebuild passed and all 95 formulas replayed with their recorded hashes.

The circuit theorem is still conditional at `exclude_from_assignment`. The missing proof must take the physical port data and the applicable refinement, assign Boolean values to the original encoder's variables, and show every clause of that exact formula holds. The local clause lemmas cover the OR and AND definitions used for auxiliary variables. The assignment theorem also needs to cover the encoder's selection, routing, and counting clauses. A successful LRAT replay establishes unsatisfiability of its DIMACS formula.

## Replay

Use Lean 4.36.0 and the upstream checkout at `e6bfe1a56efc768d244627b78f175b18de1acd6f` with its build cache and pinned Mathlib. Run the command from `research/L-meta-6140` in this fork. The required Lean helper files and the certificate checker sit alongside the six-edge files in this package.

```sh
python3 -B work/six-edge/check.py /path/to/pequalnp-proofs --lean /path/to/lean
```

Add `--proof-only` to skip CaDiCaL, or `--kernel-replay` for an additional standalone kernel replay. The command uses a temporary build directory and the tools installed alongside Lean.
