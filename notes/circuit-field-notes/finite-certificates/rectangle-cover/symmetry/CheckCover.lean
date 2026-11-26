import Std.Sat.CNF.Dimacs
import Std.Tactic.BVDecide.LRAT.Checker
import Std.Tactic.BVDecide.LRAT.Parser

open Std.Sat Std.Tactic.BVDecide

def main (args : List String) : IO UInt32 := do
  let [problem, proof] := args | throw <| IO.userError "expected DIMACS path and LRAT path"
  let source ← IO.FS.readFile problem
  let mut clauses : Array (CNF.Clause Nat) := #[]
  for line in (source.splitOn "\n").drop 1 do
    unless line.isEmpty do
      let mut clause : CNF.Clause Nat := .empty
      for token in (line.splitOn " ").dropLast do
        let some value := token.toInt? | throw <| IO.userError s!"bad literal {token}"
        clause := clause.add (value.natAbs - 1) (value > 0)
      clauses := clauses.push clause
  let formula : CNF Nat := ⟨clauses⟩
  unless formula.dimacs.trimAsciiEnd == source.trimAsciiEnd do
    throw <| IO.userError "DIMACS round-trip mismatch"
  let actions ← LRAT.loadLRATProof proof
  if LRAT.check actions formula then
    IO.println s!"Verified LRAT for {clauses.size} clauses and {actions.size} actions."
    return 0
  else
    throw <| IO.userError "LRAT verification failed"
