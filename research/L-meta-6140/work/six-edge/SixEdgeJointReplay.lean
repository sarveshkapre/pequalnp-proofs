import SixEdgeTrace
import Std.Tactic.BVDecide.LRAT.Parser

namespace SixEdge.Formula

open Std.Tactic.BVDecide

/-- Both finite checks in the circuit exclusion run on the same generated state. -/
def caseChecks (key : CertificateKey) (proof : Array LRAT.IntAction) : Bool :=
  let state := build key
  traceValidBool 1 state.events.toList && LRAT.check proof (exactCNF state)

attribute [local irreducible] build exactCNF traceValidBool LRAT.check

theorem caseChecks_spec (key : CertificateKey) (proof : Array LRAT.IntAction) :
    caseChecks key proof = true ↔ traceValidBool 1 (build key).events.toList = true ∧
      LRAT.check proof (exactCNF (build key)) = true := by
  unfold caseChecks
  exact Bool.and_eq_true_iff

/-- The offline driver supplies a case label and an LRAT file in a temporary directory. -/
def replayRecordedCase : IO Unit := do
  let label := (← IO.FS.readFile "case.txt").trimAscii.toString
  let some key := keys.find? (fun k => s!"{k.1.order} {k.1.2.toNat} {k.2.label}" == label)
    | throw (IO.userError s!"unknown case {label}")
  let proof ← LRAT.loadLRATProof "proof.lrat"
  unless caseChecks key proof do
    throw (IO.userError s!"trace numbering or LRAT failed for {label}")
  IO.println s!"Verified exact trace and LRAT for {label} ({proof.size} actions)."

end SixEdge.Formula
