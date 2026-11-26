import SixEdgeCases
import Std.Tactic.BVDecide.LRAT.Checker

namespace SixEdge

open Std.Sat Std.Tactic.BVDecide

inductive Refinement where
  | base | inactive | canonicalInactive | active | points | centreLine | otherLine
  deriving DecidableEq, Repr

def Refinement.label : Refinement → String
  | .base => "base"
  | .inactive => "inactive"
  | .canonicalInactive => "canonical_inactive"
  | .active => "active"
  | .points => "points"
  | .centreLine => "centre_line"
  | .otherLine => "other_line"

def unrefined : List Case :=
  [(3,0), (9,0), (9,6), (9,22), (6,8), (6,24),
    (10,0), (10,4), (10,16), (10,20), (12,0), (12,16)]

def refinements (k : Case) : List Refinement :=
  if k ∈ unrefined then [.base]
  else if k.1 = 6 then [.inactive, .active]
  else
    let off := if k.1 = 3 then Refinement.canonicalInactive else .inactive
    [off, .points, .centreLine] ++ (if k.2 = 0 then [] else [.otherLine])

abbrev CertificateKey := Case × Refinement

def keys : List CertificateKey :=
  cases.flatMap fun k => (refinements k).map fun r => (k, r)

theorem keys_length : keys.length = 95 := by decide
theorem keys_nodup : keys.Nodup := by decide
set_option maxRecDepth 4096 in
theorem keys_cases : (keys.map Prod.fst).dedup = cases := by decide

theorem certificate_contradicts (f : CNF Nat) (p : Array LRAT.IntAction)
    (check : LRAT.check p f = true) (assignment : Nat → Bool) (sat : f.Sat assignment) : False := by
  exact Bool.false_ne_true ((LRAT.check_sound p f check assignment).symm.trans sat)

def Case.order (k : Case) : String :=
  String.ofList ((List.range 5).map fun i => if k.1.getLsbD i then 'A' else 'O')

def certificateLines : List String :=
  keys.map fun ⟨k,r⟩ => s!"{k.order} {k.2.toNat} {r.label}"

end SixEdge

def main : IO Unit :=
  for row in SixEdge.certificateLines do
    IO.println row
