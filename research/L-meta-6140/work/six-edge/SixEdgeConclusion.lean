import SixEdgeCertificates
import SixEdgePlane
import SixEdgeTrace

namespace SixEdge.Plane

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open ResidualDegree
open Std.Sat Std.Tactic.BVDecide

attribute [local irreducible] Formula.build

/-- The final interface for the six-edge exclusion. The circuit-to-CNF
    translation must supply a satisfying assignment to one of the declared
    formulas. An LRAT proof of that same formula then yields the contradiction. -/
theorem exclude_from_assignment (formula : CertificateKey → CNF Nat)
    (certificate : CertificateKey → Array LRAT.IntAction)
    (checked : ∀ k ∈ keys, LRAT.check (certificate k) (formula k) = true)
    {C : Circuit} (S : Stars C) (least : IsLeastAO plane C)
    (empty : centreless plane C = ∅) (two : (junk plane C).card = 2)
    (three : (exceptional plane C).card = 3)
    (six : (Ustar plane C).card = 6)
    (translation : (Ustar plane C).card = 6 →
      (ofSlots (dirtyAt (charged_card two three)),
        ofSlots (centerAt (charged_card two three) S.center)) ∈ cases →
      ∃ k ∈ keys, ∃ a : Nat → Bool, (formula k).Sat a) : False := by
  obtain ⟨k, mem, assign, sat⟩ := translation six (case_covered S least empty two three)
  exact certificate_contradicts (formula k) (certificate k) (checked k mem) assign sat

/-- The exact generated clauses can be used directly with the replayed LRAT
    certificate. The caller supplies the circuit's choices and their required
    clauses, with auxiliary values constructed by `assignment_satisfies`. -/
theorem exact_trace_contradiction (key : CertificateKey) (certificate : Array LRAT.IntAction)
    (checked : LRAT.check certificate (Formula.exactCNF (Formula.build key)) = true)
    (primary : Formula.Input → Bool)
    (trace : Formula.TraceValid 1 (Formula.build key).events.toList)
    (requires : Formula.Requirements primary Formula.initial (Formula.build key).events.toList) : False :=
  certificate_contradicts _ _ checked _ (Formula.assignment_satisfies primary (Formula.build key) trace requires)

#print axioms exclude_from_assignment
#print axioms exact_trace_contradiction

end SixEdge.Plane
