import SixEdgeCertificates
import SixEdgePlane

namespace SixEdge.Plane

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open ResidualDegree
open Std.Sat Std.Tactic.BVDecide

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

#print axioms exclude_from_assignment

end SixEdge.Plane
