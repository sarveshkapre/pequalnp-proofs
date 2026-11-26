import PlaneBound
import PEqualNP.Outside.L_meta_4181

namespace PlaneDesk
open ResidualDegree PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

/-- Incidence in precisely the coordinate convention of R_meta_6140_1. -/
abbrev coordinates (u v : Fin 26) : Prop :=
  ∃ p l : Fin 13, (p - l = 0 ∨ p - l = 1 ∨ p - l = 3 ∨ p - l = 9) ∧
    ((u = Fin.castAdd 13 p ∧ v = Fin.natAdd 13 l) ∨
     (v = Fin.castAdd 13 p ∧ u = Fin.natAdd 13 l))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem coordinates_match : ∀ u v, plane.Adj u v ↔ coordinates u v := by decide

private abbrev planeAdj : DecidableRel plane.Adj := inferInstance

set_option maxHeartbeats 1200000 in
/-- Covers the four-edge branch of the specific plane left in R_meta_6140_1. -/
theorem four_for_desk (G : SimpleGraph (Fin 26)) [dec : DecidableRel G.Adj]
    (spec : ∀ u v, G.Adj u v ↔ coordinates u v) (C : Circuit)
    (least : IsLeastAO G C) (top : TopForm G C) (four : (Ustar G C).card ≤ 4) :
    64 ≤ C.size := by
  have eq : G = plane := SimpleGraph.ext (funext fun u => funext fun v => propext ((spec u v).trans (coordinates_match u v).symm))
  subst G
  cases Subsingleton.elim dec planeAdj
  exact PlaneBound.four_size C least top four

/-- This also starts from the project's public fan-in-at-most-two monotone model. -/
theorem five_for_monotone (C : Circuit) (mono : Monotone2 C)
    (computes : circuitFun 26 C = graphFun plane ∅) (small : C.size ≤ 63) :
    ∃ D, IsLeastAO plane D ∧ TopForm plane D ∧ D.size ≤ C.size ∧
      5 ≤ (Ustar plane D).card := by
  have edges : plane.edgeFinset.Nonempty := Finset.card_pos.mp (by rw [plane_edges]; decide)
  obtain ⟨D,least,top,bound⟩ := PEqualNP.Outside.L_meta_4181 26 plane C edges mono computes
  refine ⟨D,least,top,bound,?_⟩
  by_contra! h
  have := PlaneBound.four_size D least top (by omega)
  omega

#print axioms four_for_desk
#print axioms five_for_monotone
end PlaneDesk
