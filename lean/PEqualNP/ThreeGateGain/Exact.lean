import PEqualNP.ThreeGateGain.UpperBound
import PEqualNP.ThreeGateGain.GainRealize

namespace PEqualNP.ThreeGateGain
open FanoFiveUpper GainGeometry TriangleOptimality Finset Configuration

/-- Scores obtainable by ordinary circuits, with arbitrary free unions at the
output and access to all previous intersections. -/
def scores (P L : Type*) [Fintype P] [Fintype L] [Membership P L] : Set ℤ :=
  {v | ∃ (n : Nat) (_ : n ≤ 3) (s : Circuit n) (o : Arm n),
    score (fun p l => p ∈ l) (fun (p : P) (l : L) =>
      o.eval (Fintype.equivFin P p) (Fintype.equivFin L l)
        (s.eval (Fintype.equivFin P p) (Fintype.equivFin L l)) = true) univ univ = v}

/-- The maximum is achieved; it is taken over all circuits spending zero to
three intersections, even those that accept false incidences. -/
theorem exact_maximum {P L : Type*} [Fintype P] [Fintype L] [Membership P L]
    [ProjectivePlane P L] (hq : 16 ≤ ProjectivePlane.order P L) :
    IsGreatest (scores P L) (10 * (ProjectivePlane.order P L : ℤ) - 2) := by
  obtain ⟨s,o,attains,_⟩ := GainRealize.attained (P:=P) (L:=L) (by omega)
  refine ⟨⟨3,le_rfl,s,o,attains⟩,?_⟩
  rintro v ⟨n,budget,s,o,rfl⟩
  exact GainUpper.ordinary GainFinite.all_checked hq budget s o (Fintype.equivFin P) (Fintype.equivFin L)

#print axioms exact_maximum
end PEqualNP.ThreeGateGain
