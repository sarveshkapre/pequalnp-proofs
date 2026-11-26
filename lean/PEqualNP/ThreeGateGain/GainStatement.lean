import PEqualNP.ThreeGateGain.GainGeometry
import PEqualNP.ThreeGateGain.FiniteValue

namespace GainStatement
open GainFinite GainGeometry TriangleOptimality Finset
open scoped Classical

/-- The externally recorded statement scores each yes answer directly. -/
theorem score_direct {P L : Type*} [Fintype P] [Fintype L]
    (G : P → L → Prop) (prediction : P → L → Bool) :
    score G (fun p l => prediction p l = true) univ univ =
      (univ.sum fun p : P => univ.sum fun l : L =>
        if prediction p l then @ite ℤ (G p l) (Classical.propDecidable _) 1 (-1) else 0) := by
  classical
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro l _
  by_cases a : prediction p l = true <;> by_cases b : G p l <;>
    simp [weight,signedCell,hit,a,b]

end GainStatement
