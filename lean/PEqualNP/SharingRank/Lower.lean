import PEqualNP.SharingRank.Count
import PEqualNP.SharingRank.Encoding
import PEqualNP.SharingRank.Flat

namespace SharingRank.Family
open Formulas
open scoped Classical

/-- Every formula for the explicit budget-(t+3) family spends at least t+4 gates. -/
theorem formula_lower (t : Nat)
    (e : Expr (Four × Words (t+2)) (Four × Words (t+2)))
    (rep : ∀ x y, e.cell x y ↔ cell (t+2) x y = true) : t+4 ≤ e.cost := by
  by_cases flat : e.Flat
  · obtain ⟨r,c,a,b,s,u,h⟩ := e.flat_form flat
    have bound := Witness.flat_bound Witness.zero Witness.row Witness.col Witness.anchor Witness.anchor
      Witness.anchors Witness.missing Witness.crossed
      (encode ⁻¹' r) (encode ⁻¹' c) (fun i => encode ⁻¹' a i) (fun i => encode ⁻¹' b i)
      (fun i => encode ⁻¹' s i) (fun i => encode ⁻¹' u i)
      (fun x y => (encode_cell x y).symm.trans ((rep _ _).symm.trans (h _ _)))
    simp [Witness.Index,Fintype.card_sum,Fintype.card_prod] at bound
    omega
  · have matrix_eq : e.matrix = mat (t+2) := by
      ext x y
      simp only [Expr.matrix,mat,rep]
    have small := e.nested_rank flat
    rw [matrix_eq] at small
    have rank := exact_rank (t+2)
    change (mat (t+2)).rank + 2 = 3^(t+3) at rank
    by_contra! cost
    have budget : e.cost ≤ t+3 := by omega
    have ceil := Nat.mul_le_mul_left 7 (Nat.pow_le_pow_right (by decide : 0 < 3) budget)
    have large : 27 ≤ 3^(t+3) := Nat.pow_le_pow_right (n := 3) (by decide) (show 3 ≤ t+3 by omega)
    omega
end SharingRank.Family
