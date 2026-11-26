import Mathlib.LinearAlgebra.Matrix.Rank

namespace RifflePencil

/-- After erasing common zeros of a two-dimensional projection, a form
annihilating the target must vanish at sufficiently many retained columns.
The normalizing and annihilating forms use the same decoder matrices. -/
theorem annihilator_count {F : Type*} [Field F] [DecidableEq F] {n r : ℕ}
    (L : Matrix (Fin n) (Fin r) F) (D : Matrix (Fin r) (Fin n) F)
    (g h : Fin r → F) (detect : L * Matrix.diagonal g * D = 1)
    (kill : L * Matrix.diagonal h * D = 0) :
    2 * n + Fintype.card {i // h i ≠ 0} ≤ 2 * r := by
  have hL : n ≤ L.rank := by
    calc
      n = (1 : Matrix (Fin n) (Fin n) F).rank := by simp
      _ = (L * Matrix.diagonal g * D).rank := by rw [detect]
      _ ≤ (L * Matrix.diagonal g).rank := Matrix.rank_mul_le_left _ _
      _ ≤ L.rank := Matrix.rank_mul_le_left _ _
  have hD : n ≤ D.rank := by
    calc
      n = (1 : Matrix (Fin n) (Fin n) F).rank := by simp
      _ = (L * Matrix.diagonal g * D).rank := by rw [detect]
      _ ≤ D.rank := Matrix.rank_mul_le_right _ _
  have first := Matrix.rank_mul_ge L (Matrix.diagonal h)
  have second := Matrix.rank_mul_ge (L * Matrix.diagonal h) D
  rw [kill] at second
  simp only [Matrix.rank_zero, zero_add, Fintype.card_fin] at second
  rw [Matrix.rank_diagonal, Fintype.card_fin] at first
  omega

#print axioms annihilator_count

end RifflePencil
