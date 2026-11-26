import ThreeLinear

open PEqualNP.RiffleRank
open scoped BigOperators
namespace RiffleLower

private def vertex : Fin 8 → Fin 4 → ℤ :=
  ![![1,1,1,1], ![1,1,1,-1], ![1,1,-1,1], ![1,1,-1,-1],
    ![1,-1,1,1], ![1,-1,1,-1], ![1,-1,-1,1], ![1,-1,-1,-1]]

private def plusEnd : Fin 4 → Fin 4 → Fin 8 :=
  ![![0,1,2,3], ![0,1,2,3], ![0,1,4,5], ![0,2,4,6]]
private def otherEnd : Fin 4 → Fin 4 → Fin 8 :=
  ![![7,6,5,4], ![4,5,6,7], ![2,3,6,7], ![1,3,5,7]]
private def signedEnd (b c : Fin 4) (i : Fin 8) : ℤ :=
  if i = plusEnd b c then 1 else if i = otherEnd b c then (if b = 0 then 1 else -1) else 0
private def selected (b : Fin 4) (i : Fin 8) (d : Fin 4) : ℤ :=
  if i = plusEnd b d ∨ i = otherEnd b d then 1 else 0

set_option maxRecDepth 16000 in
private theorem cube_entries : ∀ a b c d : Fin 4,
    ∑ i, vertex i a * signedEnd b c i * selected b i d =
      (if a = b ∧ c = d then 2 else 0 : ℤ) := by decide

/-- Exact four-symbol width in every field in which two is invertible. -/
theorem four_exact_of_two_ne_zero (F : Type) [Field F] (h2 : (2:F) ≠ 0) :
    RiffleRankLe 8 (pairId (Fin 4) F) ∧
    ∀ r, RiffleRankLe r (pairId (Fin 4) F) → 8 ≤ r := by
  constructor
  · let φ : ℤ →+* F := Int.castRingHom F
    refine ⟨fun i a b c d => φ (vertex i a) * φ (signedEnd b c i) *
        (φ (selected b i d) / 2), ?_, ?_⟩
    · intro i
      exact ⟨_,_,_,fun _ _ _ _ => rfl⟩
    · intro a b c d
      have h := congrArg φ (cube_entries a b c d)
      simp only [map_sum,map_mul,apply_ite φ,map_ofNat,map_zero] at h
      simp_rw [← mul_div_assoc]
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul, h]
      by_cases good : a = b ∧ c = d <;> simp [pairId,good,h2]
  · intro r dec
    have h := pair_dyadic (j := 2) dec (by decide)
    omega

#print axioms four_exact_of_two_ne_zero
end RiffleLower
