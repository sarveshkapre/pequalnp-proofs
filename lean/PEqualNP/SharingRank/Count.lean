import PEqualNP.SharingRank.FamilyRank

namespace SharingRank.Family
open scoped BigOperators Classical

private noncomputable def nz (r : ℝ) : Nat := if r ≠ 0 then 1 else 0
private theorem nz_mul (x y : ℝ) : nz (x*y) = nz x * nz y := by
  by_cases h : x=0 <;> by_cases g : y=0 <;> simp [nz,h,g]

private theorem total (u : Four → ℝ) (d : Nat) :
    ∑ w : Words d, nz (tensorWeight u d w) = (∑ j : Four, nz (u j))^d := by
  induction d with
  | zero => simp [tensorWeight,nz]; rfl
  | succ d ih =>
    change (∑ w : Four × Words d, nz (u w.1 * tensorWeight u d w.2)) = _
    simp only [Fintype.sum_prod_type,nz_mul,← Finset.mul_sum,ih,← Finset.sum_mul]
    rw [pow_succ,Nat.mul_comm]

private theorem active (d : Nat) (w : Words d) (h : tensorWeight weightsC d w ≠ 0) :
    tensorWeight weightsC d w = 1 ∧ tensorWeight weightsQ d w = 1 := by
  induction d with
  | zero => exact ⟨rfl,rfl⟩
  | succ d ih =>
    obtain ⟨j,w⟩ := w
    have tail : tensorWeight weightsC d w ≠ 0 := right_ne_zero_of_mul h
    obtain ⟨a,b⟩ := ih w tail
    fin_cases j <;> norm_num [tensorWeight,weightsC,weightsQ,a,b] at *
    exact ⟨a,b⟩

private theorem head_count (d : Nat) (w : Words d) :
    (∑ j : Four, nz (coeff d (j,w))) + 2 * nz (tensorWeight weightsC d w) =
    3 * nz (tensorWeight weightsQ d w) := by
  unfold coeff
  dsimp only
  have h := active d w
  generalize hp : tensorWeight weightsC d w = p at *
  generalize hq : tensorWeight weightsQ d w = q at *
  rw [Fin.sum_univ_four]
  by_cases hp : p = 0
  · by_cases hq : q = 0 <;> norm_num [weightsAll,weightsQ,hp,hq,nz]
  · obtain ⟨a,b⟩ := h hp
    norm_num [weightsAll,weightsQ,a,b,nz]

theorem exact_rank (d : Nat) : (mat d).rank + 2 = 3^(d+1) := by
  classical
  have c := total weightsC d
  have q := total weightsQ d
  norm_num [Fin.sum_univ_four,weightsC,weightsQ,nz] at c q
  have h := Finset.sum_congr (s₁ := (Finset.univ : Finset (Words d))) rfl
    (fun w _ => head_count d w)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at h
  change (∑ w : Words d, nz (tensorWeight weightsC d w)) = 1 at c
  change (∑ w : Words d, nz (tensorWeight weightsQ d w)) = 3^d at q
  rw [c,q] at h
  rw [rank_coeff,Fintype.card_subtype]
  have card : (Finset.univ.filter (fun i => coeff d i ≠ 0)).card =
      ∑ i, nz (coeff d i) := by
    simpa only [nz,Nat.cast_id] using
      (Finset.sum_boole (R := Nat) (fun i => coeff d i ≠ 0) Finset.univ).symm
  rw [card]
  change (∑ p : Four × Words d, nz (coeff d p)) + 2 = _
  rw [Fintype.sum_prod_type_right,pow_succ,Nat.mul_comm (3^d)]
  simpa using h
end SharingRank.Family
