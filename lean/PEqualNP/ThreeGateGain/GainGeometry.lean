import PEqualNP.ThreeGateGain.TriangleErrorBounds

/-! Geometry of positive type classes in a signed incidence approximation. -/
namespace GainGeometry
open Finset TriangleOptimality
open scoped Classical

variable {P L : Type*}

noncomputable def weight (G Q : P → L → Prop) (p : P) (l : L) : ℤ :=
  if Q p l then signedCell G p l else 0

noncomputable def score (G Q : P → L → Prop) (A : Finset P) (B : Finset L) : ℤ :=
  ∑ p ∈ A, ∑ l ∈ B, weight G Q p l

theorem score_transpose (G Q : P → L → Prop) (A : Finset P) (B : Finset L) :
    score (fun l p => G p l) (fun l p => Q p l) B A = score G Q A B := sum_comm

/-- Deleting rows and columns of nonpositive gain eventually leaves a core in
which every remaining vertex contributes strictly positively. -/
theorem positive_core (G Q : P → L → Prop) (A : Finset P) (B : Finset L) :
    ∃ S ⊆ A, ∃ T ⊆ B, score G Q A B ≤ score G Q S T ∧
      (∀ p ∈ S, 0 < ∑ l ∈ T, weight G Q p l) ∧
      (∀ l ∈ T, 0 < ∑ p ∈ S, weight G Q p l) := by
  classical
  by_cases hr : ∀ p ∈ A, 0 < ∑ l ∈ B, weight G Q p l
  · by_cases hc : ∀ l ∈ B, 0 < ∑ p ∈ A, weight G Q p l
    · exact ⟨A, Subset.rfl, B, Subset.rfl, le_rfl, hr, hc⟩
    · push Not at hc
      obtain ⟨l, hl, hn⟩ := hc
      obtain ⟨S, hs, T, ht, high, hS, hT⟩ := positive_core G Q A (B.erase l)
      have e := sum_erase_add B (fun l => ∑ p ∈ A, weight G Q p l) hl
      have e' : score G Q A (B.erase l) + (∑ p ∈ A, weight G Q p l) = score G Q A B := by
        simpa only [score, sum_comm (s := A)] using e
      exact ⟨S, hs, T, ht.trans (erase_subset _ _), by omega, hS, hT⟩
  · push Not at hr
    obtain ⟨p, hp, hn⟩ := hr
    obtain ⟨S, hs, T, ht, high, hS, hT⟩ := positive_core G Q (A.erase p) B
    have e : score G Q (A.erase p) B + (∑ l ∈ B, weight G Q p l) = score G Q A B :=
      sum_erase_add A _ hp
    exact ⟨S, hs.trans (erase_subset _ _), T, ht, by omega, hS, hT⟩
termination_by A.card + B.card
decreasing_by all_goals first | omega | simp_wf; grind [Finset.card_erase_lt_of_mem]

/-- A large class with positive gain on each member has a unique predicted neighbor. -/
theorem heavy_unique (G : P → L → Prop) (hs : NoSquare G) (A : Finset P) (B : Finset L)
    (ha : 4 ≤ A.card) (positive : ∀ p ∈ A, 0 < ∑ l ∈ B, signedCell G p l) :
    B.card = 1 := by
  classical
  have low : (A.card : ℤ) ≤ gain G A B := by
    rw [gain_sum]
    simpa using (sum_le_sum (s:=A) (f:=fun _ => (1:ℤ))
      (g:=fun p => ∑ l ∈ B, signedCell G p l) (fun p hp => positive p hp))
  by_contra h
  rcases B.eq_empty_or_nonempty with rfl | ne
  · simp [gain, edges] at low
    obtain ⟨p,hp⟩ := card_pos.mp (show 0 < A.card by omega)
    have hpos := positive p hp
    simp at hpos
  · have hi := signed_rectangle G hs A B (by omega)
          (by have := card_pos.mpr ne; omega)
    omega

/-- The moment inequality gives a uniform bound on the singleton remainder
in every three-gate host. Only one shore needs a cardinality bound. -/
theorem singleton_edges (G : P → L → Prop) (hs : NoSquare G) (A : Finset P) (B : Finset L)
    (ha : A.card ≤ 28) : edges G A B ≤ 3*((A.card:ℤ)+B.card) := by
  have m := moments G hs A B
  let a : ℤ := A.card
  let b : ℤ := B.card
  change _ ≤ 3*(a+b)
  change _ ≤ b*(edges G A B+a*(a-1)) at m
  have an : 0 ≤ a := by positivity
  have bn : 0 ≤ b := by positivity
  have lim : 0 ≤ 28-a := by dsimp [a]; omega
  have numeric : 0 ≤ (3*(a+b))^2 - b*(3*(a+b)+a*(a-1)) := by
    nlinarith [mul_nonneg (mul_nonneg lim an) bn, sq_nonneg (a-b), sq_nonneg a]
  by_contra! bad
  have prod := mul_pos (show 0 < edges G A B - 3*(a+b) by omega)
    (show 0 < edges G A B + 3*(a+b)-b by omega)
  nlinarith

private theorem select {V : Type*} [DecidableEq V] (a s : Finset V) (h : s ⊆ a) (f : V → ℤ) :
    (∑ v ∈ a, if v ∈ s then f v else 0) = ∑ v ∈ s, f v := by
  rw [← sum_filter]; congr 1; ext v; simp; exact fun hv => h hv
private theorem except {V : Type*} [DecidableEq V] (a s : Finset V) (f : V → ℤ) :
    (∑ v ∈ a, if v ∉ s then f v else 0) = ∑ v ∈ a \ s, f v := by
  rw [← sum_filter]; congr 1; ext; simp
private theorem pull {V : Type*} (s : Finset V) (u : Prop) [Decidable u] (f : V → ℤ) :
    (∑ v ∈ s, if u then f v else 0) = if u then ∑ v ∈ s, f v else 0 := by
  by_cases h : u <;> simp [h]

/-- Every predicted crossing of two centers costs one unit in the union bound.
The residual includes exactly the cells outside both center sets. -/
theorem center_decomposition (G Q : P → L → Prop) (A X : Finset P) (B Y : Finset L)
    (xA : X ⊆ A) (yB : Y ⊆ B) (d : ℤ)
    (row : ∀ p ∈ X, ∑ l ∈ B, hit G p l ≤ d)
    (col : ∀ l ∈ Y, ∑ p ∈ A, hit G p l ≤ d) :
    score G Q A B ≤ ((X.card:ℤ)+Y.card)*d - edges Q X Y + score G Q (A \ X) (B \ Y) := by
  classical
  have cell (p : P) (l : L) :
      weight G Q p l + (if p ∈ X then (if l ∈ Y then hit Q p l else 0) else 0) ≤
      (if p ∈ X then hit G p l else 0) + (if l ∈ Y then hit G p l else 0) +
      (if p ∉ X then (if l ∉ Y then weight G Q p l else 0) else 0) := by
    by_cases u : p ∈ X <;> by_cases v : l ∈ Y <;> by_cases g : G p l <;> by_cases z : Q p l <;>
      simp [u,v,g,z,weight,signedCell,hit]
  have total := sum_le_sum (s:=A) (fun p _ => sum_le_sum (s:=B) (fun l _ => cell p l))
  simp only [sum_add_distrib] at total
  rw [sum_comm (f:=fun p l => if l∈Y then hit G p l else 0)] at total
  simp_rw [pull, select A X xA, select B Y yB, except] at total
  have r := sum_le_sum (s:=X) (g:=fun _ => d) row
  have c := sum_le_sum (s:=Y) (g:=fun _ => d) col
  simp only [sum_const,nsmul_eq_mul] at r c
  unfold score edges
  linarith

#print axioms positive_core
#print axioms heavy_unique
#print axioms singleton_edges
#print axioms center_decomposition
end GainGeometry
