import PEqualNP.ThreeGateGain.GainGeometryResidual

namespace GainGeometry
open Finset TriangleOptimality
open scoped Classical

variable {P L I J : Type*}

/-- Restricting both shores to vertices touching a predicted edge preserves
the signed score, including its negative entries. -/
theorem score_incident (G Q : P → L → Prop) (A : Finset P) (B : Finset L) :
    score G Q (A.filter fun p => ∃ l ∈ B, Q p l) (B.filter fun l => ∃ p ∈ A, Q p l) =
      score G Q A B := by
  classical
  simp only [score,sum_filter]
  apply sum_congr rfl; intro p hp
  by_cases ex : ∃ l ∈ B, Q p l
  · rw [ite_eq_left ex]
    apply sum_congr rfl; intro l _
    by_cases v : ∃ u ∈ A, Q u l
    · simp [v]
    · have notQ : ¬Q p l := fun h => v ⟨p,hp,h⟩
      simp [v,notQ,weight]
  · rw [ite_eq_right ex]
    symm; apply sum_eq_zero; intro l hl
    have h : ¬Q p l := fun h => ex ⟨l,hl,h⟩
    simp [weight,h]

private theorem inherit {V K : Type*} (U V' : Finset V) (f : V → K) (sub : V' ⊆ U)
    (cap : ∀ v ∈ V', (fiber U f (f v)).card ≤ 3) (k : K) : (fiber V' f k).card ≤ 3 := by
  classical
  by_cases ne : (fiber V' f k).Nonempty
  · obtain ⟨v,hv⟩ := ne
    have hv' := mem_filter.mp hv
    have le : fiber V' f k ⊆ fiber U f k := filter_subset_filter _ sub
    exact (card_le_card le).trans (hv'.2 ▸ cap v hv'.1)
  · simp [not_nonempty_iff_eq_empty.mp ne]

/-- This statement uses the score convention and count of residual types from
the finite host calculation. Its size and label conditions apply only to pairs
that the residual prediction actually accepts. -/
theorem frame_bound (G : P → L → Prop) (hs : NoSquare G) (H : I → J → Prop)
    (r : P → I) (c : L → J) (A X : Finset P) (B Y : Finset L)
    (R : Finset I) (C : Finset J) (xA : X ⊆ A) (yB : Y ⊆ B) (d : ℤ)
    (row : ∀ p ∈ X, ∑ l ∈ B, hit G p l ≤ d)
    (col : ∀ l ∈ Y, ∑ p ∈ A, hit G p l ≤ d)
    (live : ∀ p ∈ A, p ∉ X → ∀ l ∈ B, l ∉ Y → H (r p) (c l) →
       r p ∈ R ∧ c l ∈ C ∧ (fiber A r (r p)).card ≤ 3 ∧ (fiber B c (c l)).card ≤ 3)
    (limit : R.card ≤ 28) :
    score G (fun p l => H (r p) (c l)) A B ≤
      ((X.card:ℤ)+Y.card)*d - edges (fun p l => H (r p) (c l)) X Y +
        min (3*edges H R C) (3*((R.card:ℤ)+C.card)) := by
  classical
  let Q := fun p l => H (r p) (c l)
  let S := (A \ X).filter fun p => ∃ l ∈ B \ Y, Q p l
  let T := (B \ Y).filter fun l => ∃ p ∈ A \ X, Q p l
  have rp (p : P) (hp : p ∈ S) : r p ∈ R ∧ (fiber A r (r p)).card ≤ 3 := by
    obtain ⟨pm,l,lm,h⟩ := mem_filter.mp hp
    have h' := live p (mem_sdiff.mp pm).1 (mem_sdiff.mp pm).2 l
      (mem_sdiff.mp lm).1 (mem_sdiff.mp lm).2 h
    exact ⟨h'.1,h'.2.2.1⟩
  have cp (l : L) (hl : l ∈ T) : c l ∈ C ∧ (fiber B c (c l)).card ≤ 3 := by
    obtain ⟨lm,p,pm,h⟩ := mem_filter.mp hl
    have h' := live p (mem_sdiff.mp pm).1 (mem_sdiff.mp pm).2 l
      (mem_sdiff.mp lm).1 (mem_sdiff.mp lm).2 h
    exact ⟨h'.2.1,h'.2.2.2⟩
  have rx := fun p (hp : p ∈ S) => (rp p hp).1
  have cy := fun l (hl : l ∈ T) => (cp l hl).1
  have sr (i : I) (_ : i ∈ R) : (fiber S r i).card ≤ 3 :=
    inherit A S r (fun p hp => (mem_sdiff.mp (mem_filter.mp hp).1).1) (fun p hp => (rp p hp).2) i
  have sc (j : J) (_ : j ∈ C) : (fiber T c j).card ≤ 3 :=
    inherit B T c (fun l hl => (mem_sdiff.mp (mem_filter.mp hl).1).1) (fun l hl => (cp l hl).2) j
  have tb := residual_types G hs H r c S T R C rx cy sr sc limit
  have eb := residual_edges G hs H r c S T R C rx cy sr sc
  have mid : score G Q S T ≤ min (3*edges H R C) (3*((R.card:ℤ)+C.card)) := le_min eb tb
  have trim : score G Q S T = score G Q (A \ X) (B \ Y) := score_incident G Q _ _
  have cent := center_decomposition G Q A X B Y xA yB d row col
  change score G Q A B ≤ ((X.card:ℤ)+Y.card)*d - edges Q X Y + _
  linarith

/-- The host calculation only needs degree seventeen. Each frame has at most
ten centers, so its upper bound grows by at most ten per additional degree. -/
theorem stretch {t d rem g : ℤ} (size : t ≤ 10) (degree : 17 ≤ d)
    (at17 : t*17 + rem ≤ 158) (actual : g ≤ t*d + rem) : g ≤ 10*d-12 := by
  nlinarith [mul_nonneg (show 0 ≤ 10-t by omega) (show 0 ≤ d-17 by omega)]

#print axioms frame_bound
#print axioms stretch
end GainGeometry
