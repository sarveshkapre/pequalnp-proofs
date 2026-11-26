import PEqualNP.ThreeGateGain.TriangleAttainment

namespace TriangleOptimality
open Finset Configuration

variable {P L : Type*}

/-- Weight of a predicted positive cell, with a penalty for false positives. -/
noncomputable def signedCell (I : P → L → Prop) (p : P) (l : L) :=
  2 * hit I p l - 1

theorem gain_sum (I : P → L → Prop) (A : Finset P) (B : Finset L) :
    gain I A B = ∑ p ∈ A, ∑ l ∈ B, signedCell I p l := by
  simp [gain,edges,signedCell,sum_sub_distrib,← Finset.mul_sum]

variable [Membership P L] [ProjectivePlane P L] [Fintype P] [Fintype L]

private theorem one_row (p : P) (B : Finset L) :
    (∑ l ∈ B, signedCell (fun p l => p∈l) p l) ≤ (ProjectivePlane.order P L:ℤ)+1 := by
  classical
  rw [← row_total p]
  calc
    _ ≤ ∑ l ∈ B, hit (fun p l => p∈l) p l := by
      apply sum_le_sum; intro l _
      by_cases h : p∈l <;> simp [signedCell,hit,h]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun l _ _ => by
      by_cases h : p∈l <;> simp [hit,h])

private theorem one_col (l : L) (A : Finset P) :
    (∑ p ∈ A, signedCell (fun p l => p∈l) p l) ≤ (ProjectivePlane.order P L:ℤ)+1 := by
  classical
  rw [← col_total l]
  calc
    _ ≤ ∑ p ∈ A, hit (fun p l => p∈l) p l := by
      apply sum_le_sum; intro p _
      by_cases h : p∈l <;> simp [signedCell,hit,h]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun p _ _ => by
      by_cases h : p∈l <;> simp [hit,h])

/-- Includes the thin and empty cases needed for a partition of a circuit prediction. -/
theorem any_rectangle (A : Finset P) (B : Finset L) :
    gain (fun p l => p∈l) A B ≤ (ProjectivePlane.order P L : ℤ)+1 := by
  classical
  have q := ProjectivePlane.one_lt_order P L
  rcases le_or_gt 2 A.card with ha | ha
  · rcases le_or_gt 2 B.card with hb | hb
    · exact (plane_rectangle A B ha hb).trans (by omega)
    · rw [gain_sum,sum_comm]
      rcases B.eq_empty_or_nonempty with rfl | h
      · simp; positivity
      · obtain ⟨l,rfl⟩ := card_eq_one.mp (show B.card=1 by have := card_pos.mpr h; omega)
        simpa using one_col l A
  · rw [gain_sum]
    rcases A.eq_empty_or_nonempty with rfl | h
    · simp; positivity
    · obtain ⟨p,rfl⟩ := card_eq_one.mp (show A.card=1 by have := card_pos.mpr h; omega)
      simpa using one_row p B

/-- Disjoint row classes, with any accepted subset of columns for each class. -/
theorem error_by_classes {K : Type*} [Fintype K] (label : P → K) (columns : K → Finset L)
    (z : Set (P×L)) (hz : ∀ p l, (p,l)∉z ↔ l∈columns (label p)) :
    (Fintype.card P:ℤ) * (ProjectivePlane.order P L+1) - Fintype.card K * (ProjectivePlane.order P L+1)
      ≤ errors (fun (p:P) (l:L) => p∈l) z := by
  classical
  let rows (k : K) := univ.filter (label · = k)
  let S (p : P) (l : L) := signedCell (fun p l => p∈l) p l
  have group : (∑ k : K, gain (fun p l => p∈l) (rows k) (columns k)) =
      ∑ p : P, ∑ l ∈ columns (label p), S p l := by
    simp_rw [gain_sum]
    simp only [rows,Finset.sum_filter]
    rw [sum_comm]; apply sum_congr rfl; intro p _
    simp [S]
  have cap := sum_le_sum (s := (univ : Finset K)) (fun k _ => any_rectangle (rows k) (columns k))
  rw [group] at cap
  simp only [sum_const,card_univ,nsmul_eq_mul] at cap
  have cell (p : P) (l : L) :
      hit (fun p l => ¬ ((p,l)∉z ↔ p∈l)) p l =
        hit (fun p l => p∈l) p l - (if l∈columns (label p) then S p l else 0) := by
    simp only [hit,hz,S,signedCell]
    by_cases a : p∈l <;> by_cases b : l∈columns (label p) <;> simp [a,b]
  unfold errors
  simp_rw [cell]
  simp only [sum_sub_distrib,row_total,sum_const,card_univ,nsmul_eq_mul]
  have pick (p : P) : (∑ l : L, if l∈columns (label p) then S p l else 0) =
      ∑ l ∈ columns (label p), S p l := by
    rw [← sum_filter]; simp
  simp_rw [pick]; omega

omit [ProjectivePlane P L] in
/-- Strengthening the two normal-form bounds suffices for the exact optimum.
The hypotheses state independent inequalities on sets of cells and contain no circuit predicates. -/
theorem lower_from_two_forms (bound : ℤ)
    (nested : ∀ a b c : Set (P×L), TwoIntersections.Rectangle a → TwoIntersections.Rectangle b →
      TwoIntersections.Rectangle c → bound ≤ errors (fun (p:P) (l:L) => p∈l) ((a ∪ b) ∪ c))
    (parallel : ∀ a b c d : Set (P×L), TwoIntersections.Rectangle a → TwoIntersections.Rectangle b →
      TwoIntersections.Rectangle c → TwoIntersections.Rectangle d →
      bound ≤ errors (fun (p:P) (l:L) => p∈l) ((a ∪ b) ∩ (c ∪ d)))
    (z : Set (P×L)) (hz : TwoIntersections.Two TwoIntersections.Rectangle z) :
    bound ≤ errors (fun (p:P) (l:L) => p∈l) z := by
  rcases (TwoIntersections.rectangle_normal_iff _).mp hz with
    ⟨a,b,c,ha,hb,hc,rfl⟩ | ⟨a,b,c,d,ha,hb,hc,hd,rfl⟩
  · exact nested a b c ha hb hc
  · exact parallel a b c d ha hb hc hd

#print axioms any_rectangle
#print axioms error_by_classes
end TriangleOptimality
