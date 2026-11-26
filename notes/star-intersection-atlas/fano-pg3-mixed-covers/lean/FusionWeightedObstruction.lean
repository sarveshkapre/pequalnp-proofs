import Mathlib.Tactic

/- Pair weights give a dual obstruction for any finite incidence system in
which two distinct points lie on exactly one line.  The weights may depend
on semantic profiles; no assumption on their origin enters this theorem. -/
namespace FusionWeightedObstruction

open scoped BigOperators

variable {P L : Type*} [Fintype P] [Fintype L]

def lineWeight (I : P → L → Prop) [DecidableRel I]
    (w : P → P → ℤ) (l : L) : ℤ :=
  ∑ p, ∑ q, if I p l ∧ I q l then w p q else 0

theorem sum_on_three (J : P → Prop) [DecidablePred J]
    (f : P → ℤ) (i j k : P) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hJ : ∀ p, J p ↔ p = i ∨ p = j ∨ p = k) :
    (∑ p, if J p then f p else 0) = f i + f j + f k := by
  classical
  have hs : Finset.univ.filter J = {i,j,k} := by
    ext p
    simp [hJ]
  rw [← Finset.sum_filter, hs]
  simp [hij, hik, hjk, add_assoc]

theorem lineWeight_three (I : P → L → Prop) [DecidableRel I]
    (w : P → P → ℤ) (hdiag : ∀ p, w p p = 0)
    (hsymm : ∀ p q, w p q = w q p)
    (l : L) (i j k : P) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hI : ∀ p, I p l ↔ p = i ∨ p = j ∨ p = k) :
    lineWeight I w l = 2 * (w i j + w i k + w j k) := by
  classical
  unfold lineWeight
  simp_rw [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [sum_on_three (fun p => I p l) _ i j k hij hik hjk hI]
  rw [sum_on_three (fun p => I p l) _ i j k hij hik hjk hI,
    sum_on_three (fun p => I p l) _ i j k hij hik hjk hI,
    sum_on_three (fun p => I p l) _ i j k hij hik hjk hI]
  rw [hdiag i, hdiag j, hdiag k, hsymm j i, hsymm k i, hsymm k j]
  ring

theorem sum_incident_pair (I : P → L → Prop) [DecidableRel I]
    (w : P → P → ℤ) (p q : P) (hdiag : ∀ p, w p p = 0)
    (joining : ∀ p q, p ≠ q → ∃! l, I p l ∧ I q l) :
    (∑ l, if I p l ∧ I q l then w p q else 0) = w p q := by
  classical
  by_cases hpq : p = q
  · subst q
    simp [hdiag]
  · obtain ⟨l, hl, hu⟩ := joining p q hpq
    rw [Finset.sum_eq_single l]
    · simp [hl]
    · intro l' _ hne
      have hn : ¬ (I p l' ∧ I q l') := by
        intro h
        exact hne (hu l' h)
      simp [hn]
    · simp

theorem sum_lineWeight (I : P → L → Prop) [DecidableRel I]
    (w : P → P → ℤ) (hdiag : ∀ p, w p p = 0)
    (joining : ∀ p q, p ≠ q → ∃! l, I p l ∧ I q l) :
    (∑ l, lineWeight I w l) = ∑ p, ∑ q, w p q := by
  classical
  unfold lineWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  exact sum_incident_pair I w p q hdiag joining

/-- A positive total weight cannot be partitioned into nonpositive lines. -/
theorem no_pair_weight_certificate
    (I : P → L → Prop) [DecidableRel I]
    (w : P → P → ℤ) (hdiag : ∀ p, w p p = 0)
    (joining : ∀ p q, p ≠ q → ∃! l, I p l ∧ I q l)
    (positive : 0 < ∑ p, ∑ q, w p q)
    (nonpositive : ∀ l, lineWeight I w l ≤ 0) : False := by
  have hsum : (∑ l, lineWeight I w l) ≤ 0 :=
    Finset.sum_nonpos (fun l _ => nonpositive l)
  rw [sum_lineWeight I w hdiag joining] at hsum
  omega

#print axioms sum_lineWeight
#print axioms lineWeight_three
#print axioms no_pair_weight_certificate

end FusionWeightedObstruction
