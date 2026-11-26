import PEqualNP.FiveRows.Core

/-! Exact threshold for a three-intersection circuit / four-intersection formula
gap with five rows. Uses the unrestricted 5×6 classification for the lower widths. -/
namespace FiveRowThreshold
open Set TwoIntersections ThreeIntersectionsFormula

abbrev Region (n : Nat) := Set (Fin 5 × Fin n)

def GapAt (n : Nat) : Prop :=
  ∃ z : Region n, ThreeIntersections.Three Rectangle z ∧ ¬ Two Rectangle z ∧
    Formula Rectangle 4 z ∧ ∀ k, k < 4 → ¬ Formula Rectangle k z

def pull {a b : Nat} (f : Fin b → Fin a) (z : Region a) : Region b :=
  (fun p : Fin 5 × Fin b => (p.1, f p.2)) ⁻¹' z

private def foldCols {a b : Nat} (pos : 0 < a) (j : Fin b) : Fin a :=
  ⟨j.val % a, Nat.mod_lt _ pos⟩

private theorem recover {a b : Nat} (hab : a ≤ b) (pos : 0 < a) (z : Region a) :
    pull (Fin.castLE hab) (pull (foldCols pos) z) = z := by
  ext ⟨i,j⟩
  have hh : foldCols pos (Fin.castLE hab j) = j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
  change (i,foldCols pos (Fin.castLE hab j)) ∈ z ↔ (i,j) ∈ z
  rw [hh]

theorem pull_formula {a b k : Nat} (f : Fin b → Fin a) {z : Region a}
    (hz : Formula Rectangle k z) : Formula Rectangle k (pull f z) := by
  induction hz with
  | base hr =>
    obtain ⟨rows, cols, rfl⟩ := hr
    exact .base ⟨rows, f ⁻¹' cols, rfl⟩
  | meet _ _ h₁ h₂ => exact .meet h₁ h₂
  | join _ _ h₁ h₂ => exact .join h₁ h₂

theorem pull_three {a b : Nat} (f : Fin b → Fin a) {z : Region a}
    (hz : ThreeIntersections.Three Rectangle z) : ThreeIntersections.Three Rectangle (pull f z) :=
  (ThreeIntersections.rectangle_normal_iff _).mpr
    (ThreeIntersections.rectangle_normal_preimage id f ((ThreeIntersections.rectangle_normal_iff _).mp hz))

theorem two_formula {n : Nat} {z : Region n} (h : Two Rectangle z) :
    Formula Rectangle 2 z := by
  rcases (TwoIntersections.rectangle_normal_iff z).mp h with
      ⟨a,b,c,ha,hb,hc,rfl⟩ | ⟨a,b,c,d,ha,hb,hc,hd,rfl⟩
  · exact .join (.join (.base ha) (.base hb)) (.base hc)
  · exact .meet (.join (.base ha) (.base hb)) (.join (.base hc) (.base hd))

private theorem wide (n : Nat) (h : 7 ≤ n) : GapAt n := by
  let f : Fin n → Fin 7 := foldCols (by decide)
  have recover' := recover h (by decide : 0 < 7) FiveRowSharing.zero
  have lower (k : Nat) (lt : k < 4) : ¬ Formula Rectangle k (pull f FiveRowSharing.zero) := by
    intro hz
    have smaller := pull_formula (Fin.castLE h) hz
    rw [show pull (Fin.castLE h) (pull f FiveRowSharing.zero) = _ from recover'] at smaller
    exact FiveRowSharing.formula_lower lt smaller
  exact ⟨pull f FiveRowSharing.zero, pull_three f FiveRowSharing.circuit_three,
    fun two => lower 2 (by decide) (two_formula two), pull_formula f FiveRowSharing.formula_four, lower⟩

private theorem narrow (n : Nat) (h : n ≤ 6) : ¬ GapAt n := by
  rintro ⟨z, hz, _, _, lower⟩
  by_cases pos : 0 < n
  · let f : Fin 6 → Fin n := foldCols pos
    have three := pull_three f hz
    obtain ⟨hc,_,nonexception,_⟩ := Atlas56.classify Atlas56.full_cover (pull f z)
    have cub := nonexception (fun exc => (hc.mp exc) three)
    have hf := (Atlas56.cube_models cub).2
    have smaller := pull_formula (Fin.castLE h) hf
    rw [show pull (Fin.castLE h) (pull f z) = z from recover h pos z] at smaller
    exact lower 3 (by decide) smaller
  · have hn : n = 0 := by omega
    subst n
    have hr : Rectangle z := ⟨univ,univ,by ext p; exact Fin.elim0 p.2⟩
    exact lower 0 (by decide) (.base hr)

theorem gap_iff_seven_le (n : Nat) : GapAt n ↔ 7 ≤ n := by
  constructor
  · intro hg
    by_contra! tooSmall
    exact narrow n (by omega) hg
  · exact wide n

#print axioms gap_iff_seven_le
end FiveRowThreshold
