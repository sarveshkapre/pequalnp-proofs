import FusionMixed

/-!
Signed partial-word profiles of actual fusion operands. The antichain argument
is the one published in discussion 19729, comment 19913262. The local condition
retains, in addition, a singleton profile compatible with its containing row and
column and opposed to every incident row at that column.

This is a necessary condition only. No saturation or finite Fano obstruction is
assumed or asserted here.
-/
namespace FusionProfiles

open FusionCanonical FusionFull FusionMixed

variable {R C X : Type*} {k : Nat}

/-- 0 is a wildcard; 1 and 2 are the two exclusive operand orientations. -/
abbrev Word (k : Nat) := Fin k → Fin 3

noncomputable def profile (E H : Fin k → Set X) (S : Set X) : Word k := by
  classical
  exact fun i => if S ⊆ E i then (if S ⊆ H i then 0 else 1)
    else (if S ⊆ H i then 2 else 0)

def Opposes (a b : Word k) : Prop :=
  ∃ i, (a i = 1 ∧ b i = 2) ∨ (a i = 2 ∧ b i = 1)

def Compatible (a b : Word k) : Prop := ¬ Opposes a b

/-- Every fixed coordinate of a is retained by b. -/
def Refines (a b : Word k) : Prop := ∀ i, a i ≠ 0 → b i = a i

theorem profile_eq_one_iff (E H : Fin k → Set X) (S : Set X) (i : Fin k) :
    profile E H S i = 1 ↔ S ⊆ E i ∧ ¬ S ⊆ H i := by
  classical
  by_cases hE : S ⊆ E i <;> by_cases hH : S ⊆ H i <;>
    simp [profile,hE,hH]

theorem profile_eq_two_iff (E H : Fin k → Set X) (S : Set X) (i : Fin k) :
    profile E H S i = 2 ↔ S ⊆ H i ∧ ¬ S ⊆ E i := by
  classical
  by_cases hE : S ⊆ E i <;> by_cases hH : S ⊆ H i <;>
    simp [profile,hE,hH]

theorem Opposes.symm {a b : Word k} (h : Opposes a b) : Opposes b a := by
  obtain ⟨i,h | h⟩ := h
  · exact ⟨i,Or.inr ⟨h.2,h.1⟩⟩
  · exact ⟨i,Or.inl ⟨h.2,h.1⟩⟩

theorem Compatible.symm {a b : Word k} (h : Compatible a b) : Compatible b a :=
  fun hb => h hb.symm

theorem refines_refl (a : Word k) : Refines a a := fun _ _ => rfl

theorem Refines.trans {a b c : Word k} (hab : Refines a b) (hbc : Refines b c) :
    Refines a c := by
  intro i hi
  have hbi := hab i hi
  exact (hbc i (by simpa only [hbi] using hi)).trans hbi

theorem Opposes.of_refines_left {a b p : Word k}
    (h : Opposes a p) (hab : Refines a b) : Opposes b p := by
  obtain ⟨i,h | h⟩ := h
  · have hi : a i ≠ 0 := by rw [h.1]; decide
    exact ⟨i,Or.inl ⟨(hab i hi).trans h.1,h.2⟩⟩
  · have hi : a i ≠ 0 := by rw [h.1]; decide
    exact ⟨i,Or.inr ⟨(hab i hi).trans h.1,h.2⟩⟩

theorem Opposes.of_refines_right {a b p : Word k}
    (h : Opposes p a) (hab : Refines a b) : Opposes p b :=
  (h.symm.of_refines_left hab).symm

theorem subset_compatible (E H : Fin k → Set X) {S T : Set X} (hST : S ⊆ T) :
    Compatible (profile E H S) (profile E H T) := by
  rintro ⟨i,h | h⟩
  · have hS := (profile_eq_one_iff E H S i).mp h.1
    have hT := (profile_eq_two_iff E H T i).mp h.2
    exact hS.2 (hST.trans hT.1)
  · have hS := (profile_eq_two_iff E H S i).mp h.1
    have hT := (profile_eq_one_iff E H T i).mp h.2
    exact hS.2 (hST.trans hT.1)

theorem covers_opposes (E H : Fin k → Set X) {A B : Set X} (i : Fin k)
    (h : Covers (upTwo A B) (E i) (H i)) :
    Opposes (profile E H A) (profile E H B) := by
  rcases covers_upTwo_iff.mp h with ⟨hA,hB⟩ | ⟨hA,hB⟩
  · exact ⟨i,Or.inl ⟨(profile_eq_one_iff E H A i).mpr hA,
      (profile_eq_two_iff E H B i).mpr hB⟩⟩
  · exact ⟨i,Or.inr ⟨(profile_eq_two_iff E H A i).mpr hA,
      (profile_eq_one_iff E H B i).mpr hB⟩⟩

theorem opposes_iff_covered (E H : Fin k → Set X) (A B : Set X) :
    Opposes (profile E H A) (profile E H B) ↔
      ∃ i, Covers (upTwo A B) (E i) (H i) := by
  constructor
  · rintro ⟨i,h | h⟩
    · exact ⟨i,covers_upTwo_iff.mpr (Or.inl
        ⟨(profile_eq_one_iff E H A i).mp h.1,
          (profile_eq_two_iff E H B i).mp h.2⟩)⟩
    · exact ⟨i,covers_upTwo_iff.mpr (Or.inr
        ⟨(profile_eq_two_iff E H A i).mp h.1,
          (profile_eq_one_iff E H B i).mp h.2⟩)⟩
  · rintro ⟨i,hi⟩
    exact covers_opposes E H i hi

def LocalProfileCondition (G : R → C → Prop)
    (rowWords : R → Word k) (colWords : C → Word k) : Prop :=
  (∀ r c, G r c → Opposes (rowWords r) (colWords c)) ∧
  ∀ a c, ¬ G a c → ∃ p : Word k,
    Compatible (rowWords a) p ∧ Compatible (colWords c) p ∧
    ∀ r, G r c → Opposes (rowWords r) p

def LocalProfileModel (G : R → C → Prop) (k : Nat) : Prop :=
  ∃ rowWords : R → Word k, ∃ colWords : C → Word k,
    LocalProfileCondition G rowWords colWords

theorem mixed_cover_to_local_profile {G : R → C → Prop} {k : Nat}
    (h : MixedCover G k) : LocalProfileModel G k := by
  obtain ⟨E,H,hcover⟩ := h
  refine ⟨fun r => profile E H (row G r), fun c => profile E H (col G c), ?_, ?_⟩
  · intro r c hrc
    obtain ⟨i,hi⟩ := hcover (canonical G r c) (Or.inl ⟨r,c,hrc,rfl⟩)
    exact covers_opposes E H i hi
  · intro a c hac
    let z : Zero G := ⟨(a,c),hac⟩
    refine ⟨profile E H {z}, ?_, ?_, ?_⟩
    · exact (subset_compatible E H (Set.singleton_subset_iff.mpr rfl :
        ({z} : Set (Zero G)) ⊆ row G a)).symm
    · exact (subset_compatible E H (Set.singleton_subset_iff.mpr rfl :
        ({z} : Set (Zero G)) ⊆ col G c)).symm
    · intro r hrc
      obtain ⟨i,hi⟩ := hcover (upTwo (row G r) {z})
        (Or.inr (Or.inl ⟨r,c,z,hrc,rfl,rfl⟩))
      exact covers_opposes E H i hi

theorem full_cover_to_local_profile {G : R → C → Prop} {k : Nat}
    (hr : ∀ r, (row G r).Nonempty) (hc : ∀ c, (col G c).Nonempty)
    (h : FullCover G k) : LocalProfileModel G k :=
  mixed_cover_to_local_profile (full_cover_implies_mixed hr hc h)

def RowAntichain (rowWords : R → Word k) : Prop :=
  ∀ r s, r ≠ s → ¬ Refines (rowWords r) (rowWords s)

theorem row_antichain {G : R → C → Prop}
    {rowWords : R → Word k} {colWords : C → Word k}
    (h : LocalProfileCondition G rowWords colWords)
    (separates : ∀ r s, r ≠ s → ∃ c, G r c ∧ ¬ G s c) :
    RowAntichain rowWords := by
  intro r s hrs href
  obtain ⟨c,hrc,hsc⟩ := separates r s hrs
  obtain ⟨p,hcompat,_,hop⟩ := h.2 s c hsc
  exact hcompat ((hop r hrc).of_refines_left href)

theorem RowAntichain.injective {rowWords : R → Word k}
    (h : RowAntichain rowWords) : Function.Injective rowWords := by
  intro r s hrs
  by_contra hne
  apply h r s hne
  rw [hrs]
  exact refines_refl _

theorem local_profile_has_row_antichain {G : R → C → Prop} {k : Nat}
    (separates : ∀ r s, r ≠ s → ∃ c, G r c ∧ ¬ G s c)
    (h : LocalProfileModel G k) :
    ∃ rowWords : R → Word k, ∃ colWords : C → Word k,
      LocalProfileCondition G rowWords colWords ∧ RowAntichain rowWords := by
  obtain ⟨rowWords,colWords,hw⟩ := h
  exact ⟨rowWords,colWords,hw,row_antichain hw separates⟩

#print axioms subset_compatible
#print axioms opposes_iff_covered
#print axioms mixed_cover_to_local_profile
#print axioms full_cover_to_local_profile
#print axioms row_antichain
#print axioms RowAntichain.injective
#print axioms local_profile_has_row_antichain

end FusionProfiles
