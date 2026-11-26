import FusionProfiles

/- Only canonical and row-plus-singleton witnesses are needed for the local
profile obstruction. The dual column-plus-singleton constraints are omitted. -/
namespace FusionRowMixed

open FusionCanonical FusionFull FusionMixed FusionProfiles

variable {R C : Type*}

def RowMixedWitness (G : R → C → Prop) (F : Set (Set (Zero G))) : Prop :=
  (∃ r c, G r c ∧ F = canonical G r c) ∨
  (∃ (r : R) (c : C) (z : Zero G), G r c ∧ z.val.2 = c ∧ F = upTwo (row G r) {z})

def RowMixedCover (G : R → C → Prop) (k : Nat) : Prop :=
  ∃ E H : Fin k → Set (Zero G),
    ∀ F, RowMixedWitness G F → ∃ i, Covers F (E i) (H i)

theorem mixed_cover_implies_row_mixed {G : R → C → Prop} {k : Nat}
    (h : MixedCover G k) : RowMixedCover G k := by
  obtain ⟨E,H,h⟩ := h
  refine ⟨E,H,?_⟩
  intro F hF
  exact h F (hF.elim Or.inl (Or.inr ∘ Or.inl))

theorem row_mixed_to_local_profile {G : R → C → Prop} {k : Nat}
    (h : RowMixedCover G k) : LocalProfileModel G k := by
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
        (Or.inr ⟨r,c,z,hrc,rfl,rfl⟩)
      exact covers_opposes E H i hi

#print axioms mixed_cover_implies_row_mixed
#print axioms row_mixed_to_local_profile

end FusionRowMixed
