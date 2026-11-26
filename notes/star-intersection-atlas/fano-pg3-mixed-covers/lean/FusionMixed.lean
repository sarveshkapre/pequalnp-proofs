import FusionFull

/-!
Mixed two-generator semifilters. The row/singleton argument builds on the
partial-word observation published in discussion 19729, comment 19913262.

The finite interface below preserves actual operand membership. It does not
replace operands by independent row/column profiles, impose disjointness, or
assume a gate order. This module does not assert a finite Fano exclusion.
-/
namespace FusionMixed

open FusionCanonical FusionFull

variable {R C X I : Type*}

def upTwo (A B : Set X) : Set (Set X) := {W | A ⊆ W ∨ B ⊆ W}

theorem upTwo_semifilter {A B : Set X} (hA : A.Nonempty) (hB : B.Nonempty) :
    SemiFilter (upTwo A B) := by
  refine ⟨⟨Set.univ, Or.inl (Set.subset_univ _)⟩, ?_, ?_⟩
  · rintro (h | h)
    · obtain ⟨a, ha⟩ := hA
      exact h ha
    · obtain ⟨b, hb⟩ := hB
      exact h hb
  · intro S hS T hST
    exact hS.elim (fun h => Or.inl (h.trans hST)) (fun h => Or.inr (h.trans hST))

theorem canonical_eq_upTwo (G : R → C → Prop) (r : R) (c : C) :
    canonical G r c = upTwo (row G r) (col G c) := rfl

theorem covers_upTwo_iff {A B E H : Set X} :
    Covers (upTwo A B) E H ↔
      ((A ⊆ E ∧ ¬ A ⊆ H) ∧ (B ⊆ H ∧ ¬ B ⊆ E)) ∨
      ((A ⊆ H ∧ ¬ A ⊆ E) ∧ (B ⊆ E ∧ ¬ B ⊆ H)) := by
  simp only [Covers, upTwo, Set.mem_ofPred_eq, Set.subset_inter_iff]
  tauto

theorem not_preserves_iff_covers {F : Set (Set X)} {E H : Set X} :
    ¬ Preserves F E H ↔ Covers F E H := by
  simp only [Preserves, Covers]
  tauto

/- Adding cells omitted by both operands to both operands preserves every
exclusive containment profile. The resulting pair covers the whole ground set.
This claim concerns two-generator semifilters, not arbitrary semifilters. -/
def saturate (E H : Set X) : Set X := E ∪ (E ∪ H)ᶜ

theorem exclusive_saturate {A E H : Set X}
    (hE : A ⊆ E) (hH : ¬ A ⊆ H) :
    A ⊆ saturate E H ∧ ¬ A ⊆ saturate H E := by
  refine ⟨fun x hx => Or.inl (hE hx), ?_⟩
  intro h
  apply hH
  intro x hx
  rcases h hx with hmem | hnone
  · exact hmem
  · exact (hnone (Or.inr (hE hx))).elim

theorem saturate_union (E H : Set X) :
    saturate E H ∪ saturate H E = Set.univ := by
  ext x
  simp only [saturate,Set.mem_union,Set.mem_compl_iff,Set.mem_univ]
  tauto

theorem covers_upTwo_saturate {A B E H : Set X}
    (h : Covers (upTwo A B) E H) :
    Covers (upTwo A B) (saturate E H) (saturate H E) := by
  rcases covers_upTwo_iff.mp h with ⟨hA,hB⟩ | ⟨hA,hB⟩
  · exact covers_upTwo_iff.mpr (Or.inl
      ⟨exclusive_saturate hA.1 hA.2, exclusive_saturate hB.1 hB.2⟩)
  · exact covers_upTwo_iff.mpr (Or.inr
      ⟨exclusive_saturate hA.1 hA.2, exclusive_saturate hB.1 hB.2⟩)

def MixedWitness (G : R → C → Prop) (F : Set (Set (Zero G))) : Prop :=
  (∃ r c, G r c ∧ F = canonical G r c) ∨
  (∃ r c, ∃ z : Zero G, G r c ∧ z.val.2 = c ∧
    F = upTwo (row G r) {z}) ∨
  (∃ r c, ∃ z : Zero G, G r c ∧ z.val.1 = r ∧
    F = upTwo (col G c) {z})

def MixedCover (G : R → C → Prop) (k : Nat) : Prop :=
  ∃ E H : Fin k → Set (Zero G),
    ∀ F, MixedWitness G F → ∃ i, Covers F (E i) (H i)

theorem MixedWitness.two_generators {G : R → C → Prop} {F : Set (Set (Zero G))}
    (h : MixedWitness G F) : ∃ A B, F = upTwo A B := by
  rcases h with ⟨r,c,_,rfl⟩ | ⟨r,c,z,_,_,rfl⟩ | ⟨r,c,z,_,_,rfl⟩
  · exact ⟨row G r,col G c,rfl⟩
  · exact ⟨row G r,{z},rfl⟩
  · exact ⟨col G c,{z},rfl⟩

theorem mixed_cover_iff_saturated {G : R → C → Prop} {k : Nat} :
    MixedCover G k ↔ ∃ E H : Fin k → Set (Zero G),
      (∀ i, E i ∪ H i = Set.univ) ∧
      ∀ F, MixedWitness G F → ∃ i, Covers F (E i) (H i) := by
  constructor
  · rintro ⟨E,H,hcover⟩
    refine ⟨fun i => saturate (E i) (H i), fun i => saturate (H i) (E i),
      fun i => saturate_union _ _, ?_⟩
    intro F hw
    obtain ⟨i,hi⟩ := hcover F hw
    obtain ⟨A,B,rfl⟩ := hw.two_generators
    exact ⟨i,covers_upTwo_saturate hi⟩
  · rintro ⟨E,H,_,hcover⟩
    exact ⟨E,H,hcover⟩

/-- Each listed witness is a proper semifilter above the indicated target edge. -/
theorem MixedWitness.above {G : R → C → Prop} {F : Set (Set (Zero G))}
    (hr : ∀ r, (row G r).Nonempty) (hc : ∀ c, (col G c).Nonempty)
    (hw : MixedWitness G F) :
    ∃ r c, G r c ∧ SemiFilter F ∧ row G r ∈ F ∧ col G c ∈ F := by
  rcases hw with ⟨r,c,hrc,rfl⟩ | ⟨r,c,z,hrc,hz,rfl⟩ | ⟨r,c,z,hrc,hz,rfl⟩
  · exact ⟨r,c,hrc,upTwo_semifilter (hr r) (hc c),
      Or.inl (Set.Subset.refl _), Or.inr (Set.Subset.refl _)⟩
  · refine ⟨r,c,hrc,upTwo_semifilter (hr r) (Set.singleton_nonempty z),
      Or.inl (Set.Subset.refl _), Or.inr ?_⟩
    exact Set.singleton_subset_iff.mpr hz
  · refine ⟨r,c,hrc,upTwo_semifilter (hc c) (Set.singleton_nonempty z),
      Or.inr ?_, Or.inl (Set.Subset.refl _)⟩
    exact Set.singleton_subset_iff.mpr hz

theorem full_cover_implies_mixed {G : R → C → Prop} {k : Nat}
    (hr : ∀ r, (row G r).Nonempty) (hc : ∀ c, (col G c).Nonempty) :
    FullCover G k → MixedCover G k := by
  rintro ⟨E,H,hcover⟩
  refine ⟨E,H,?_⟩
  intro F hw
  obtain ⟨r,c,hrc,hF,hrow,hcol⟩ := hw.above hr hc
  obtain ⟨i,hi⟩ := hcover r c hrc F hF hrow hcol
  exact ⟨i,not_preserves_iff_covers.mp hi⟩

theorem mixed_cover_mono {G : R → C → Prop} {k l : Nat}
    (hkl : k ≤ l) (h : MixedCover G k) : MixedCover G l := by
  obtain ⟨E,H,hcover⟩ := h
  let E' (i : Fin l) : Set (Zero G) := if hi : i.val < k then E ⟨i.val,hi⟩ else ∅
  let H' (i : Fin l) : Set (Zero G) := if hi : i.val < k then H ⟨i.val,hi⟩ else ∅
  refine ⟨E',H',?_⟩
  intro F hw
  obtain ⟨i,hi⟩ := hcover F hw
  refine ⟨i.castLE hkl,?_⟩
  simpa only [E',H',Fin.val_castLE,dite_eq_left i.isLt] using hi

/-! Finite operand-membership interface. All generator sets are explicit finite
sets; operands remain arbitrary Boolean membership functions on the whole ground
type. Nothing forces different witnesses to choose the same covering pair. -/

def bitSet (w : X → Bool) : Set X := {x | w x = true}

def subsetBits (A : Finset X) (w : X → Bool) : Bool :=
  decide (∀ x ∈ A, w x = true)

theorem coe_subset_bitSet_iff (A : Finset X) (w : X → Bool) :
    (A : Set X) ⊆ bitSet w ↔ subsetBits A w = true := by
  simp [subsetBits,bitSet,Set.subset_def]

def coveredBits (A B : Finset X) (E H : X → Bool) : Bool :=
  ((subsetBits A E && !(subsetBits A H)) && (subsetBits B H && !(subsetBits B E))) ||
  ((subsetBits A H && !(subsetBits A E)) && (subsetBits B E && !(subsetBits B H)))

theorem covers_upTwo_bits_iff (A B : Finset X) (E H : X → Bool) :
    Covers (upTwo (A : Set X) (B : Set X)) (bitSet E) (bitSet H) ↔
      coveredBits A B E H = true := by
  rw [covers_upTwo_iff]
  simp only [coe_subset_bitSet_iff]
  cases hAE : subsetBits A E <;> cases hAH : subsetBits A H <;>
    cases hBE : subsetBits B E <;> cases hBH : subsetBits B H <;>
      simp [coveredBits,hAE,hAH,hBE,hBH]

def FiniteCovered (A B : I → Finset X) {k : Nat}
    (E H : Fin k → X → Bool) : Prop :=
  ∀ j, ∃ i, coveredBits (A j) (B j) (E i) (H i) = true

theorem finite_covered_iff (A B : I → Finset X) {k : Nat}
    (E H : Fin k → X → Bool) :
    FiniteCovered A B E H ↔
      ∀ j, ∃ i, Covers (upTwo (A j : Set X) (B j : Set X)) (bitSet (E i)) (bitSet (H i)) := by
  simp only [FiniteCovered,covers_upTwo_bits_iff]

theorem bitSet_decide (S : Set X) [DecidablePred (· ∈ S)] :
    bitSet (fun x => decide (x ∈ S)) = S := by
  ext x
  simp [bitSet]

/-- Soundness suffices for a lower bound: the finite catalogue need not contain
every mixed witness, and may contain duplicates. -/
theorem mixed_cover_to_finite {G : R → C → Prop} {k : Nat}
    (A B : I → Finset (Zero G))
    (hw : ∀ j, MixedWitness G (upTwo (A j : Set (Zero G)) (B j : Set (Zero G))))
    (h : MixedCover G k) :
    ∃ E H : Fin k → Zero G → Bool, FiniteCovered A B E H := by
  classical
  obtain ⟨E,H,hcover⟩ := h
  refine ⟨fun i x => decide (x ∈ E i), fun i x => decide (x ∈ H i), ?_⟩
  apply (finite_covered_iff _ _ _ _).2
  intro j
  obtain ⟨i,hi⟩ := hcover _ (hw j)
  exact ⟨i,by simpa only [bitSet_decide] using hi⟩

theorem full_cover_to_finite {G : R → C → Prop} {k : Nat}
    (hr : ∀ r, (row G r).Nonempty) (hc : ∀ c, (col G c).Nonempty)
    (A B : I → Finset (Zero G))
    (hw : ∀ j, MixedWitness G (upTwo (A j : Set (Zero G)) (B j : Set (Zero G))))
    (h : FullCover G k) :
    ∃ E H : Fin k → Zero G → Bool, FiniteCovered A B E H :=
  mixed_cover_to_finite A B hw (full_cover_implies_mixed hr hc h)

/-- Every cell may be required to belong to at least one operand of each pair
when searching for a cover of this two-generator witness family. -/
theorem mixed_cover_to_finite_saturated {G : R → C → Prop} {k : Nat}
    (A B : I → Finset (Zero G))
    (hw : ∀ j, MixedWitness G (upTwo (A j : Set (Zero G)) (B j : Set (Zero G))))
    (h : MixedCover G k) :
    ∃ E H : Fin k → Zero G → Bool,
      (∀ i x, E i x = true ∨ H i x = true) ∧ FiniteCovered A B E H := by
  classical
  obtain ⟨E,H,total,hcover⟩ := mixed_cover_iff_saturated.mp h
  refine ⟨fun i x => decide (x ∈ E i), fun i x => decide (x ∈ H i), ?_, ?_⟩
  · intro i x
    have hx : x ∈ E i ∪ H i := by rw [total i]; trivial
    simpa only [decide_eq_true_eq,Set.mem_union] using hx
  · apply (finite_covered_iff _ _ _ _).2
    intro j
    obtain ⟨i,hi⟩ := hcover _ (hw j)
    exact ⟨i,by simpa only [bitSet_decide] using hi⟩

theorem full_cover_to_finite_saturated {G : R → C → Prop} {k : Nat}
    (hr : ∀ r, (row G r).Nonempty) (hc : ∀ c, (col G c).Nonempty)
    (A B : I → Finset (Zero G))
    (hw : ∀ j, MixedWitness G (upTwo (A j : Set (Zero G)) (B j : Set (Zero G))))
    (h : FullCover G k) :
    ∃ E H : Fin k → Zero G → Bool,
      (∀ i x, E i x = true ∨ H i x = true) ∧ FiniteCovered A B E H :=
  mixed_cover_to_finite_saturated A B hw (full_cover_implies_mixed hr hc h)

/-- An optional complete catalogue also gives an exact equivalence. -/
theorem mixed_cover_iff_finite {G : R → C → Prop} {k : Nat}
    (A B : I → Finset (Zero G))
    (catalogue : ∀ F, MixedWitness G F ↔
      ∃ j, F = upTwo (A j : Set (Zero G)) (B j : Set (Zero G))) :
    MixedCover G k ↔ ∃ E H : Fin k → Zero G → Bool, FiniteCovered A B E H := by
  constructor
  · exact mixed_cover_to_finite A B (fun j => (catalogue _).2 ⟨j,rfl⟩)
  · rintro ⟨E,H,hcover⟩
    refine ⟨fun i => bitSet (E i), fun i => bitSet (H i), ?_⟩
    intro F hw
    obtain ⟨j,rfl⟩ := (catalogue F).1 hw
    exact (finite_covered_iff A B E H).1 hcover j

#print axioms covers_upTwo_iff
#print axioms covers_upTwo_saturate
#print axioms mixed_cover_iff_saturated
#print axioms MixedWitness.above
#print axioms full_cover_implies_mixed
#print axioms covers_upTwo_bits_iff
#print axioms mixed_cover_to_finite
#print axioms full_cover_to_finite
#print axioms full_cover_to_finite_saturated
#print axioms mixed_cover_iff_finite

end FusionMixed
