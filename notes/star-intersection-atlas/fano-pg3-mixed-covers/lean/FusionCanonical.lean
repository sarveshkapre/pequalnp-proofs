import Mathlib.Tactic

/-
Canonical semifilters from Cavalar--Oliveira, arXiv:2503.14117, Sections 3.1 and 4.2.
The ground type is the set of nonedges, so every operand is genuinely a subset
of the required ambient space. No disjointness restriction is put on a pair.
-/
namespace FusionCanonical

variable {R C X : Type*}

abbrev Zero (G : R → C → Prop) := {z : R × C // ¬ G z.1 z.2}

def row (G : R → C → Prop) (r : R) : Set (Zero G) := {z | z.val.1 = r}
def col (G : R → C → Prop) (c : C) : Set (Zero G) := {z | z.val.2 = c}

def SemiFilter (F : Set (Set X)) : Prop :=
  F.Nonempty ∧ ∅ ∉ F ∧ ∀ S ∈ F, ∀ T, S ⊆ T → T ∈ F

def canonical (G : R → C → Prop) (r : R) (c : C) : Set (Set (Zero G)) :=
  {W | row G r ⊆ W ∨ col G c ⊆ W}

def Covers (F : Set (Set X)) (E H : Set X) : Prop :=
  E ∈ F ∧ H ∈ F ∧ E ∩ H ∉ F

def Preserves (F : Set (Set X)) (E H : Set X) : Prop :=
  E ∈ F → H ∈ F → E ∩ H ∈ F

def CanonicalCover (G : R → C → Prop) (k : ℕ) : Prop :=
  ∃ E H : Fin k → Set (Zero G), ∀ r c, G r c →
    SemiFilter (canonical G r c) → ∃ i, Covers (canonical G r c) (E i) (H i)

theorem canonical_semifilter {G : R → C → Prop} {r : R} {c : C}
    (hr : ∃ c', ¬ G r c') (hc : ∃ r', ¬ G r' c) :
    SemiFilter (canonical G r c) := by
  refine ⟨⟨Set.univ, Or.inl (Set.subset_univ _)⟩, ?_, ?_⟩
  · rintro (h | h)
    · obtain ⟨c', hrc⟩ := hr
      exact h (show (⟨(r, c'), hrc⟩ : Zero G) ∈ row G r from rfl)
    · obtain ⟨r', hrc⟩ := hc
      exact h (show (⟨(r', c), hrc⟩ : Zero G) ∈ col G c from rfl)
  · intro S hS T hST
    exact hS.elim (fun h => Or.inl (h.trans hST)) (fun h => Or.inr (h.trans hST))

theorem covers_iff {G : R → C → Prop} {r : R} {c : C} {E H : Set (Zero G)} :
    Covers (canonical G r c) E H ↔
      ((row G r ⊆ E ∧ ¬ row G r ⊆ H) ∧ (col G c ⊆ H ∧ ¬ col G c ⊆ E)) ∨
      ((row G r ⊆ H ∧ ¬ row G r ⊆ E) ∧ (col G c ⊆ E ∧ ¬ col G c ⊆ H)) := by
  simp only [Covers, canonical, Set.mem_ofPred_eq, Set.subset_inter_iff]
  tauto

/- Both color classes must meet every nonedge star. -/
structure SplitZeros (G : R → C → Prop) (A : Set R) (B : Set C) : Prop where
  row_in : ∀ r, ∃ c, ¬ G r c ∧ c ∈ B
  row_out : ∀ r, ∃ c, ¬ G r c ∧ c ∉ B
  col_in : ∀ c, ∃ r, ¬ G r c ∧ r ∈ A
  col_out : ∀ c, ∃ r, ¬ G r c ∧ r ∉ A

def left (G : R → C → Prop) (A : Set R) (B : Set C) : Set (Zero G) :=
  {z | z.val.1 ∈ A ∨ z.val.2 ∈ B}

def right (G : R → C → Prop) (A : Set R) (B : Set C) : Set (Zero G) :=
  {z | z.val.1 ∉ A ∨ z.val.2 ∉ B}

theorem SplitZeros.compl_right {G : R → C → Prop} {A : Set R} {B : Set C}
    (h : SplitZeros G A B) : SplitZeros G A Bᶜ := by
  exact ⟨h.row_out, by simpa only [Set.mem_compl_iff, not_not] using h.row_in,
    h.col_in, h.col_out⟩

theorem row_left_iff {G : R → C → Prop} {A : Set R} {B : Set C}
    (h : SplitZeros G A B) (r : R) : row G r ⊆ left G A B ↔ r ∈ A := by
  constructor
  · intro hs
    obtain ⟨c, hrc, hc⟩ := h.row_out r
    exact (hs (show (⟨(r,c), hrc⟩ : Zero G) ∈ row G r from rfl)).resolve_right hc
  · intro hr z hz
    exact Or.inl (by simpa only [row, Set.mem_ofPred_eq] using hz ▸ hr)

theorem row_right_iff {G : R → C → Prop} {A : Set R} {B : Set C}
    (h : SplitZeros G A B) (r : R) : row G r ⊆ right G A B ↔ r ∉ A := by
  constructor
  · intro hs
    obtain ⟨c, hrc, hc⟩ := h.row_in r
    exact (hs (show (⟨(r,c), hrc⟩ : Zero G) ∈ row G r from rfl)).resolve_right (not_not_intro hc)
  · intro hr z hz
    exact Or.inl (by simpa only [row, Set.mem_ofPred_eq] using hz ▸ hr)

theorem col_left_iff {G : R → C → Prop} {A : Set R} {B : Set C}
    (h : SplitZeros G A B) (c : C) : col G c ⊆ left G A B ↔ c ∈ B := by
  constructor
  · intro hs
    obtain ⟨r, hrc, hr⟩ := h.col_out c
    exact (hs (show (⟨(r,c), hrc⟩ : Zero G) ∈ col G c from rfl)).resolve_left hr
  · intro hc z hz
    exact Or.inr (by simpa only [col, Set.mem_ofPred_eq] using hz ▸ hc)

theorem col_right_iff {G : R → C → Prop} {A : Set R} {B : Set C}
    (h : SplitZeros G A B) (c : C) : col G c ⊆ right G A B ↔ c ∉ B := by
  constructor
  · intro hs
    obtain ⟨r, hrc, hr⟩ := h.col_in c
    exact (hs (show (⟨(r,c), hrc⟩ : Zero G) ∈ col G c from rfl)).resolve_left (not_not_intro hr)
  · intro hc z hz
    exact Or.inr (by simpa only [col, Set.mem_ofPred_eq] using hz ▸ hc)

theorem covers_checkerboard_iff {G : R → C → Prop} {A : Set R} {B : Set C}
    (h : SplitZeros G A B) (r : R) (c : C) :
    Covers (canonical G r c) (left G A B) (right G A B) ↔
      ((r ∈ A ∧ c ∉ B) ∨ (r ∉ A ∧ c ∈ B)) := by
  rw [covers_iff, row_left_iff h, row_right_iff h, col_left_iff h, col_right_iff h]
  tauto

theorem canonical_two_of_split {G : R → C → Prop} {A : Set R} {B : Set C}
    (h : SplitZeros G A B) : CanonicalCover G 2 := by
  classical
  refine ⟨![left G A B, left G A Bᶜ], ![right G A B, right G A Bᶜ], ?_⟩
  intro r c _ _
  by_cases hr : r ∈ A <;> by_cases hc : c ∈ B
  · refine ⟨1, ?_⟩
    exact (covers_checkerboard_iff h.compl_right r c).2 (Or.inl ⟨hr, not_not_intro hc⟩)
  · exact ⟨0, (covers_checkerboard_iff h r c).2 (Or.inl ⟨hr,hc⟩)⟩
  · exact ⟨0, (covers_checkerboard_iff h r c).2 (Or.inr ⟨hr,hc⟩)⟩
  · exact ⟨1, (covers_checkerboard_iff h.compl_right r c).2 (Or.inr ⟨hr,hc⟩)⟩

/- A common incident column propagates a row's exclusive operand orientation. -/
theorem no_single_pair {G : R → C → Prop} {E H : Set (Zero G)}
    (common : ∀ r r', ∃ c, G r c ∧ G r' c)
    (edge : ∃ r c, G r c)
    (cover : ∀ r c, G r c → Covers (canonical G r c) E H) : False := by
  obtain ⟨r₀,c₀,he⟩ := edge
  have row_propagate : ∀ r r', row G r ⊆ E → row G r' ⊆ E := by
    intro r r' hE
    obtain ⟨c, hrc, hr'c⟩ := common r r'
    have hcH : col G c ⊆ H ∧ ¬ col G c ⊆ E := by
      rcases covers_iff.mp (cover r c hrc) with h | h
      · exact h.2
      · exact (h.1.2 hE).elim
    rcases covers_iff.mp (cover r' c hr'c) with h | h
    · exact h.1.1
    · exact (hcH.2 h.2.1).elim
  have row_propagate' : ∀ r r', row G r ⊆ H → row G r' ⊆ H := by
    intro r r' hH
    obtain ⟨c, hrc, hr'c⟩ := common r r'
    have hcE : col G c ⊆ E ∧ ¬ col G c ⊆ H := by
      rcases covers_iff.mp (cover r c hrc) with h | h
      · exact (h.1.2 hH).elim
      · exact h.2
    rcases covers_iff.mp (cover r' c hr'c) with h | h
    · exact (hcE.2 h.2.1).elim
    · exact h.1.1
  rcases covers_iff.mp (cover r₀ c₀ he) with h | h
  · apply h.2.2
    intro z _
    exact row_propagate r₀ z.val.1 h.1.1 rfl
  · apply h.2.2
    intro z _
    exact row_propagate' r₀ z.val.1 h.1.1 rfl

theorem canonical_not_one {G : R → C → Prop}
    (common : ∀ r r', ∃ c, G r c ∧ G r' c)
    (edge : ∃ r c, G r c)
    (rows : ∀ r, ∃ c, ¬ G r c) (cols : ∀ c, ∃ r, ¬ G r c) :
    ¬ CanonicalCover G 1 := by
  rintro ⟨E,H,h⟩
  apply no_single_pair common edge (E := E 0) (H := H 0)
  intro r c hrc
  obtain ⟨i,hi⟩ := h r c hrc (canonical_semifilter (rows r) (cols c))
  have hi0 : i = 0 := Subsingleton.elim _ _
  simpa only [hi0] using hi

theorem canonical_exact_two_of_split {G : R → C → Prop} {A : Set R} {B : Set C}
    (h : SplitZeros G A B)
    (common : ∀ r r', ∃ c, G r c ∧ G r' c)
    (edge : ∃ r c, G r c) :
    CanonicalCover G 2 ∧ ¬ CanonicalCover G 1 := by
  refine ⟨canonical_two_of_split h, canonical_not_one common edge ?_ ?_⟩
  · intro r; obtain ⟨c,hc,_⟩ := h.row_in r; exact ⟨c,hc⟩
  · intro c; obtain ⟨r,hr,_⟩ := h.col_in c; exact ⟨r,hr⟩

theorem canonical_zero_to_one {G : R → C → Prop}
    (h : CanonicalCover G 0) : CanonicalCover G 1 := by
  obtain ⟨E,H,hcover⟩ := h
  refine ⟨fun _ => ∅, fun _ => ∅, ?_⟩
  intro r c he hF
  obtain ⟨i,_⟩ := hcover r c he hF
  exact Fin.elim0 i

theorem canonical_minimum_two {G : R → C → Prop}
    (h : CanonicalCover G 2 ∧ ¬ CanonicalCover G 1) :
    CanonicalCover G 2 ∧ ∀ k, k < 2 → ¬ CanonicalCover G k := by
  refine ⟨h.1, ?_⟩
  intro k hk hc
  have : k = 0 ∨ k = 1 := by omega
  rcases this with rfl | rfl
  · exact h.2 (canonical_zero_to_one hc)
  · exact h.2 hc

#print axioms covers_iff
#print axioms canonical_exact_two_of_split
#print axioms canonical_minimum_two

end FusionCanonical
