import PEqualNP.SixSharing.ThreeIntersections

/-!
The shared fifth shape in `ThreeIntersections.Normal` cannot be omitted for
arbitrary meet-closed base families.  Here the base sets are positive
conjunctions on six variables, including the constant false and true sets.

The argument uses seven minimal satisfying supports and majority closure,
not exhaustive enumeration of normal-form parameters.  This is a generic
family separation; it is not asserted to be a rectangle-family separation.
-/
namespace ThreeIntersectionsSharingGap
open Set TwoIntersections

abbrev Assignment := Finset (Fin 6)

def principal (a : Assignment) : Set Assignment := {x | a ⊆ x}

def Conjunction : Family Assignment :=
  fun s => s = ∅ ∨ ∃ a, s = principal a

def diamond : Set Assignment :=
  {x | (2 ∈ x ∨ (3 ∈ x ∧ (0 ∈ x ∨ 1 ∈ x))) ∧
    (4 ∈ x ∨ (5 ∈ x ∧ (0 ∈ x ∨ 1 ∈ x)))}

def FirstFour {α : Type*} (F : Family α) (z : Set α) : Prop :=
  (∃ a b c d, F a ∧ F b ∧ F c ∧ F d ∧ z = (a ∪ b) ∪ (c ∪ d)) ∨
  (∃ a b c d e, F a ∧ F b ∧ F c ∧ F d ∧ F e ∧
    z = ((a ∪ b) ∪ c) ∩ (d ∪ e)) ∨
  (∃ a b c d e f, F a ∧ F b ∧ F c ∧ F d ∧ F e ∧ F f ∧
    z = ((a ∪ b) ∩ (c ∪ d)) ∩ (e ∪ f)) ∨
  (∃ a b c d e, F a ∧ F b ∧ F c ∧ F d ∧ F e ∧
    z = a ∪ ((b ∪ c) ∩ (d ∪ e)))

theorem conjunction_closed : Closed Conjunction := by
  rintro s t (rfl | ⟨a, rfl⟩) (rfl | ⟨b, rfl⟩)
  · exact Or.inl (by simp)
  · exact Or.inl (by simp)
  · exact Or.inl (by simp)
  · exact Or.inr ⟨a ∪ b, by ext x; simp [principal]⟩

theorem conjunction_univ : Conjunction univ := by
  exact Or.inr ⟨∅, by ext x; simp [principal]⟩

/-- A union of the positive conjunctions indexed by `g`. -/
def cover (g : Finset Assignment) : Set Assignment :=
  {x | ∃ a ∈ g, a ⊆ x}

def CoverCount (n : ℕ) (z : Set Assignment) : Prop :=
  ∃ g : Finset Assignment, g.card ≤ n ∧ z = cover g

theorem conjunction_cover {s : Set Assignment} (hs : Conjunction s) :
    CoverCount 1 s := by
  rcases hs with rfl | ⟨a, rfl⟩
  · exact ⟨∅, by simp, by ext x; simp [cover]⟩
  · exact ⟨{a}, by simp, by ext x; simp [cover, principal]⟩

theorem cover_union {m n : ℕ} {s t : Set Assignment}
    (hs : CoverCount m s) (ht : CoverCount n t) : CoverCount (m+n) (s ∪ t) := by
  rcases hs with ⟨g, hg, rfl⟩
  rcases ht with ⟨h, hh, rfl⟩
  refine ⟨g ∪ h, (Finset.card_union_le g h).trans (Nat.add_le_add hg hh), ?_⟩
  ext x
  change ((∃ a ∈ g, a ⊆ x) ∨ ∃ a ∈ h, a ⊆ x) ↔
    ∃ a ∈ g ∪ h, a ⊆ x
  constructor
  · rintro (⟨a,ha,hax⟩ | ⟨a,ha,hax⟩)
    · exact ⟨a, Finset.mem_union_left _ ha, hax⟩
    · exact ⟨a, Finset.mem_union_right _ ha, hax⟩
  · rintro ⟨a,ha,hax⟩
    rcases Finset.mem_union.mp ha with ha | ha
    · exact Or.inl ⟨a,ha,hax⟩
    · exact Or.inr ⟨a,ha,hax⟩

theorem cover_inter {m n : ℕ} {s t : Set Assignment}
    (hs : CoverCount m s) (ht : CoverCount n t) : CoverCount (m*n) (s ∩ t) := by
  rcases hs with ⟨g, hg, rfl⟩
  rcases ht with ⟨h, hh, rfl⟩
  refine ⟨(g ×ˢ h).image (fun p => p.1 ∪ p.2), ?_, ?_⟩
  · calc
      ((g ×ˢ h).image (fun p => p.1 ∪ p.2)).card ≤ (g ×ˢ h).card :=
        Finset.card_image_le
      _ = g.card * h.card := Finset.card_product g h
      _ ≤ m*n := Nat.mul_le_mul hg hh
  · ext x
    change ((∃ a ∈ g, a ⊆ x) ∧ (∃ b ∈ h, b ⊆ x)) ↔
      ∃ c ∈ (g ×ˢ h).image (fun p => p.1 ∪ p.2), c ⊆ x
    constructor
    · rintro ⟨⟨a, ha, hax⟩, ⟨b, hb, hbx⟩⟩
      exact ⟨a ∪ b, Finset.mem_image.mpr
        ⟨(a,b), Finset.mem_product.mpr ⟨ha,hb⟩, rfl⟩,
        Finset.union_subset hax hbx⟩
    · rintro ⟨c, hc, hcx⟩
      rcases Finset.mem_image.mp hc with ⟨⟨a,b⟩, hab, rfl⟩
      obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
      exact ⟨⟨a,ha, fun i hi => hcx (Finset.mem_union_left _ hi)⟩,
        ⟨b,hb, fun i hi => hcx (Finset.mem_union_right _ hi)⟩⟩

def Minimal (z : Set Assignment) (x : Assignment) : Prop :=
  x ∈ z ∧ ∀ y, y ⊆ x → y ∈ z → x ⊆ y

def witnesses : Finset Assignment :=
  {{2,4}, {0,3,4}, {1,3,4}, {0,2,5}, {1,2,5}, {0,3,5}, {1,3,5}}

theorem witnesses_card : witnesses.card = 7 := by decide +kernel

theorem witnesses_minimal : ∀ x ∈ witnesses, Minimal diamond x := by
  unfold Minimal diamond
  decide +kernel

/-- Every conjunction cover needs a different generator for each minimal support. -/
theorem diamond_cover_bound {n : ℕ} (hz : CoverCount n diamond) : 7 ≤ n := by
  rcases hz with ⟨g, hg, heq⟩
  have sub : witnesses ⊆ g := by
    intro x hx
    obtain ⟨hxd, hxmin⟩ := witnesses_minimal x hx
    rw [heq] at hxd
    obtain ⟨a, ha, hax⟩ := hxd
    have had : a ∈ diamond := by
      rw [heq]
      exact ⟨a, ha, Finset.Subset.refl _⟩
    have hxa : x ⊆ a := hxmin a hax had
    have h : x = a := Finset.Subset.antisymm hxa hax
    exact h ▸ ha
  have hcard := (Finset.card_le_card sub).trans hg
  simpa [witnesses_card] using hcard

def majority (x y z : Assignment) : Assignment :=
  ((x ∩ y) ∪ (x ∩ z)) ∪ (y ∩ z)

def MajorityClosed (s : Set Assignment) : Prop :=
  ∀ x y z, x ∈ s → y ∈ s → z ∈ s → majority x y z ∈ s

private theorem conjunction_majority12 {s : Set Assignment} (hs : Conjunction s)
    {x y z : Assignment} (hx : x ∈ s) (hy : y ∈ s) : majority x y z ∈ s := by
  rcases hs with rfl | ⟨a, rfl⟩
  · exact False.elim hx
  · intro i hi
    have hix := hx hi
    have hiy := hy hi
    simp [majority, hix, hiy]

private theorem conjunction_majority13 {s : Set Assignment} (hs : Conjunction s)
    {x y z : Assignment} (hx : x ∈ s) (hz : z ∈ s) : majority x y z ∈ s := by
  rcases hs with rfl | ⟨a, rfl⟩
  · exact False.elim hx
  · intro i hi
    have hix := hx hi
    have hiz := hz hi
    simp [majority, hix, hiz]

private theorem conjunction_majority23 {s : Set Assignment} (hs : Conjunction s)
    {x y z : Assignment} (hy : y ∈ s) (hz : z ∈ s) : majority x y z ∈ s := by
  rcases hs with rfl | ⟨a, rfl⟩
  · exact False.elim hy
  · intro i hi
    have hiy := hy hi
    have hiz := hz hi
    simp [majority, hiy, hiz]

/-- A disjunction of two positive conjunctions is closed under majority. -/
theorem union_two_majority {s t : Set Assignment}
    (hs : Conjunction s) (ht : Conjunction t) : MajorityClosed (s ∪ t) := by
  intro x y z hx hy hz
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz
  all_goals first
    | exact Or.inl (conjunction_majority12 hs hx hy)
    | exact Or.inl (conjunction_majority13 hs hx hz)
    | exact Or.inl (conjunction_majority23 hs hy hz)
    | exact Or.inr (conjunction_majority12 ht hx hy)
    | exact Or.inr (conjunction_majority13 ht hx hz)
    | exact Or.inr (conjunction_majority23 ht hy hz)

theorem inter_majority {s t : Set Assignment}
    (hs : MajorityClosed s) (ht : MajorityClosed t) : MajorityClosed (s ∩ t) := by
  intro x y z hx hy hz
  exact ⟨hs x y z hx.1 hy.1 hz.1, ht x y z hx.2 hy.2 hz.2⟩

/-- ADE, BDE, CE are accepted but their majority DE is rejected. -/
theorem diamond_not_majority : ¬ MajorityClosed diamond := by
  intro h
  have hx : ({0,3,4} : Assignment) ∈ diamond := by simp [diamond]
  have hy : ({1,3,4} : Assignment) ∈ diamond := by simp [diamond]
  have hz : ({2,4} : Assignment) ∈ diamond := by simp [diamond]
  have hf : majority ({0,3,4} : Assignment) {1,3,4} {2,4} ∉ diamond := by
    simp [diamond, majority]
  exact hf (h _ _ _ hx hy hz)

theorem diamond_not_first_four : ¬ FirstFour Conjunction diamond := by
  rintro (⟨a,b,c,d,ha,hb,hc,hd,heq⟩ |
    ⟨a,b,c,d,e,ha,hb,hc,hd,he,heq⟩ |
    ⟨a,b,c,d,e,f,ha,hb,hc,hd,he,hf,heq⟩ |
    ⟨a,b,c,d,e,ha,hb,hc,hd,he,heq⟩)
  · have hcover : CoverCount 4 diamond := by
      rw [heq]
      exact cover_union (cover_union (conjunction_cover ha) (conjunction_cover hb))
        (cover_union (conjunction_cover hc) (conjunction_cover hd))
    have := diamond_cover_bound hcover
    omega
  · have hcover : CoverCount 6 diamond := by
      rw [heq]
      exact cover_inter
        (cover_union (cover_union (conjunction_cover ha) (conjunction_cover hb))
          (conjunction_cover hc))
        (cover_union (conjunction_cover hd) (conjunction_cover he))
    have := diamond_cover_bound hcover
    omega
  · apply diamond_not_majority
    rw [heq]
    exact inter_majority (inter_majority (union_two_majority ha hb)
      (union_two_majority hc hd)) (union_two_majority he hf)
  · have hcover : CoverCount 5 diamond := by
      rw [heq]
      exact cover_union (conjunction_cover ha)
        (cover_inter (cover_union (conjunction_cover hb) (conjunction_cover hc))
          (cover_union (conjunction_cover hd) (conjunction_cover he)))
    have := diamond_cover_bound hcover
    omega

theorem diamond_three : ThreeIntersections.Three Conjunction diamond := by
  apply (ThreeIntersections.normal_iff conjunction_closed conjunction_univ diamond).mpr
  refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
  refine ⟨principal {0}, principal {1}, principal {2}, principal {3},
    principal {4}, principal {5}, Or.inr ⟨{0},rfl⟩, Or.inr ⟨{1},rfl⟩,
    Or.inr ⟨{2},rfl⟩, Or.inr ⟨{3},rfl⟩, Or.inr ⟨{4},rfl⟩,
    Or.inr ⟨{5},rfl⟩, ?_⟩
  ext x
  simp [diamond, principal]

/-- Omitting the shared shape makes the generic classification false. -/
theorem shared_shape_necessary :
    Closed Conjunction ∧ Conjunction univ ∧
    ThreeIntersections.Three Conjunction diamond ∧ ¬ FirstFour Conjunction diamond :=
  ⟨conjunction_closed, conjunction_univ, diamond_three, diamond_not_first_four⟩

#print axioms diamond_cover_bound
#print axioms diamond_not_majority
#print axioms shared_shape_necessary

end ThreeIntersectionsSharingGap
