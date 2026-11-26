import ThreeIntersectionsSharingGap

/-!
Formulas, rather than circuits, with at most three paid unions.

Each subtree contributes its cost separately: there is no discounted reuse.
Free intersections may occur arbitrarily often.  After absorbing intersections
of base leaves into the meet-closed family, exactly the first four shapes of
the three-gate circuit classification remain.
-/
namespace ThreeIntersectionsFormula
open Set TwoIntersections ThreeIntersectionsSharingGap

variable {α : Type*}

/-- Formula cost counts occurrences of paid unions, including repeated subtrees. -/
inductive Formula (F : Family α) : ℕ → Set α → Prop where
  | base {z} : F z → Formula F 0 z
  | meet {m n s t} : Formula F m s → Formula F n t → Formula F (m+n) (s ∩ t)
  | join {m n s t} : Formula F m s → Formula F n t → Formula F (m+n+1) (s ∪ t)

private def One (F : Family α) (z : Set α) : Prop :=
  ∃ a b, F a ∧ F b ∧ z = a ∪ b

private def Small (F : Family α) : ℕ → Set α → Prop
  | 0, z => F z
  | 1, z => One F z
  | 2, z => TwoIntersections.Normal F z
  | _, z => FirstFour F z

private theorem one_cut {F : Family α} (hc : Closed F) {s t}
    (hs : F s) (ht : One F t) : One F (s ∩ t) := by
  rcases ht with ⟨a,b,ha,hb,rfl⟩
  exact ⟨s ∩ a, s ∩ b, hc hs ha, hc hs hb, by ext; simp; tauto⟩

private theorem two_cut {F : Family α} (hc : Closed F) {s t}
    (hs : F s) (ht : TwoIntersections.Normal F t) :
    TwoIntersections.Normal F (s ∩ t) := by
  rcases ht with ⟨a,b,c,ha,hb,hc',rfl⟩ | ⟨a,b,c,d,ha,hb,hc',hd,rfl⟩
  · exact Or.inl ⟨s ∩ a, s ∩ b, s ∩ c, hc hs ha, hc hs hb, hc hs hc',
      by ext; simp; tauto⟩
  · exact Or.inr ⟨s ∩ a, s ∩ b, c, d, hc hs ha, hc hs hb, hc', hd,
      by ext; simp; tauto⟩

theorem first_four_cut {F : Family α} (hc : Closed F) {s t}
    (hs : F s) (ht : FirstFour F t) : FirstFour F (s ∩ t) := by
  rcases ht with ⟨a,b,c,d,ha,hb,hc',hd,rfl⟩ |
    ⟨a,b,c,d,e,ha,hb,hc',hd,he,rfl⟩ |
    ⟨a,b,c,d,e,f,ha,hb,hc',hd,he,hf,rfl⟩ |
    ⟨a,b,c,d,e,ha,hb,hc',hd,he,rfl⟩
  · exact Or.inl ⟨s ∩ a, s ∩ b, s ∩ c, s ∩ d,
      hc hs ha, hc hs hb, hc hs hc', hc hs hd, by ext; simp; tauto⟩
  · exact Or.inr (Or.inl ⟨s ∩ a, s ∩ b, s ∩ c, d, e,
      hc hs ha, hc hs hb, hc hs hc', hd, he, by ext; simp; tauto⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨s ∩ a, s ∩ b, c, d, e, f,
      hc hs ha, hc hs hb, hc', hd, he, hf, by ext; simp; tauto⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨s ∩ a, s ∩ b, s ∩ c, d, e,
      hc hs ha, hc hs hb, hc hs hc', hd, he, by ext; simp; tauto⟩))

private theorem one_meet_two {F : Family α} {s t}
    (hs : One F s) (ht : TwoIntersections.Normal F t) : FirstFour F (s ∩ t) := by
  rcases hs with ⟨a,b,ha,hb,rfl⟩
  rcases ht with ⟨c,d,e,hc,hd,he,rfl⟩ | ⟨c,d,e,f,hc,hd,he,hf,rfl⟩
  · exact Or.inr (Or.inl ⟨c,d,e,a,b,hc,hd,he,ha,hb,by ext; simp; tauto⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨a,b,c,d,e,f,ha,hb,hc,hd,he,hf,
      by ext; simp; tauto⟩))

private theorem base_join_two {F : Family α} {s t}
    (hs : F s) (ht : TwoIntersections.Normal F t) : FirstFour F (s ∪ t) := by
  rcases ht with ⟨a,b,c,ha,hb,hc,rfl⟩ | ⟨a,b,c,d,ha,hb,hc,hd,rfl⟩
  · exact Or.inl ⟨s,a,b,c,hs,ha,hb,hc,by ext; simp; tauto⟩
  · exact Or.inr (Or.inr (Or.inr ⟨s,a,b,c,d,hs,ha,hb,hc,hd,rfl⟩))

private theorem formula_small {F : Family α} (hc : Closed F) {n z}
    (h : Formula F n z) (hn : n ≤ 3) : Small F n z := by
  induction h with
  | base hz => exact hz
  | @meet m n s t hs ht ihs iht =>
    have hm : m ≤ 3 := by omega
    have hn' : n ≤ 3 := by omega
    have hS := ihs hm
    have hT := iht hn'
    interval_cases m <;> interval_cases n
    all_goals try omega
    all_goals simp only [Small] at hS hT ⊢
    · exact hc hS hT
    · exact one_cut hc hS hT
    · exact two_cut hc hS hT
    · exact first_four_cut hc hS hT
    · rw [inter_comm]
      exact one_cut hc hT hS
    · rcases hS with ⟨a,b,ha,hb,rfl⟩
      rcases hT with ⟨c,d,hc',hd,rfl⟩
      exact Or.inr ⟨a,b,c,d,ha,hb,hc',hd,rfl⟩
    · exact one_meet_two hS hT
    · rw [inter_comm]
      exact two_cut hc hT hS
    · rw [inter_comm]
      exact one_meet_two hT hS
    · rw [inter_comm]
      exact first_four_cut hc hT hS
  | @join m n s t hs ht ihs iht =>
    have hm : m ≤ 2 := by omega
    have hn' : n ≤ 2 := by omega
    have hS := ihs (by omega)
    have hT := iht (by omega)
    interval_cases m <;> interval_cases n
    all_goals try omega
    all_goals simp only [Small] at hS hT ⊢
    · exact ⟨s,t,hS,hT,rfl⟩
    · rcases hT with ⟨a,b,ha,hb,rfl⟩
      exact Or.inl ⟨s,a,b,hS,ha,hb,by ext; simp; tauto⟩
    · exact base_join_two hS hT
    · rcases hS with ⟨a,b,ha,hb,rfl⟩
      exact Or.inl ⟨a,b,t,ha,hb,hT,rfl⟩
    · rcases hS with ⟨a,b,ha,hb,rfl⟩
      rcases hT with ⟨c,d,hc',hd,rfl⟩
      exact Or.inl ⟨a,b,c,d,ha,hb,hc',hd,rfl⟩
    · rw [union_comm]
      exact base_join_two hT hS

private theorem base_first_four {F : Family α} {z} (hz : F z) : FirstFour F z := by
  exact Or.inl ⟨z,z,z,z,hz,hz,hz,hz,by ext; simp⟩

private theorem one_first_four {F : Family α} {z} (hz : One F z) : FirstFour F z := by
  rcases hz with ⟨a,b,ha,hb,rfl⟩
  exact Or.inl ⟨a,b,a,b,ha,hb,ha,hb,by ext; simp⟩

private theorem two_first_four {F : Family α} {z}
    (hz : TwoIntersections.Normal F z) : FirstFour F z := by
  rcases hz with ⟨a,b,c,ha,hb,hc,rfl⟩ | ⟨a,b,c,d,ha,hb,hc,hd,rfl⟩
  · exact Or.inl ⟨a,b,c,c,ha,hb,hc,hc,by ext; simp⟩
  · exact Or.inr (Or.inl ⟨a,b,b,c,d,ha,hb,hb,hc,hd,by ext; simp⟩)

/-- Every formula with at most three paid unions has one of the four tree shapes. -/
theorem formula_first_four {F : Family α} (hc : Closed F) {n z}
    (h : Formula F n z) (hn : n ≤ 3) : FirstFour F z := by
  have hx := formula_small hc h hn
  interval_cases n
  · exact base_first_four hx
  · exact one_first_four hx
  · exact two_first_four hx
  · exact hx

/-- Each of the four shapes has an actual formula with three paid unions. -/
theorem first_four_formula {F : Family α} {z} (hz : FirstFour F z) : Formula F 3 z := by
  rcases hz with ⟨a,b,c,d,ha,hb,hc,hd,rfl⟩ |
    ⟨a,b,c,d,e,ha,hb,hc,hd,he,rfl⟩ |
    ⟨a,b,c,d,e,f,ha,hb,hc,hd,he,hf,rfl⟩ |
    ⟨a,b,c,d,e,ha,hb,hc,hd,he,rfl⟩
  · exact .join (.join (.base ha) (.base hb)) (.join (.base hc) (.base hd))
  · exact .meet (.join (.join (.base ha) (.base hb)) (.base hc))
      (.join (.base hd) (.base he))
  · exact .meet (.meet (.join (.base ha) (.base hb)) (.join (.base hc) (.base hd)))
      (.join (.base he) (.base hf))
  · exact .join (.base ha) (.meet (.join (.base hb) (.base hc))
      (.join (.base hd) (.base he)))

/-- A finite structural criterion for formulas, without any universe assumption. -/
theorem formula_three_iff {F : Family α} (hc : Closed F) (z : Set α) :
    Formula F 3 z ↔ FirstFour F z :=
  ⟨fun h => formula_first_four hc h (by decide), first_four_formula⟩

/-- Expanding the shared diamond requires only four union occurrences in a formula. -/
theorem diamond_four_formula {F : Family α} {a b c d e f : Set α}
    (ha : F a) (hb : F b) (hc : F c) (hd : F d) (he : F e) (hf : F f) :
    Formula F 4 ((c ∪ (d ∩ (a ∪ b))) ∩ (e ∪ (f ∩ (a ∪ b)))) := by
  have h : Formula F 4
      ((c ∩ e) ∪ ((a ∪ b) ∩ (((c ∩ f) ∪ (d ∩ e)) ∪ (d ∩ f)))) :=
    .join (.meet (.base hc) (.base he))
      (.meet (.join (.base ha) (.base hb))
        (.join (.join (.meet (.base hc) (.base hf)) (.meet (.base hd) (.base he)))
          (.meet (.base hd) (.base hf))))
  convert h using 1
  ext x
  simp only [mem_inter_iff, mem_union]
  tauto

/-- The generic sharing witness cannot have a formula with at most three paid unions. -/
theorem generic_diamond_no_small_formula {n : ℕ} (hn : n ≤ 3) :
    ¬ Formula Conjunction n diamond := by
  intro h
  exact diamond_not_first_four (formula_first_four conjunction_closed h hn)

#print axioms formula_first_four
#print axioms formula_three_iff
#print axioms diamond_four_formula
#print axioms generic_diamond_no_small_formula

end ThreeIntersectionsFormula
