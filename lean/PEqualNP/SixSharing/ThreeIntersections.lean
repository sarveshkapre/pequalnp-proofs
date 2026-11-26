import PEqualNP.SixSharing.TwoIntersections

/-!
Three paid intersections, in the zero-set model.

This builds on pjscruggs's `TwoIntersections.normal_iff`, copied unchanged from
commit 7da7d81614b93ea808c11ac27f27136942fec385 in the adjacent vendor directory.
Free gates intersect zero sets; paid gates take their union. Earlier gates may
be reused without limit. No finiteness or rectangle hypothesis is needed until
the final specialization.
-/
namespace ThreeIntersections
open Set TwoIntersections

variable {α : Type*}

/-- Three paid gates, with arbitrary free gates and fan-out between them. -/
def Three (F : Family α) (z : Set α) : Prop :=
  ∃ a b, Free F a ∧ Free F b ∧ Two (With F (a ∪ b)) z

/-- The five structural shapes. The final disjunct shares `a ∪ b`. -/
def Normal (F : Family α) (z : Set α) : Prop :=
  (∃ a b c d, F a ∧ F b ∧ F c ∧ F d ∧ z = (a ∪ b) ∪ (c ∪ d)) ∨
  (∃ a b c d e, F a ∧ F b ∧ F c ∧ F d ∧ F e ∧
    z = ((a ∪ b) ∪ c) ∩ (d ∪ e)) ∨
  (∃ a b c d e f, F a ∧ F b ∧ F c ∧ F d ∧ F e ∧ F f ∧
    z = ((a ∪ b) ∩ (c ∪ d)) ∩ (e ∪ f)) ∨
  (∃ a b c d e, F a ∧ F b ∧ F c ∧ F d ∧ F e ∧
    z = a ∪ ((b ∪ c) ∩ (d ∪ e))) ∨
  (∃ a b c d e f, F a ∧ F b ∧ F c ∧ F d ∧ F e ∧ F f ∧
    z = (c ∪ (d ∩ (a ∪ b))) ∩ (e ∪ (f ∩ (a ∪ b))))

private theorem free_base {F : Family α} (hc : Closed F) {z}
    (hz : Free F z) : F z := by
  induction hz with
  | input h => exact h
  | meet _ _ ih jh => exact hc ih jh

theorem free_lift {F G : Family α} (h : ∀ s, F s → Free G s) {z}
    (hz : Free F z) : Free G z := by
  induction hz with
  | input hs => exact h _ hs
  | meet _ _ ih jh => exact Free.meet ih jh

private theorem with_lift {F G : Family α} (h : ∀ s, F s → Free G s)
    (a : Set α) : ∀ s, With F a s → Free (With G a) s := by
  intro s hs
  rcases hs with hs | rfl
  · exact free_lift (fun _ hx => Free.input (Or.inl hx)) (h s hs)
  · exact Free.input (Or.inr rfl)

theorem two_lift {F G : Family α} (h : ∀ s, F s → Free G s) {z}
    (hz : Two F z) : Two G z := by
  rcases hz with ⟨a, b, ha, hb, c, d, hc, hd, hz⟩
  exact ⟨a, b, free_lift h ha, free_lift h hb, c, d,
    free_lift (with_lift h (a ∪ b)) hc,
    free_lift (with_lift h (a ∪ b)) hd,
    free_lift (with_lift (with_lift h (a ∪ b)) (c ∪ d)) hz⟩

theorem cut_closed {F : Family α} (hc : Closed F) (h : Set α) :
    Closed (Cut F h) := by
  intro s t hs ht
  rcases hs with hs | ⟨a, ha, rfl⟩ <;>
    rcases ht with ht | ⟨b, hb, rfl⟩
  · exact Or.inl (hc hs ht)
  · exact Or.inr ⟨_, hc hs hb, by ext x; simp [and_assoc]⟩
  · exact Or.inr ⟨_, hc ha ht, by ext x; simp [and_left_comm, and_comm]⟩
  · exact Or.inr ⟨_, hc ha hb, by ext x; simp [and_assoc, and_left_comm, and_comm]⟩

private theorem cut_self {F : Family α} (hu : F univ) (h : Set α) :
    Cut F h h := Or.inr ⟨univ, hu, (univ_inter h).symm⟩

private theorem two_with_iff_cut {F : Family α} (hu : F univ) (h z : Set α) :
    Two (With F h) z ↔ Two (Cut F h) z := by
  constructor
  · apply two_lift
    intro s hs
    rcases hs with hs | rfl
    · exact Free.input (Or.inl hs)
    · exact Free.input (cut_self hu _)
  · apply two_lift
    intro s hs
    rcases hs with hs | ⟨r, hr, rfl⟩
    · exact Free.input (Or.inl hs)
    · exact Free.meet (Free.input (Or.inl hr)) (Free.input (Or.inr rfl))

/-- One shared first gate, followed by the existing two-gate characterization. -/
theorem three_iff_seeded_normal {F : Family α} (hc : Closed F) (hu : F univ)
    (z : Set α) :
    Three F z ↔ ∃ a b, F a ∧ F b ∧ TwoIntersections.Normal (Cut F (a ∪ b)) z := by
  constructor
  · rintro ⟨a, b, ha, hb, hz⟩
    refine ⟨a, b, free_base hc ha, free_base hc hb, ?_⟩
    apply (TwoIntersections.normal_iff (cut_closed hc (a ∪ b)) (Or.inl hu) z).mp
    exact (two_with_iff_cut hu (a ∪ b) z).mp hz
  · rintro ⟨a, b, ha, hb, hz⟩
    refine ⟨a, b, Free.input ha, Free.input hb, ?_⟩
    apply (two_with_iff_cut hu (a ∪ b) z).mpr
    exact (TwoIntersections.normal_iff (cut_closed hc (a ∪ b)) (Or.inl hu) z).mpr hz

private theorem classify_cut_normal {F : Family α} (hc : Closed F)
    {p q z : Set α} (hp : F p) (hq : F q)
    (hz : TwoIntersections.Normal (Cut F (p ∪ q)) z) : Normal F z := by
  rcases hz with ⟨a, b, c, ha, hb, hc', rfl⟩ | ⟨a, b, c, d, ha, hb, hc', hd, rfl⟩
  · rcases ha with ha | ⟨a, ha, rfl⟩ <;>
      rcases hb with hb | ⟨b, hb, rfl⟩ <;>
      rcases hc' with hc' | ⟨c, hc', rfl⟩
    · exact Or.inl ⟨a, b, c, c, ha, hb, hc', hc', by ext; simp⟩
    · exact Or.inl ⟨a, b, c ∩ p, c ∩ q, ha, hb, hc hc' hp, hc hc' hq,
        by ext; simp; tauto⟩
    · exact Or.inl ⟨a, b ∩ p, b ∩ q, c, ha, hc hb hp, hc hb hq, hc',
        by ext; simp; tauto⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, c, p, q, ha, hb, hc', hp, hq,
        by ext; simp; tauto⟩)))
    · exact Or.inl ⟨a ∩ p, a ∩ q, b, c, hc ha hp, hc ha hq, hb, hc',
        by ext; simp; tauto⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨b, a, c, p, q, hb, ha, hc', hp, hq,
        by ext; simp; tauto⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨c, a, b, p, q, hc', ha, hb, hp, hq,
        by ext; simp; tauto⟩)))
    · exact Or.inr (Or.inl ⟨a, b, c, p, q, ha, hb, hc', hp, hq,
        by ext; simp; tauto⟩)
  · rcases ha with ha | ⟨a, ha, rfl⟩ <;>
      rcases hb with hb | ⟨b, hb, rfl⟩ <;>
      rcases hc' with hc' | ⟨c, hc', rfl⟩ <;>
      rcases hd with hd | ⟨d, hd, rfl⟩
    · exact Or.inr (Or.inl ⟨a, b, b, c, d, ha, hb, hb, hc', hd,
        by ext; simp⟩)
    · exact Or.inr (Or.inl ⟨c, d ∩ p, d ∩ q, a, b, hc', hc hd hp, hc hd hq, ha, hb,
        by ext; simp; tauto⟩)
    · exact Or.inr (Or.inl ⟨c ∩ p, c ∩ q, d, a, b, hc hc' hp, hc hc' hq, hd, ha, hb,
        by ext; simp only [mem_inter_iff, mem_union]; tauto⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨a, b, c, d, p, q, ha, hb, hc', hd, hp, hq,
        by ext; simp; tauto⟩))
    · exact Or.inr (Or.inl ⟨a, b ∩ p, b ∩ q, c, d, ha, hc hb hp, hc hb hq, hc', hd,
        by ext; simp; tauto⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨p, q, a, b, c, d, hp, hq, ha, hb, hc', hd, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨p, q, a, b, d, c, hp, hq, ha, hb, hd, hc',
        by ext; simp; tauto⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨a, b, c, d, p, q, ha, hb, hc', hd, hp, hq,
        by ext; simp; tauto⟩))
    · exact Or.inr (Or.inl ⟨a ∩ p, a ∩ q, b, c, d, hc ha hp, hc ha hq, hb, hc', hd,
        by ext; simp; tauto⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨p, q, b, a, c, d, hp, hq, hb, ha, hc', hd,
        by ext; simp; tauto⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨p, q, b, a, d, c, hp, hq, hb, ha, hd, hc',
        by ext; simp; tauto⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨a, b, c, d, p, q, ha, hb, hc', hd, hp, hq,
        by ext; simp; tauto⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨a, b, c, d, p, q, ha, hb, hc', hd, hp, hq,
        by ext; simp; tauto⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨a, b, c, d, p, q, ha, hb, hc', hd, hp, hq,
        by ext; simp; tauto⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨a, b, c, d, p, q, ha, hb, hc', hd, hp, hq,
        by ext; simp; tauto⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨a, b, c, d, p, q, ha, hb, hc', hd, hp, hq,
        by ext; simp; tauto⟩))

/-- A complete classification, including unrestricted reuse of earlier gates. -/
theorem normal_iff {F : Family α} (hc : Closed F) (hu : F univ) (z : Set α) :
    Three F z ↔ Normal F z := by
  rw [three_iff_seeded_normal hc hu]
  constructor
  · rintro ⟨a, b, ha, hb, hz⟩
    exact classify_cut_normal hc ha hb hz
  · rintro (⟨a, b, c, d, ha, hb, hc', hd, rfl⟩ |
      ⟨a, b, c, d, e, ha, hb, hc', hd, he, rfl⟩ |
      ⟨a, b, c, d, e, f, ha, hb, hc', hd, he, hf, rfl⟩ |
      ⟨a, b, c, d, e, ha, hb, hc', hd, he, rfl⟩ |
      ⟨a, b, c, d, e, f, ha, hb, hc', hd, he, hf, rfl⟩)
    · refine ⟨a, b, ha, hb, Or.inl ⟨a ∪ b, c, d, cut_self hu _, Or.inl hc', Or.inl hd, ?_⟩⟩
      ext; simp; tauto
    · exact ⟨a, b, ha, hb, Or.inr ⟨a ∪ b, c, d, e, cut_self hu _, Or.inl hc',
        Or.inl hd, Or.inl he, rfl⟩⟩
    · refine ⟨a, b, ha, hb, Or.inr ⟨c ∩ (a ∪ b), d ∩ (a ∪ b), e, f,
        Or.inr ⟨c, hc', rfl⟩, Or.inr ⟨d, hd, rfl⟩, Or.inl he, Or.inl hf, ?_⟩⟩
      ext; simp; tauto
    · refine ⟨b, c, hb, hc', Or.inl ⟨a, d ∩ (b ∪ c), e ∩ (b ∪ c),
        Or.inl ha, Or.inr ⟨d, hd, rfl⟩, Or.inr ⟨e, he, rfl⟩, ?_⟩⟩
      ext; simp; tauto
    · exact ⟨a, b, ha, hb, Or.inr ⟨c, d ∩ (a ∪ b), e, f ∩ (a ∪ b),
        Or.inl hc', Or.inr ⟨d, hd, rfl⟩, Or.inl he, Or.inr ⟨f, hf, rfl⟩, rfl⟩⟩

/-- The size-independent three-intersection criterion for star circuits. -/
theorem rectangle_normal_iff {ι κ : Type*} (z : Set (ι × κ)) :
    Three Rectangle z ↔ Normal Rectangle z := by
  apply normal_iff
  · rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    exact ⟨a ∩ c, b ∩ d, by ext x; simp; tauto⟩
  · exact ⟨univ, univ, by simp⟩

/-- Pulling back the base sets pulls back every normal form. -/
theorem normal_preimage {β : Type*} {F : Family α} {G : Family β}
    (f : β → α) (hbase : ∀ s, F s → G (f ⁻¹' s)) {z : Set α}
    (hz : Normal F z) : Normal G (f ⁻¹' z) := by
  rcases hz with (⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ |
    ⟨a, b, c, d, e, ha, hb, hc, hd, he, rfl⟩ |
    ⟨a, b, c, d, e, f', ha, hb, hc, hd, he, hf, rfl⟩ |
    ⟨a, b, c, d, e, ha, hb, hc, hd, he, rfl⟩ |
    ⟨a, b, c, d, e, f', ha, hb, hc, hd, he, hf, rfl⟩)
  · exact Or.inl ⟨f ⁻¹' a, f ⁻¹' b, f ⁻¹' c, f ⁻¹' d,
      hbase _ ha, hbase _ hb, hbase _ hc, hbase _ hd, rfl⟩
  · exact Or.inr (Or.inl ⟨f ⁻¹' a, f ⁻¹' b, f ⁻¹' c, f ⁻¹' d, f ⁻¹' e,
      hbase _ ha, hbase _ hb, hbase _ hc, hbase _ hd, hbase _ he, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨f ⁻¹' a, f ⁻¹' b, f ⁻¹' c, f ⁻¹' d,
      f ⁻¹' e, f ⁻¹' f', hbase _ ha, hbase _ hb, hbase _ hc, hbase _ hd,
      hbase _ he, hbase _ hf, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f ⁻¹' a, f ⁻¹' b, f ⁻¹' c,
      f ⁻¹' d, f ⁻¹' e, hbase _ ha, hbase _ hb, hbase _ hc, hbase _ hd,
      hbase _ he, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨f ⁻¹' a, f ⁻¹' b, f ⁻¹' c,
      f ⁻¹' d, f ⁻¹' e, f ⁻¹' f', hbase _ ha, hbase _ hb, hbase _ hc,
      hbase _ hd, hbase _ he, hbase _ hf, rfl⟩)))

/-- In particular, deleting or duplicating rows/columns preserves every shape. -/
theorem rectangle_normal_preimage {ι κ ι' κ' : Type*}
    (f : ι' → ι) (g : κ' → κ) {z : Set (ι × κ)} (hz : Normal Rectangle z) :
    Normal Rectangle ((fun p : ι' × κ' => (f p.1, g p.2)) ⁻¹' z) := by
  apply normal_preimage _ _ hz
  rintro s ⟨rows, cols, rfl⟩
  exact ⟨f ⁻¹' rows, g ⁻¹' cols, rfl⟩

#print axioms normal_iff
#print axioms rectangle_normal_iff
end ThreeIntersections
