import Mathlib.Tactic

/-! A fixed set of possibly true gates factors a rejecting cell into a test in
each block. Once a legal arm is chosen, its row and column tests separate.
The prefixed-point hypotheses include ordinary acyclic and least-fixed-point
semantics. The gate and block types need not be finite for this equivalence. -/
theorem PEqualNP.PaidDepth.SupportBlocks :
    ∀ (G B R C : Type) (block : G → B) (edge : G → Bool → G → Prop)
      (row : G → Bool → R → Prop) (col : G → Bool → C → Prop)
      (need : G → Prop) (x : R) (y : C) (on : G → Prop),
    (∀ g, (∀ e, row g e x ∨ col g e y ∨ ∃ j, edge g e j ∧ on j) → on g) →
    (∀ T : G → Prop,
      (∀ g, (∀ e, row g e x ∨ col g e y ∨ ∃ j, edge g e j ∧ T j) → T g) →
      ∀ g, on g → T g) →
    ((∀ g, need g → ¬on g) ↔
      ∃ T : G → Prop, (∀ g, need g → ¬T g) ∧
        ∀ b, ∃ arm : G → Bool,
          (∀ g, block g = b → ¬T g → ∀ j, edge g (arm g) j → ¬T j) ∧
          (∀ g, block g = b → ¬T g → ¬row g (arm g) x) ∧
          (∀ g, block g = b → ¬T g → ¬col g (arm g) y)) := by
  classical
  intro G B R C block edge row col need x y on closed least
  constructor
  · intro rejects
    have pick (g : G) : ∃ e : Bool, ¬on g →
        ¬row g e x ∧ ¬col g e y ∧ ∀ j, edge g e j → ¬on j := by
      by_cases active : on g
      · exact ⟨false, fun h => False.elim (h active)⟩
      · have missing := mt (closed g) active
        push Not at missing
        obtain ⟨e, h⟩ := missing
        exact ⟨e, fun _ => h⟩
    choose arm spec using pick
    exact ⟨on, rejects, fun _ => ⟨arm, fun g _ hg => (spec g hg).2.2,
      fun g _ hg => (spec g hg).1, fun g _ hg => (spec g hg).2.1⟩⟩
  · rintro ⟨T, omitted, localTests⟩
    have pre : ∀ g, (∀ e, row g e x ∨ col g e y ∨ ∃ j, edge g e j ∧ T j) → T g := by
      intro g fires
      by_contra outside
      obtain ⟨arm, legal, rows, cols⟩ := localTests (block g)
      rcases fires (arm g) with r | c | ⟨j, dep, inside⟩
      · exact rows g rfl outside r
      · exact cols g rfl outside c
      · exact legal g rfl outside j dep inside
    exact fun g output h => omitted g output (least T pre g h)
