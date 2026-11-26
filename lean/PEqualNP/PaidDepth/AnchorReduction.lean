import Mathlib.Tactic

/-! Guess some true gates and propagate through every gate with a hit arm.
The reduced closure uses only the opposite arm. The remaining local tests
are sufficient, and are complete whenever the anchors cover all true gates. -/
theorem PEqualNP.PaidDepth.AnchorReduction :
    ∀ (G : Type) (arm : (G → Prop) → G → Bool → Prop)
      (need anchor on T : G → Prop) (hit : G → Bool → Prop),
    (∀ X Y : G → Prop, (∀ g, X g → Y g) → ∀ g e, arm X g e → arm Y g e) →
    (∀ g, (∀ e, arm on g e) → on g) →
    (∀ X : G → Prop, (∀ g, (∀ e, arm X g e) → X g) → ∀ g, on g → X g) →
    (∀ g, anchor g → T g) →
    (∀ g e, hit g e → arm T g (!e) → T g) →
    (∀ X : G → Prop, (∀ g, anchor g → X g) →
      (∀ g e, hit g e → arm X g (!e) → X g) → ∀ g, T g → X g) →
    (let test := (∀ g, need g → ¬T g) ∧
       (∀ g, ¬anchor g → (∀ e, ¬hit g e) → ¬(∀ e, arm T g e))
     (test → ∀ g, need g → ¬on g) ∧
     ((∀ g, anchor g → on g) → (∀ g e, hit g e → arm on g e) →
       (∀ g, on g → anchor g ∨ ∃ e, hit g e) →
       (∀ g, need g → ¬on g) → test)) := by
  classical
  intro G arm need anchor on T hit mono onClosed onLeast anchored propagate reducedLeast
  dsimp only
  constructor
  · rintro ⟨missing, localTests⟩
    have pre (g : G) (both : ∀ e, arm T g e) : T g := by
      by_cases a : anchor g
      · exact anchored g a
      by_cases h : ∃ e, hit g e
      · obtain ⟨e, he⟩ := h
        exact propagate g e he (both (!e))
      exact False.elim (localTests g a (fun e he => h ⟨e, he⟩) both)
    exact fun g output active => missing g output (onLeast T pre g active)
  · intro correct reaches covered rejects
    have step (g : G) (e : Bool) (h : hit g e) (other : arm on g (!e)) : on g := by
      apply onClosed g
      intro b
      cases e <;> cases b <;> first | exact reaches g _ h | exact other
    have sub := reducedLeast on correct step
    refine ⟨fun g output v => rejects g output (sub g v), ?_⟩
    intro g absent untouched both
    have v := onClosed g (fun e => mono T on sub g e (both e))
    rcases covered g v with a | ⟨e, h⟩
    · exact absent a
    · exact untouched e h
