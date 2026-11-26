import Mathlib.Tactic

/-! Rejection tests for a prefix separated into matched vertices and an
independent set. Only the demands on the independent vertices are split. -/
theorem PEqualNP.PaidDepth.MatchedPrefix :
    ∀ (s n : Nat) (I : Type) (raw : (Fin s ⊕ Fin n) → Bool → I → Prop)
      (dep : (Fin s ⊕ Fin n) → Bool → (Fin s ⊕ Fin n) → Prop)
      (level : (Fin s ⊕ Fin n) → Nat) (wire : (Fin s ⊕ Fin n) → I → Prop),
    (∀ i e j, dep i e j → level j < level i) →
    (∀ i e j, ¬dep (.inr i) e (.inr j)) →
    (∀ i x, wire i x ↔ ∀ e, raw i e x ∨ ∃ j, dep i e j ∧ wire j x) →
    ∀ (need : Fin s → Prop) (keep extra : Fin n → Prop) (x : I),
      ((∀ i, need i → ¬wire (.inl i) x) ∧
       (∀ j, keep j ∨ extra j → ¬wire (.inr j) x)) ↔
      ∃ right : Fin n → Bool,
        (∀ j, extra j → ¬raw (.inr j) (right j) x) ∧
        ∃ σ : Fin s → Option Bool,
          (∀ i, need i → (σ i).isSome = true) ∧
          (∀ j, extra j → ∀ i, dep (.inr j) (right j) (.inl i) → (σ i).isSome = true) ∧
          (∀ i e, σ i = some e → ¬raw (.inl i) e x ∧
             ∀ j, dep (.inl i) e (.inl j) → (σ j).isSome = true) ∧
          ∃ left : Fin n → Bool, ∀ j,
            (keep j ∨ ∃ i e, σ i = some e ∧ dep (.inl i) e (.inr j)) →
            ¬raw (.inr j) (left j) x ∧
             ∀ i, dep (.inr j) (left j) (.inl i) → (σ i).isSome = true := by
  classical
  intro s n I raw dep level wire lower independent sem need keep extra x
  constructor
  · rintro ⟨hn,hi⟩
    have pick (i) : ∃ e : Bool, ¬wire i x → ¬ raw i e x ∧ ∀ j, dep i e j → ¬wire j x := by
      by_cases w : wire i x
      · exact ⟨false,fun off => False.elim (off w)⟩
      · have bad := mt (sem i x).mpr w
        push Not at bad
        obtain ⟨e,he⟩ := bad
        exact ⟨e,fun _ => he⟩
    choose arm h using pick
    let σ (i : Fin s) : Option Bool := if wire (.inl i) x then none else some (arm (.inl i))
    have active i : (σ i).isSome = true ↔ ¬wire (.inl i) x := by
      by_cases w : wire (.inl i) x <;> simp [σ,w]
    have selected i e (he : σ i = some e) : ¬wire (.inl i) x ∧ arm (.inl i) = e := by
      by_cases w : wire (.inl i) x
      · simp [σ,w] at he
      · exact ⟨w,by simpa [σ,w] using he⟩
    refine ⟨fun j => arm (.inr j),fun j hj => (h _ (hi j (.inr hj))).1, σ,
      fun i hn' => (active i).mpr (hn i hn'), ?_, ?_, fun j => arm (.inr j), ?_⟩
    · intro j oj i edge
      exact (active i).mpr ((h _ (hi j (.inr oj))).2 _ edge)
    · intro i e he
      obtain ⟨off,rfl⟩ := selected i e he
      exact ⟨(h _ off).1,fun j edge => (active j).mpr ((h _ off).2 _ edge)⟩
    · intro j hj
      have off : ¬wire (.inr j) x := by
        rcases hj with kept | ⟨i,e,he,edge⟩
        · exact hi j (.inl kept)
        · obtain ⟨off,rfl⟩ := selected i e he
          exact (h _ off).2 _ edge
      exact ⟨(h _ off).1,fun i edge => (active i).mpr ((h _ off).2 _ edge)⟩
  · rintro ⟨right,hr,σ,hn,hd,hs,left,hl⟩
    let bank (j : Fin n) := keep j ∨ ∃ i e, σ i = some e ∧ dep (.inl i) e (.inr j)
    let live : (Fin s ⊕ Fin n) → Prop := Sum.elim (fun i => (σ i).isSome = true)
      (fun j => bank j ∨ extra j)
    have cert (i : Fin s ⊕ Fin n) (hi : live i) :
        ∃ e, ¬raw i e x ∧ ∀ j, dep i e j → live j := by
      rcases i with a | b
      · change (σ a).isSome = true at hi
        cases he : σ a with
        | none => simp [he] at hi
        | some e =>
          refine ⟨e,(hs a e he).1,?_⟩
          rintro (j|j) edge
          · exact (hs a e he).2 j edge
          · exact Or.inl (Or.inr ⟨a,e,he,edge⟩)
      · change bank b ∨ extra b at hi
        rcases hi with lhs | rhs
        · refine ⟨left b,(hl b lhs).1,?_⟩
          rintro (j|j) edge
          · exact (hl b lhs).2 _ edge
          · exact False.elim (independent _ _ _ edge)
        · refine ⟨right b,hr b rhs,?_⟩
          rintro (j|j) edge
          · exact hd b rhs _ edge
          · exact False.elim (independent _ _ _ edge)
    have off : ∀ z i, level i = z → live i → ¬wire i x := by
      intro z
      induction z using Nat.strong_induction_on with
      | ind z ih =>
        intro i hz hi wi
        obtain ⟨e,miss,closed⟩ := cert i hi
        rcases (sem i x).mp wi e with hit | ⟨j,edge,wj⟩
        · exact miss hit
        · exact ih _ (hz ▸ lower i e j edge) _ rfl (closed _ edge) wj
    refine ⟨fun i si => off _ _ rfl (hn i si),?_⟩
    rintro j (kept|omitted)
    · exact off _ _ rfl (Or.inl (Or.inl kept) : live (.inr j))
    · exact off _ _ rfl (Or.inr omitted : live (.inr j))
