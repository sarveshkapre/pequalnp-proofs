import Mathlib.Tactic

/-! A private predecessor needs an arm choice only when its reader selects the
arm on which it occurs. Encode the two choices by one three-valued digit. -/
theorem PEqualNP.PaidDepth.LeafTraces :
∀ (r h : Nat) (R C : Type)
    (baseR : (Fin r → Bool) → (Fin h → Bool) → R → Prop)
    (baseC : (Fin r → Bool) → (Fin h → Bool) → C → Prop)
    (needed : (Fin r → Bool) → (Fin h → Bool) → Fin h → Prop)
    (leafR : Fin h → Bool → R → Prop) (leafC : Fin h → Bool → C → Prop),
  ∃ (rows : Fin (2^r * 3^h) → R → Prop) (cols : Fin (2^r * 3^h) → C → Prop),
    ∀ x y, (∃ (z : Fin r → Bool) (p l : Fin h → Bool), baseR z p x ∧ baseC z p y ∧
      ∀ i, needed z p i → p i = true → leafR i (l i) x ∧ leafC i (l i) y) ↔
      ∃ j, rows j x ∧ cols j y := by
  classical
  intro r h R C baseR baseC needed leafR leafC
  let Code := (Fin r → Bool) × (Fin h → Option Bool)
  have count : Fintype.card Code = 2^r * 3^h := by simp [Code]
  let number := Fintype.equivFinOfCardEq count
  let parent (c : Code) (i : Fin h) := (c.2 i).isSome
  let leaf (c : Code) (i : Fin h) := (c.2 i).getD false
  let row (c : Code) (x : R) := baseR c.1 (parent c) x ∧
    ∀ i, needed c.1 (parent c) i → parent c i = true → leafR i (leaf c i) x
  let col (c : Code) (y : C) := baseC c.1 (parent c) y ∧
    ∀ i, needed c.1 (parent c) i → parent c i = true → leafC i (leaf c i) y
  refine ⟨fun j => row (number.symm j), fun j => col (number.symm j), ?_⟩
  intro x y
  constructor
  · rintro ⟨z, p, l, bx, by', active⟩
    let c : Code := (z, fun i => if p i then some (l i) else none)
    have hp : parent c = p := by
      funext i
      cases e : p i <;> simp [parent, c, e]
    have hl (i : Fin h) (e : p i = true) : leaf c i = l i := by simp [leaf, c, e]
    refine ⟨number c, ?_⟩
    simp only [Equiv.symm_apply_apply]
    dsimp only [row, col]
    change (baseR z (parent c) x ∧ (∀ i, needed z (parent c) i → parent c i = true → leafR i (leaf c i) x)) ∧
      (baseC z (parent c) y ∧ (∀ i, needed z (parent c) i → parent c i = true → leafC i (leaf c i) y))
    simp only [hp]
    exact ⟨⟨bx, fun i hi he => by simpa only [hl i he] using (active i hi he).1⟩,
      ⟨by', fun i hi he => by simpa only [hl i he] using (active i hi he).2⟩⟩
  · rintro ⟨j, hr, hc⟩
    let c := number.symm j
    exact ⟨c.1, parent c, leaf c, hr.1, hc.1,
      fun i hi he => ⟨hr.2 i hi he, hc.2 i hi he⟩⟩
