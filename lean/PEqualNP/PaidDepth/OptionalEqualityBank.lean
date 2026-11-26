import Mathlib.Tactic

namespace PEqualNP.PaidDepth

theorem OptionalEqualityBank :
∀ g n : Nat,
  let X := Fin g → Fin (n+2)
  let bank := fun b : Nat => ∃ (row col : Fin b → X → Prop)
    (use : (Fin g → Bool) → Fin b → Prop), ∀ mask x y,
    (∀ i, mask i = true → x i = y i) ↔
      ∃ j, use mask j ∧ row j x ∧ col j y
  IsLeast {b : Nat | bank b} ((n+3)^g)
 := by
  classical
  intro g n X bank
  let W := Fin g → Option (Fin (n+2))
  have count : Fintype.card W = (n+3)^g := by simp [W]
  let num := Fintype.equivFinOfCardEq count
  let maskOf (w : W) (i : Fin g) := (w i).isSome
  let fits (w : W) (x : X) := ∀ i a, w i = some a → x i = a
  constructor
  · refine ⟨fun j => fits (num.symm j), fun j => fits (num.symm j),
      fun mask j => maskOf (num.symm j) = mask, ?_⟩
    intro mask x y
    constructor
    · intro eqOn
      let w : W := fun i => if mask i then some (x i) else none
      refine ⟨num w, ?_⟩
      simp only [Equiv.symm_apply_apply]
      constructor
      · funext i
        cases hm : mask i <;> simp [maskOf,w,hm]
      constructor
      · intro i a h
        cases hm : mask i <;> simp_all [w]
      · intro i a h
        cases hm : mask i
        · simp [w,hm] at h
        · simpa [w,hm] using (eqOn i hm).symm.trans (by simpa [w,hm] using h)
    · rintro ⟨j,selected,rx,cy⟩ i hi
      have present : ((num.symm j) i).isSome = true := by
        change maskOf (num.symm j) i = true
        rw [selected,hi]
      cases hv : (num.symm j) i with
      | none => simp [hv] at present
      | some a => exact (rx i a hv).trans (cy i a hv).symm
  · intro b hb
    obtain ⟨row,col,use,spec⟩ := hb
    let left (w : W) (i : Fin g) : Fin (n+2) := (w i).getD 0
    let right (w : W) (i : Fin g) : Fin (n+2) := (w i).getD 1
    have witnesses (w : W) : ∃ j, use (maskOf w) j ∧ row j (left w) ∧ col j (right w) := by
      apply (spec _ _ _).mp
      intro i hi
      cases h : w i <;> simp_all [maskOf,left,right]
    choose pick sel rows cols using witnesses
    have injective : Function.Injective pick := by
      intro u v same
      have eqFrom (w a b' : W) (ha : pick a = pick w) (hb' : pick b' = pick w) :
          ∀ i, maskOf w i = true → left a i = right b' i := by
        apply (spec _ _ _).mpr
        exact ⟨pick w,sel w,ha ▸ rows a,hb' ▸ cols b'⟩
      funext i
      have uv := eqFrom u u v rfl same.symm i
      have vv := eqFrom u v v same.symm same.symm i
      have uu := eqFrom v u u same same i
      cases h : u i <;> cases h' : v i <;> simp_all [maskOf,left,right,Fin.ext_iff]
    simpa [count] using Fintype.card_le_of_injective pick injective

end PEqualNP.PaidDepth
