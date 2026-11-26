import Mathlib.Tactic

namespace PaidSeparator

abbrev Node (s m b : Nat) := Fin s ⊕ (Fin m × Fin b)

def Here (z : Fin m) : Node s m b → Prop :=
  Sum.elim (fun _ => True) (fun p => p.1 = z)

private def view (σ : Fin s → Option Bool) (T : Fin b → Prop) : Node s m b → Prop
  | .inl a => (σ a).isSome = true
  | .inr (_, i) => T i

private def pick (σ : Fin s → Option Bool) (β : Fin b → Bool) : Node s m b → Bool
  | .inl a => (σ a).getD false
  | .inr (_, i) => β i

private def splice (u : Fin s → α) (v : Fin m → Fin b → α) : Node s m b → α
  | .inl a => u a
  | .inr (z,i) => v z i

private def localOK (seed : Node s m b → Prop) (dep : Node s m b → Bool → Node s m b → Prop)
    (miss : Node s m b → Bool → Prop) (z : Fin m) (σ : Fin s → Option Bool) (β : Fin b → Bool) :=
  ∃ T : Fin b → Prop,
    (∀ i, Here z i → seed i → view σ T i) ∧
    (∀ i, Here z i → view σ T i → miss i (pick σ β i)) ∧
    (∀ i j, Here z i → Here z j → view σ T i → dep i (pick σ β i) j → view σ T j)

end PaidSeparator

open PaidSeparator in
theorem PEqualNP.PaidDepth.SeparatorComplement :
    ∀ (r c s m b : Nat) (_hm : 0 < m)
      (seed : Node s m b → Prop) (dep : Node s m b → Bool → Node s m b → Prop)
      (level : Node s m b → Nat)
      (A : Node s m b → Bool → Set (Fin r)) (B : Node s m b → Bool → Set (Fin c))
      (outR : Set (Fin r)) (outC : Set (Fin c)) (v : Node s m b → Fin r → Fin c → Prop),
    (∀ i e j, dep i e j → level j < level i) →
    (∀ i e j, dep i e j → ∃ z, Here z i ∧ Here z j) →
    (∀ i x y, v i x y ↔ ∀ e, x ∈ A i e ∨ y ∈ B i e ∨ ∃ j, dep i e j ∧ v j x y) →
    ∃ L : (Fin s → Option Bool) → Fin m → (Fin b → Bool) → Set (Fin r),
    ∃ R : (Fin s → Option Bool) → Fin m → (Fin b → Bool) → Set (Fin c),
    ∀ x y, (¬ (x ∈ outR ∨ y ∈ outC ∨ ∃ i, seed i ∧ v i x y)) ↔
      ∃ σ, ∀ z, ∃ β, x ∈ L σ z β ∧ y ∈ R σ z β := by
  classical
  intro r c s m b hm seed dep level A B outR outC v lower contact sem
  refine ⟨fun σ z β => {x | x ∉ outR ∧ localOK seed dep (fun i e => x ∉ A i e) z σ β},
    fun σ z β => {y | y ∉ outC ∧ localOK seed dep (fun i e => y ∉ B i e) z σ β}, ?_⟩
  intro x y
  let z0 : Fin m := ⟨0,hm⟩
  have covered (i : Node s m b) : ∃ z, Here z i := by
    rcases i with a | ⟨q,j⟩
    · exact ⟨z0, trivial⟩
    · exact ⟨q,rfl⟩
  constructor
  · intro reject
    have possible (i) : ∃ e : Bool, ¬v i x y →
        x ∉ A i e ∧ y ∉ B i e ∧ ∀ j, dep i e j → ¬v j x y := by
      by_cases on : v i x y
      · exact ⟨false,fun off => False.elim (off on)⟩
      · have bad := mt (sem i x y).mpr on
        push Not at bad
        obtain ⟨e,he⟩ := bad
        exact ⟨e,fun _ => he⟩
    choose choice hc using possible
    let σ (a : Fin s) : Option Bool := if v (.inl a) x y then none else some (choice (.inl a))
    let T (z : Fin m) (j : Fin b) := ¬v (.inr (z,j)) x y
    refine ⟨σ,fun z => ⟨fun j => choice (.inr (z,j)), ?_⟩⟩
    have active (i : Node s m b) (hi : Here z i) : view σ (T z) i ↔ ¬v i x y := by
      rcases i with a | ⟨q,j⟩
      · by_cases h : v (.inl a) x y <;> simp [view, σ, h]
      · change q = z at hi
        subst q
        rfl
    have arm (i : Node s m b) (hi : Here z i) (off : ¬v i x y) :
        pick σ (fun j => choice (.inr (z,j))) i = choice i := by
      rcases i with a | ⟨q,j⟩
      · simp [pick,σ,off]
      · change q = z at hi
        subst q
        rfl
    have seeds i hi hseed := (active i hi).mpr (fun h => reject (.inr (.inr ⟨i,hseed,h⟩)))
    have step i j hi hj hai hd := by
      have off := (active i hi).mp hai
      exact (active j hj).mpr ((hc i off).2.2 j ((arm i hi off) ▸ hd))
    exact ⟨⟨fun h => reject (.inl h), T z, seeds,
      fun i hi hai => (arm i hi ((active i hi).mp hai)) ▸ (hc i ((active i hi).mp hai)).1,
      step⟩, ⟨fun h => reject (.inr (.inl h)), T z, seeds,
      fun i hi hai => (arm i hi ((active i hi).mp hai)) ▸ (hc i ((active i hi).mp hai)).2.1,
      step⟩⟩
  · rintro ⟨σ,h⟩
    choose β hb using h
    have rows (z) := (hb z).1.2
    have cols (z) := (hb z).2.2
    choose U hsU hrU hdU using rows
    choose V hsV hrV hdV using cols
    let on (i : Node s m b) := splice (fun a => (σ a).isSome = true)
      (fun z j => U z j ∧ V z j) i
    let arm (i : Node s m b) := splice (fun a => (σ a).getD false) β i
    have forms (z) (i : Node s m b) (hi : Here z i) :
        (on i ↔ view σ (U z) i ∧ view σ (V z) i) ∧ arm i = pick σ (β z) i := by
      rcases i with a | ⟨q,j⟩
      · exact ⟨⟨fun h => ⟨h,h⟩,And.left⟩,rfl⟩
      · change q = z at hi
        subst q
        exact ⟨Iff.rfl,rfl⟩
    have off : ∀ n i, level i = n → on i → ¬v i x y := by
      intro n
      induction n using Nat.strong_induction_on with
      | ind n ih =>
        intro i hi hai vi
        obtain ⟨z,hzi⟩ := covered i
        obtain ⟨hu,hv⟩ := (forms z i hzi).1.mp hai
        have rejectRow := hrU z i hzi hu
        have rejectCol := hrV z i hzi hv
        rw [← (forms z i hzi).2] at rejectRow rejectCol
        rcases (sem i x y).mp vi (arm i) with row | col | ⟨j,edge,vj⟩
        · exact rejectRow row
        · exact rejectCol col
        · obtain ⟨q,hqi,hqj⟩ := contact i _ j edge
          obtain ⟨ru,cv⟩ := (forms q i hqi).1.mp hai
          have edge' := (forms q i hqi).2 ▸ edge
          have aj := (forms q j hqj).1.mpr
            ⟨hdU q i j hqi hqj ru edge',hdV q i j hqi hqj cv edge'⟩
          exact ih _ (hi ▸ lower i _ j edge) j rfl aj vj
    rintro (u | w | ⟨i,si,vi⟩)
    · exact (hb z0).1.1 u
    · exact (hb z0).2.1 w
    · obtain ⟨z,hz⟩ := covered i
      exact off _ i rfl ((forms z i hz).1.mpr ⟨hsU z i hz si,hsV z i hz si⟩) vi
