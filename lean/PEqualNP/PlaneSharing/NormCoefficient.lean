import Mathlib.Tactic

/-! After dividing out a common coefficient and undoing a common Frobenius
power, each output coefficient is a permutation on every norm fibre. This
proves it permutes the entire slope set even for a noncomputable branch table. -/
theorem PEqualNP.PlaneSharing.NormCoefficient :
    ∀ (K E : Type) [Field K] [Finite K] (key : K → E) (branch : E → K ≃+* K)
    (negative : E → Bool) (outer : K ≃+* K) (u : K), u ≠ 0 →
    (∀ z, key (-z) = key z) → (∀ e z, key (branch e z) = key z) →
    Function.Bijective (fun z : K =>
      u * outer (if negative (key z) then -(branch (key z) z) else branch (key z) z)) := by
  intro K E _ _ key branch negative outer u u0 signKey branchKey
  let routed (e : E) (z : K) := if negative e then -(branch e z) else branch e z
  have keeps (e : E) (z : K) : key (routed e z) = key z := by
    cases h : negative e <;> simp [routed,h,signKey,branchKey]
  have inj (e : E) : Function.Injective (routed e) := by
    intro x y eq
    cases h : negative e <;> simpa [routed,h] using eq
  apply Finite.injective_iff_bijective.mp
  intro x y eq
  have terms : routed (key x) x = routed (key y) y := by
    apply outer.injective
    exact mul_left_cancel₀ u0 eq
  have same := congrArg key terms
  rw [keeps,keeps] at same
  rw [← same] at terms
  exact inj _ terms
