import Mathlib.Tactic

open scoped BigOperators

/-! Finite upper bound for the mass of all compatible supports. The recurrence
also allows independent gate destinations to have different incoming laws,
provided a common upper bound on each transition is available. -/
theorem PEqualNP.PaidDepth.SupportMass :
    ∀ (a : ℝ) (w : ℕ → ℝ) (P : ℕ → ℕ → ℝ),
    0 < a → (∀ s, 0 ≤ w s) → (∀ s, w (s + 1) < a) →
    P 0 0 ≤ 1 → (∀ s, P 0 (s + 1) ≤ 0) →
    (∀ n, P (n + 1) 0 ≤ a * P n 0) →
    (∀ n s, P (n + 1) (s + 1) ≤ w (s + 1) * P n (s + 1) + P n s) →
    ∀ n, (∑ s ∈ Finset.range (n + 1), P n s) ≤
      a ^ n * ∑ s ∈ Finset.range (n + 1),
        ∏ j ∈ Finset.range s, (a - w (j + 1))⁻¹ := by
  intro a w P ha hw gap base empty stay step
  let b (s : ℕ) := ∏ j ∈ Finset.range s, (a - w (j + 1))⁻¹
  have pos (s : ℕ) : 0 < b s :=
    Finset.prod_pos (fun j _ => inv_pos.mpr (sub_pos.mpr (gap j)))
  have identity (s : ℕ) : (a - w (s + 1)) * b (s + 1) = b s := by
    have nz := ne_of_gt (sub_pos.mpr (gap s))
    simp only [b, Finset.prod_range_succ]
    field_simp
  have bound (n s : ℕ) : P n s ≤ a ^ n * b s := by
    induction n generalizing s with
    | zero =>
      cases s with
      | zero => simpa [b] using base
      | succ t => simpa using (empty t).trans (pos (t + 1)).le
    | succ n ih =>
      cases s with
      | zero =>
        calc P (n + 1) 0 ≤ a * P n 0 := stay n
             _ ≤ a * (a ^ n * b 0) := mul_le_mul_of_nonneg_left (ih 0) ha.le
             _ = a ^ (n + 1) * b 0 := by ring
      | succ t =>
        calc P (n + 1) (t + 1) ≤ w (t + 1) * P n (t + 1) + P n t := step n t
             _ ≤ w (t + 1) * (a ^ n * b (t + 1)) + a ^ n * b t :=
               add_le_add (mul_le_mul_of_nonneg_left (ih (t + 1)) (hw _)) (ih t)
             _ = a ^ (n + 1) * b (t + 1) := by
               rw [← identity t]
               ring
  intro n
  change _ ≤ a ^ n * ∑ s ∈ Finset.range (n + 1), b s
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun s _ => bound n s
