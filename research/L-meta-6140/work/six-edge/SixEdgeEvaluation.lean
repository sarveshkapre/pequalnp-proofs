import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

namespace SixEdge

/-- A schedule records the value of each finished stage. The function for the
next stage uses the values of its earlier ports on the same input row. -/
def evalSchedule (stage : ℕ → (ℕ → Bool) → Bool) (mute : Option ℕ) :
    ℕ → ℕ → Bool
  | 0 => fun _ => false
  | k+1 => Function.update (evalSchedule stage mute k) k
      (if mute = some k then false else stage k (evalSchedule stage mute k))

theorem mute_below (stage : ℕ → (ℕ → Bool) → Bool) (m : ℕ) :
    ∀ k ≤ m, evalSchedule stage (some m) k = evalSchedule stage none k := by
  intro k
  induction k with
  | zero => simp [evalSchedule]
  | succ k ih =>
    intro h
    have ne : m ≠ k := by omega
    simp [evalSchedule, ne, ih (by omega)]

theorem mute_monotone (stage : ℕ → (ℕ → Bool) → Bool) (mono : ∀ j, Monotone (stage j))
    (m k : ℕ) : evalSchedule stage (some m) k ≤ evalSchedule stage none k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    intro q
    by_cases isStage : q = k
    · subst q
      simp only [evalSchedule, Function.update_self, reduceCtorEq, ite_false]
      split
      · exact Bool.false_le _
      · exact mono k ih
    · simpa [evalSchedule, Function.update_of_ne isStage] using ih q

theorem mute_when_off (stage : ℕ → (ℕ → Bool) → Bool) {m : ℕ}
    (off : stage m (evalSchedule stage none m) = false) :
    ∀ k, evalSchedule stage (some m) k = evalSchedule stage none k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases h : m = k
    · subst k
      simp [evalSchedule, ih, off]
    · simp [evalSchedule, ih, h]

private theorem true_le_eq {b : Bool} (h : true ≤ b) : b = true := by
  cases b
  · exact ((by decide : ¬ true ≤ false) h).elim
  · rfl

/-- Muting a stage that stays off on residual incidences preserves every test.
    The retained incidences already fire on raw literals, independent of the
    internal gates. Monotonicity handles the negative rows. -/
theorem mute_preserves_tests {Row : Type}
    (stage : Row → ℕ → (ℕ → Bool) → Bool)
    (output : Row → (ℕ → Bool) → Bool)
    (monoStage : ∀ r j, Monotone (stage r j)) (monoOut : ∀ r, Monotone (output r))
    (positive retained : Row → Prop) (m k : ℕ)
    (correct : ∀ r, output r (evalSchedule (stage r) none k) = true ↔ positive r)
    (already : ∀ r, retained r → output r (fun _ => false) = true)
    (off : ∀ r, positive r → ¬ retained r →
      stage r m (evalSchedule (stage r) none m) = false) :
    ∀ r, output r (evalSchedule (stage r) (some m) k) = true ↔ positive r := by
  intro r
  constructor
  · intro fires
    apply (correct r).mp
    apply true_le_eq
    simpa [fires] using monoOut r (mute_monotone _ (monoStage r) m k)
  · intro pos
    by_cases kept : retained r
    · apply true_le_eq
      simpa [already r kept] using
        monoOut r (show (fun _ => false) ≤ evalSchedule (stage r) (some m) k from
          fun _ => Bool.false_le _)
    · rw [mute_when_off _ (off r pos kept) k]
      exact (correct r).mpr pos

#print axioms mute_preserves_tests

end SixEdge
