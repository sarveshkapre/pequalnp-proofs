import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace RiffleDictionary

/-- A translate of a dot-product level distinguishes its own symbol on a
    common rational sphere. This is the support step in the direct construction. -/
theorem shell_separates {d : ℕ} (a b t u : Fin d → ℚ)
    (shell : ∑ i, a i ^ 2 = ∑ i, b i ^ 2)
    (layer : ∑ i, b i * t i = ∑ i, b i * u i)
    (collision : ∀ i, a i + t i = b i + u i) : a = b ∧ t = u := by
  have coord : ∀ i, (a i - b i)^2 =
      a i ^ 2 - b i ^ 2 + 2 * (b i * t i - b i * u i) := by
    intro i
    have hi : u i = a i + t i - b i := by linarith [collision i]
    rw [hi]
    ring
  have total : ∑ i, (a i - b i)^2 = 0 := by
    simp_rw [coord]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, shell, layer]
    ring
  have each := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ Finset.univ) => sq_nonneg (a i - b i))).mp total
  have eq : a = b := by
    funext i
    have hi := each i (Finset.mem_univ i)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hi)
  refine ⟨eq, ?_⟩
  funext i
  simpa only [eq, add_right_inj] using collision i

#print axioms shell_separates
end RiffleDictionary
