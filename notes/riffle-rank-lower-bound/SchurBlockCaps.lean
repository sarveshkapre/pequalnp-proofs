import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open Finset
open scoped BigOperators

namespace RiffleBlockCaps

def combine {F : Type*} [Field F] {r k : ℕ} (A : Fin r → Fin k → F) :
    (Fin r → F) →ₗ[F] (Fin k → F) where
  toFun x a := ∑ i, x i * A i a
  map_add' x y := by ext a; simp [add_mul, sum_add_distrib]
  map_smul' z x := by ext a; simp [mul_assoc, mul_sum]

/-- A decoder's product code maps into its target line under the shared matrix.
The row-by-column products span the product of the two generator spaces by bilinearity. -/
theorem product_in_target {F : Type*} [Field F] {k n r : ℕ} (b : Fin k)
    (A : Fin r → Fin k → F) (L : Fin n → Fin r → F) (B : Fin r → Fin n → F)
    (decode : ∀ a c d, ∑ i, L c i * A i a * B i d =
      if a = b ∧ c = d then 1 else 0) :
    Submodule.span F (Set.range (fun cd : Fin n × Fin n => fun i => L cd.1 i * B i cd.2)) ≤
      (Submodule.span F ({Pi.single b (1 : F)} : Set (Fin k → F))).comap (combine A) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨c,d⟩,rfl⟩
  change combine A (fun i => L c i * B i d) ∈
    Submodule.span F ({Pi.single b (1 : F)} : Set (Fin k → F))
  have eq : combine A (fun i => L c i * B i d) =
      if c = d then Pi.single b (1 : F) else 0 := by
    ext a
    change ∑ i, (L c i * B i d) * A i a = _
    simp_rw [mul_right_comm (L c _) (B _ d) (A _ a)]
    rw [decode]
    by_cases ha : a = b <;> by_cases hc : c = d <;> simp [ha,hc]
  rw [eq]
  split
  · exact Submodule.subset_span (Set.mem_singleton _)
  · exact Submodule.zero_mem _

/-- Lower bounds already available at the stage where a row is used.
For each row only entries strictly below its target count are accessed. -/
def lower : ℕ → ℕ
  | 0 => 0 | 1 => 32 | 2 => 48 | 3 => 56 | 4 => 60 | 5 => 62
  | 6 => 63 | 7 => 64 | 8 => 66 | 9 => 67 | 10 => 68 | 11 => 70
  | 12 => 71 | 13 => 72 | 14 => 74 | 15 => 75 | 16 => 76 | _ => 0

def slope (k r M numerator denominator : ℕ) : Prop :=
  ∀ (m : Fin (M+1)) (t : Fin (k+1)),
    3 ≤ m.val → min 4 m.val ≤ t.val → t.val ≤ m.val →
    lower (k-t.val) + m.val ≤ r →
    denominator * (m.val - t.val + 2) ≤ numerator * m.val

instance (k r M a b : ℕ) : Decidable (slope k r M a b) := by
  unfold slope
  infer_instance

set_option maxRecDepth 12000
set_option maxHeartbeats 8000000

theorem eight_block : slope 8 65 51 9 10 := by decide
theorem eleven_block : slope 11 69 58 7 8 := by decide
theorem fourteen_block : slope 14 73 65 5 6 := by decide
theorem seventeen_block : slope 17 77 72 4 5 := by decide

/-- Assembly of all individual bounds, allowing one exceptional small block. -/
theorem sum_exclusion {I : Type*} [Fintype I] [DecidableEq I]
    (size cap : I → ℕ) (p : I) (r a b extra : ℕ)
    (budget : ∑ i, size i ≤ r) (demand : 64 ≤ ∑ i, cap i)
    (bound : ∀ i, b * cap i ≤ a * size i + (if p = i then extra else 0))
    (strict : a*r+extra < b*64) : False := by
  have summed := sum_le_sum (s := (univ : Finset I)) (fun i _ => bound i)
  simp only [sum_add_distrib, ← mul_sum, sum_ite_eq, mem_univ, ite_true] at summed
  have lo := Nat.mul_le_mul_left b demand
  have hi := Nat.mul_le_mul_left a budget
  omega

theorem four_budgets :
    9*65+(2*10-9) < 10*64 ∧ 7*69+(2*8-7) < 8*64 ∧
    5*73+(2*6-5) < 6*64 ∧ 4*77+(2*5-4) < 5*64 := by decide

#print axioms product_in_target
#print axioms eight_block
#print axioms eleven_block
#print axioms fourteen_block
#print axioms seventeen_block
#print axioms sum_exclusion
#print axioms four_budgets

end RiffleBlockCaps
