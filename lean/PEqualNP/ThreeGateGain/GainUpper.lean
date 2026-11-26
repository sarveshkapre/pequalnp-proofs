import PEqualNP.ThreeGateGain.GainTrim
import PEqualNP.ThreeGateGain.GainCircuit
import PEqualNP.ThreeGateGain.GainPhysicalUpper

namespace GainUpper
open GainFinite GainGeometry TriangleOptimality Finset Configuration
open scoped Classical

variable {P L : Type*} [Fintype P] [Fintype L] [Membership P L] [ProjectivePlane P L]

private theorem restricted_row (p : P) (B : Finset L) :
    (∑ l ∈ B, hit (fun (p:P) (l:L) => p ∈ l) p l) ≤ (ProjectivePlane.order P L : ℤ) + 1 := by
  rw [← row_total p]
  apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
  intro l _ _; simp only [hit]; split <;> decide

private theorem restricted_column (l : L) (A : Finset P) :
    (∑ p ∈ A, hit (fun (p:P) (l:L) => p ∈ l) p l) ≤ (ProjectivePlane.order P L : ℤ) + 1 := by
  rw [← col_total l]
  apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
  intro p _ _; simp only [hit]; split <;> decide

theorem plane (checks : ∀ h : Host, checkHost h = true)
    (hq : 16 ≤ ProjectivePlane.order P L) (w : BitVec 9) (r : P → BitVec 6)
    (c : L → BitVec 6) (rawP : P → Bool) (rawL : L → Bool) :
    score (fun p l => p ∈ l) (fun p l =>
      (rawP p || rawL l || threeValue w (r p ||| c l)) = true) univ univ ≤
      10 * (ProjectivePlane.order P L : ℤ) - 2 := by
  obtain ⟨A,B,bound,rpos,cpos⟩ := GainTrim.normalize w r c rawP rawL (by omega : 3 ≤ ProjectivePlane.order P L)
  have sq : TriangleOptimality.NoSquare (fun (p:P) (l:L) => p ∈ l) :=
    fun _ _ _ _ u v s t => Nondegenerate.eq_or_eq u v s t
  let h := scalarHost (wiringScalar w)
  have upper := GainFrameBridge.physical_upper (fun (p:P) (l:L) => p ∈ l) sq h
    (fun p => wordType (wiringScalar w) (r p)) (fun l => wordType (wiringScalar w) (c l))
    A B ((ProjectivePlane.order P L : ℤ)+1) (by omega)
    (fun p _ => restricted_row p B) (fun l _ => restricted_column l A) rpos cpos (checks h)
  linarith [bound.trans upper]

/-- A corollary for the existing list-of-gates semantics, at any numbering of
the vertices. The circuit may spend fewer than three intersections. -/
theorem ordinary (checks : ∀ h : Host, checkHost h = true)
    (hq : 16 ≤ ProjectivePlane.order P L) {R C n : Nat} (budget : n ≤ 3)
    (program : FanoFiveUpper.Circuit n) (out : FanoFiveUpper.Arm n)
    (rp : P → Fin R) (cl : L → Fin C) :
    score (fun p l => p ∈ l)
      (fun p l => out.eval (rp p) (cl l) (program.eval (rp p) (cl l)) = true) univ univ ≤
        10 * (ProjectivePlane.order P L : ℤ) - 2 := by
  obtain ⟨next, o, same⟩ := GainCircuit.pad (R:=R) (C:=C) budget program out
  obtain ⟨w,r,c,word⟩ := GainCircuit.circuit_words (R:=R) (C:=C) next o
  simpa only [same,word] using plane (P:=P) (L:=L) checks hq w (fun p => r (rp p))
    (fun l => c (cl l)) (fun p => o.pointMask.testBit (rp p).val) (fun l => o.lineMask.testBit (cl l).val)

end GainUpper
