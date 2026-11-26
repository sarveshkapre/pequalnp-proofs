import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-! Exact rank of the universal AND matrix of the shared-gate family.
Each coordinate pair has four membership patterns. The subset zeta matrix
simultaneously diagonalizes their three local kernels by congruence. -/
namespace SharingRank.Family
open Matrix
open scoped Kronecker Classical
abbrev Four := Fin 4
def Words : Nat → Type
  | 0 => Unit
  | d+1 => Four × Words d
instance wordFinite : (d : Nat) → Fintype (Words d)
  | 0 => inferInstanceAs (Fintype Unit)
  | d+1 => @instFintypeProd _ _ inferInstance (wordFinite d)
instance wordDec : (d : Nat) → DecidableEq (Words d)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | d+1 => letI := wordDec d; inferInstanceAs (DecidableEq (Four × Words d))

def zeta : Matrix Four Four ℝ := !![1,0,0,0; 1,1,0,0; 1,0,1,0; 1,1,1,1]
def weightsAll : Four → ℝ := ![1,0,0,0]
def weightsC : Four → ℝ := ![0,1,0,0]
def weightsQ : Four → ℝ := ![0,1,1,-1]
noncomputable def transform {I : Type} [Fintype I] [DecidableEq I] (a : Matrix I I ℝ)
    (w : I → ℝ) := a * diagonal w * a.transpose

def firstBit (x y : Four) : Bool := x.val.testBit 0 && y.val.testBit 0
def otherBit (x y : Four) : Bool := x.val.testBit 1 && y.val.testBit 1
def someBit (x y : Four) : Bool := firstBit x y || otherBit x y

private theorem local_values (i j : Four) :
    transform zeta weightsAll i j = 1 ∧
    transform zeta weightsC i j = (if firstBit i j then 1 else 0) ∧
    transform zeta weightsQ i j = (if someBit i j then 1 else 0) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [transform,zeta,weightsAll,weightsC,weightsQ,Matrix.mul_apply,Fin.sum_univ_four,
      Matrix.vecMul_diagonal,firstBit,otherBit,someBit,Matrix.transpose_apply,Matrix.diagonal_apply] <;> decide

private theorem kr_transpose {I J : Type} (a : Matrix I I ℝ) (b : Matrix J J ℝ) :
    (a ⊗ₖ b).transpose = a.transpose ⊗ₖ b.transpose := rfl

private theorem combine {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (a : Matrix I I ℝ) (b : Matrix J J ℝ) (v : I → ℝ) (w : J → ℝ) :
    transform a v ⊗ₖ transform b w = transform (a ⊗ₖ b) (fun p => v p.1 * w p.2) := by
  unfold transform
  rw [Matrix.mul_kronecker_mul,Matrix.mul_kronecker_mul,Matrix.diagonal_kronecker_diagonal,kr_transpose]

noncomputable def basis : (d : Nat) → Matrix (Words d) (Words d) ℝ
  | 0 => 1
  | d+1 => zeta ⊗ₖ basis d

private theorem basis_det (d : Nat) : (basis d).det ≠ 0 := by
  have hz : zeta.det = 1 := by
    have lower : zeta.IsLowerTriangular := by
      intro i j h
      change i < j at h
      fin_cases i <;> fin_cases j <;> first | exact False.elim (by revert h; decide) | norm_num [zeta]
    rw [Matrix.det_of_isLowerTriangular _ lower]
    norm_num [zeta,Fin.prod_univ_four,Matrix.diag]
  induction d with
  | zero => exact (by simp [basis])
  | succ d ih =>
    change (zeta ⊗ₖ basis d).det ≠ 0
    rw [Matrix.det_kronecker,hz]
    simp [ih]

def tensorWeight (u : Four → ℝ) : (d : Nat) → Words d → ℝ
  | 0 => fun _ => 1
  | d+1 => fun x => u x.1 * tensorWeight u d x.2

def allPairs (test : Four → Four → Bool) : (d : Nat) → Words d → Words d → Bool
  | 0 => fun _ _ => true
  | d+1 => fun x y => test x.1 y.1 && allPairs test d x.2 y.2

private theorem tensor_values (u : Four → ℝ) (test : Four → Four → Bool)
    (base : ∀ i j, transform zeta u i j = if test i j then 1 else 0) (d : Nat) (x y : Words d) :
    transform (basis d) (tensorWeight u d) x y = if allPairs test d x y then 1 else 0 := by
  induction d with
  | zero =>
    cases x; cases y
    simp [basis,transform,tensorWeight,allPairs,Matrix.one_apply,Matrix.diagonal_apply]
    exact Matrix.one_apply_eq ..
  | succ d ih =>
    obtain ⟨i,x⟩ := x
    obtain ⟨j,y⟩ := y
    change transform (zeta ⊗ₖ basis d) (fun p => u p.1 * tensorWeight u d p.2) (i,x) (j,y) = _
    rw [← combine,Matrix.kronecker_apply,base,ih]
    cases h : test i j <;> cases g : allPairs test d x y <;> simp [allPairs,h,g]

def cell (d : Nat) (x y : Four × Words d) : Bool :=
  allPairs firstBit d x.2 y.2 || (someBit x.1 y.1 && allPairs someBit d x.2 y.2)

noncomputable def mat (d : Nat) : Matrix (Four × Words d) (Four × Words d) ℝ :=
  fun x y => if cell d x y then 1 else 0

noncomputable def coeff (d : Nat) (p : Four × Words d) : ℝ :=
  weightsAll p.1 * tensorWeight weightsC d p.2 +
    weightsQ p.1 * tensorWeight weightsQ d p.2 - weightsQ p.1 * tensorWeight weightsC d p.2

private theorem pair_imp (d : Nat) (x y : Words d) :
    allPairs firstBit d x y = true → allPairs someBit d x y = true := by
  induction d with
  | zero => simp [allPairs]
  | succ d ih =>
    obtain ⟨a,x⟩ := x
    obtain ⟨b,y⟩ := y
    simp only [allPairs,Bool.and_eq_true]
    rintro ⟨h,h'⟩
    exact ⟨by simp [someBit,h],ih x y h'⟩

private theorem factor (d : Nat) : mat d = transform (zeta ⊗ₖ basis d) (coeff d) := by
  classical
  have linear (a : Matrix (Four × Words d) (Four × Words d) ℝ) (p q r : Four × Words d → ℝ) :
      transform a (fun i => p i + q i - r i) = transform a p + transform a q - transform a r := by
    unfold transform
    rw [← Matrix.diagonal_sub,← Matrix.diagonal_add]
    simp only [Matrix.mul_sub,Matrix.mul_add,
      Matrix.sub_mul,Matrix.add_mul,transform]
  unfold coeff
  rw [linear,← combine,← combine,← combine]
  ext x y
  obtain ⟨i,x⟩ := x
  obtain ⟨j,y⟩ := y
  simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.kronecker_apply,(local_values i j).1,
    (local_values i j).2.2,tensor_values weightsC firstBit (fun a b => (local_values a b).2.1),
    tensor_values weightsQ someBit (fun a b => (local_values a b).2.2),one_mul,mat,cell]
  have imply := pair_imp d x y
  by_cases h : allPairs firstBit d x y = true <;> by_cases t : someBit i j = true <;>
    by_cases g : allPairs someBit d x y = true <;> simp_all

theorem rank_coeff (d : Nat) : (mat d).rank = Fintype.card {i // coeff d i ≠ 0} := by
  have hz : (zeta ⊗ₖ basis d).det ≠ 0 := basis_det (d+1)
  rw [factor,transform,Matrix.rank_mul_eq_left_of_det_ne_zero _ _ (by simpa using hz),
      Matrix.rank_mul_eq_right_of_det_ne_zero _ _ hz,Matrix.rank_diagonal]
end SharingRank.Family
