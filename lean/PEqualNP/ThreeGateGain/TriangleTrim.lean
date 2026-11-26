import PEqualNP.ThreeGateGain.TriangleErrorBounds

namespace TriangleOptimality
open Finset Configuration

private theorem sel {α : Type*} [Fintype α] [DecidableEq α] (s : Finset α) (f : α → ℤ) :
    (∑ a : α, if a∈s then f a else 0) = ∑ a ∈ s, f a := by rw [← sum_filter]; simp

private theorem pull {α : Type*} [Fintype α] (c : Prop) [Decidable c] (f : α → ℤ) :
    (∑ a : α, if c then f a else 0) = if c then ∑ a : α, f a else 0 := by
  by_cases h : c <;> simp [h]

variable {P L : Type*} [Fintype P] [Fintype L]

/-- Summing any weight on the union of whole rows and columns, counting its overlap once. -/
private theorem star_sum [DecidableEq P] [DecidableEq L] (X : Finset P) (Y : Finset L) (v : P → L → ℤ) :
    (∑ p : P, ∑ l : L, if p ∈ X ∨ l ∈ Y then v p l else 0) =
      (∑ p ∈ X, ∑ l : L, v p l) + (∑ l ∈ Y, ∑ p : P, v p l) - ∑ p ∈ X, ∑ l ∈ Y, v p l := by
  classical
  have each (p : P) (l : L) :
      (if p ∈ X ∨ l ∈ Y then v p l else 0) =
        (if p∈X then v p l else 0) + (if l∈Y then v p l else 0) -
          (if p∈X then (if l∈Y then v p l else 0) else 0) := by
    by_cases a : p∈X <;> by_cases b : l∈Y <;> simp [a,b]
  simp_rw [each]; simp only [sum_sub_distrib,sum_add_distrib]
  rw [sum_comm (f:=fun p l => if l∈Y then v p l else 0)]
  simp_rw [pull,sel]

private theorem star_numeric {a b n d flags : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (_hd : 0 ≤ d)
    (hn : 3*d ≤ n) (han : a ≤ n) (hbn : b ≤ n) (h₁ : flags ≤ d*(a+b)) (h₂ : flags ≤ n*d) :
    2*flags ≤ n*(a+b)-a*b := by
  by_cases aBig : 2*d ≤ a
  · nlinarith [mul_nonneg (show 0 ≤ n-a by omega) hb,
      mul_nonneg (show 0 ≤ a-2*d by omega) (show 0 ≤ n by omega)]
  by_cases bBig : 2*d ≤ b
  · nlinarith [mul_nonneg (show 0 ≤ n-b by omega) ha,
      mul_nonneg (show 0 ≤ b-2*d by omega) (show 0 ≤ n by omega)]
  nlinarith [mul_nonneg (show 0 ≤ 2*d-a by omega) hb,
    mul_nonneg (show 0 ≤ 2*d-b by omega) ha, mul_nonneg (show 0 ≤ n-3*d by omega) (add_nonneg ha hb)]

variable [Membership P L] [ProjectivePlane P L]

/-- For order at least three, adding whole raw stars to a disjoint prediction
cannot improve total accuracy. The lower threshold matters for the count used here. -/
theorem trim_full_stars (X : Finset P) (Y : Finset L) (z : Set (P×L))
    (hq : 3 ≤ ProjectivePlane.order P L)
    (full : ∀ p l, p∈X ∨ l∈Y → (p,l)∉z) :
    let trimmed := z ∪ {u : P×L | u.1∈X ∨ u.2∈Y}
    errors (fun (p:P) (l:L) => p∈l) trimmed ≤ errors (fun (p:P) (l:L) => p∈l) z := by
  classical
  let I (p:P) (l:L) := hit (fun p l => p∈l) p l
  let q : ℤ := ProjectivePlane.order P L
  let n : ℤ := Fintype.card P
  let d := q+1
  have nline : (Fintype.card L : ℤ) = n := by
    dsimp [n]; exact_mod_cast (ProjectivePlane.card_points_eq_card_lines P L).symm
  have nval : n = q^2+q+1 := by dsimp [n,q]; exact_mod_cast ProjectivePlane.card_points P L
  have large : 3*d ≤ n := by
    have h : 3 ≤ q := by dsimp [q]; exact_mod_cast hq
    dsimp [d]; nlinarith [mul_nonneg (show 0 ≤ q-3 by omega) (show 0 ≤ q+1 by omega)]
  let flags := ∑ p : P, ∑ l : L, if p∈X ∨ l∈Y then I p l else 0
  have row (p:P) : (∑ l : L, I p l)=d := row_total p
  have col (l:L) : (∑ p : P, I p l)=d := col_total l
  have pos (p:P) (l:L) : 0 ≤ I p l := by by_cases a : p∈l <;> simp [I,hit,a]
  have f₁ : flags ≤ d*((X.card:ℤ)+Y.card) := by
    dsimp only [flags]; rw [star_sum]; simp_rw [row,col]
    have t : 0 ≤ ∑ p ∈ X, ∑ l ∈ Y, I p l :=
      sum_nonneg (fun p _ => sum_nonneg (fun l _ => pos p l))
    simp only [sum_const,nsmul_eq_mul]; nlinarith
  have f₂ : flags ≤ n*d := by
    calc
      _ ≤ ∑ p : P, ∑ l : L, I p l := by
        apply sum_le_sum; intro p _
        apply sum_le_sum; intro l _
        split <;> first | rfl | exact pos p l
      _ = _ := by simp [row,n]
  have cap := star_numeric (a:=(X.card:ℤ)) (b:=(Y.card:ℤ)) (n:=n) (d:=d) (flags:=flags)
    (by positivity) (by positivity) (by dsimp [d,q]; positivity) large
    (by dsimp [n]; exact_mod_cast card_le_univ X) (by rw [← nline]; exact_mod_cast card_le_univ Y) f₁ f₂
  let t := z ∪ {u : P×L | u.1∈X ∨ u.2∈Y}
  let err (Z : Set (P×L)) (p:P) (l:L) := hit (fun p l => ¬ ((p,l)∉Z ↔ p∈l)) p l
  have diff (p:P) (l:L) : err t p l - err z p l =
      2*(if p∈X ∨ l∈Y then I p l else 0) - (if p∈X ∨ l∈Y then 1 else 0) := by
    have h := full p l
    by_cases a : p∈l <;> by_cases b : (p,l)∈z <;>
      by_cases x : p∈X <;> by_cases y : l∈Y <;> simp_all [err,I,t,hit]
  have diffSum := congrArg (fun f : P → L → ℤ => ∑ p : P, ∑ l : L, f p l)
    (funext fun p => funext (diff p))
  change (∑ p : P, ∑ l : L, err t p l) ≤ ∑ p : P, ∑ l : L, err z p l
  simp only [sum_sub_distrib,← Finset.mul_sum] at diffSum
  rw [star_sum X Y (fun _ _ => 1)] at diffSum
  change 2*(∑ p : P, ∑ l : L, if p∈X ∨ l∈Y then I p l else 0) ≤ _ at cap
  simp only [sum_const,card_univ,nsmul_eq_mul,mul_one,nline] at diffSum
  dsimp only [n] at *
  nlinarith

#print axioms trim_full_stars
end TriangleOptimality
