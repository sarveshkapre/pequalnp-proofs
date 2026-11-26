import PackedRiffle
import PEqualNP.Defs.RiffleRank
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Log

namespace PackedRiffle
open Finset Polynomial PEqualNP.RiffleRank
open scoped BigOperators

/-- A bound in the repository's original two-block model, with all sample sets
and the injection of the alphabet discharged in characteristic zero. -/
theorem pair_bound (F : Type) [Field F] [CharZero F] (n s t : ℕ) (h : n ≤ s^t) :
    RiffleRankLe ((t*(s-1)+1) * (2*(s-1)+1)^t) (pairId (Fin n) F) := by
  classical
  obtain ⟨enc⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin n) (β := Fin t → Fin s) (by simpa using h)
  let v (i : Fin s) : F := i.val
  let x (i : Fin (sampleCount s 2)) : F := i.val
  let e (i : Fin (t * outerDegree s 2 + 1)) : F := (i.val : F)+1
  have hv : Function.Injective v := fun _ _ h => Fin.ext (Nat.cast_injective h)
  have hx : Function.Injective x := fun _ _ h => Fin.ext (Nat.cast_injective h)
  have he : Function.Injective e := fun _ _ h => Fin.ext (Nat.cast_injective (add_right_cancel h))
  have hnz (j) : e j ≠ 0 := by
    change (j.val : F) + 1 ≠ 0
    rw [← Nat.cast_succ]
    exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  let seq (a c : Fin n) (l : Fin t) (i : ℕ) := if i = 0 then enc a l else enc c l
  let idx := Fin (t * outerDegree s 2 + 1) × (Fin t → Fin (sampleCount s 2))
  let A (z : idx) (a : Fin n) := ∏ l, (inputPoly v (enc a l) 0 (e z.1) 0).eval (x (z.2 l))
  let C (z : idx) (b c : Fin n) := ∏ l,
    (inputPoly v (enc c l) (v (enc b l)) (e z.1) 1).eval (x (z.2 l))
  let D (z : idx) (b d : Fin n) := (basis e z.1).eval 0 * ∏ l,
    (basis x (z.2 l)).eval (addr v (seq b d l) (e z.1) 2)
  let f (z : idx) (a b c d : Fin n) := A z a * C z b c * D z b d
  have total (a b c d : Fin n) : pairId (Fin n) F a b c d = ∑ z, f z a b c d := by
    have hc : (∀ l, ∀ i < 2, seq a c l i = seq b d l i) ↔ a = b ∧ c = d := by
      constructor
      · intro h
        exact ⟨enc.injective (funext fun l => by simpa [seq] using h l 0 (by decide)),
          enc.injective (funext fun l => by simpa [seq] using h l 1 (by decide))⟩
      · rintro ⟨rfl, rfl⟩
        simp
    have H := exact_decomposition (k := 2) v hv x hx e he hnz (seq a c) (seq b d)
    simp only [hc] at H
    rw [Fintype.sum_prod_type]
    refine H.trans ?_
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro u _
    change _ = A (j,u) a * C (j,u) b c * D (j,u) b d
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    unfold A C D
    simp [addr, seq, Finset.sum_range_succ, mul_comm]
  let perm := Fintype.equivFin idx
  have hr : Fintype.card idx = (t*(s-1)+1) * (2*(s-1)+1)^t := by
    have ho : outerDegree s 2 = s-1 := by
      unfold outerDegree
      rw [show 2 = Nat.succ (Nat.succ 0) by decide, Finset.sum_range_succ, Finset.sum_range_succ]
      simp
    unfold idx
    rw [Fintype.card_eq_nat_card, Nat.card_prod, Nat.card_fun]
    simp only [Nat.card_fin, ho, sampleCount]
  rw [← hr]
  refine ⟨fun i => f (perm.symm i), fun i => ⟨_, _, _, fun _ _ _ _ => rfl⟩, ?_⟩
  intro a b c d
  rw [total]
  exact (perm.symm.sum_comp (fun z => f z a b c d)).symm

#print axioms pair_bound

/-- For every d ≥ 1 the two-block rank is O_d(n^(1+1/d)) in characteristic
zero. This is the integer-power form, avoiding real powers and logarithms. -/
theorem pair_exponent_one (F : Type) [Field F] [CharZero F] (d : ℕ) (hd : 0 < d) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n → ∃ r : ℕ, RiffleRankLe r (pairId (Fin n) F) ∧
      r^d ≤ K * n^(d+1) := by
  let s := 4^d
  have hs : 1 < s := Nat.one_lt_pow hd.ne' (by decide)
  refine ⟨s^d * s^(d+1), fun n hn => ?_⟩
  let t := Nat.clog s n
  have hpack : n ≤ s^t := Nat.le_pow_clog hs n
  have hceil : s^t ≤ s*n := by
    have ht : 0 < t := Nat.clog_pos hs hn
    have hpred : s^(t-1) < n := Nat.pow_pred_clog_lt_self s hn
    calc
      s^t = s * s^(t-1) := by rw [← pow_succ']; congr 1; omega
      _ ≤ s*n := Nat.mul_le_mul_left _ hpred.le
  let r := (t*(s-1)+1)*(2*(s-1)+1)^t
  refine ⟨r, pair_bound F n s t hpack, ?_⟩
  have h1 : t*(s-1)+1 ≤ s*2^t := by
    calc
      _ ≤ t*s + s := Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.sub_le ..)) hs.le
      _ = s*(t+1) := by ring
      _ ≤ s*2^t := Nat.mul_le_mul_left _ t.lt_two_pow_self
  have h2 : 2*(s-1)+1 ≤ 2*s := by omega
  have hr : r ≤ s*(4*s)^t := by
    calc
      r ≤ (s*2^t)*(2*s)^t := Nat.mul_le_mul h1 (Nat.pow_le_pow_left h2 _)
      _ = s*(4*s)^t := by rw [Nat.mul_assoc, ← mul_pow]; congr 2; ring
  have he : (4*s)^d = s^(d+1) := by rw [mul_pow, pow_succ']
  calc
    r^d ≤ (s*(4*s)^t)^d := Nat.pow_le_pow_left hr d
    _ = s^d * (s^t)^(d+1) := by
      rw [mul_pow]
      apply congrArg (s^d * ·)
      rw [← pow_mul, Nat.mul_comm t d, pow_mul, he, ← pow_mul, Nat.mul_comm (d+1) t, pow_mul]
    _ ≤ s^d * (s*n)^(d+1) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hceil _)
    _ = _ := by rw [mul_pow]; ring

#print axioms pair_exponent_one
end PackedRiffle
