import PencilRank
import PEqualNP.Defs.RiffleRank
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Finset PEqualNP.RiffleRank
open scoped BigOperators
namespace RiffleLower

private theorem sandwich_apply {F : Type} [Field F] {n r : ℕ}
    (L : Matrix (Fin n) (Fin r) F) (D : Matrix (Fin r) (Fin n) F)
    (w : Fin r → F) (c d : Fin n) :
    (L * Matrix.diagonal w * D) c d = ∑ i, L c i * w i * D i d := by
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal]

private def Dictionary (F : Type) [Field F] (r k n : ℕ) : Prop :=
  ∃ (A : Fin r → Fin k → F) (C : Fin k → Fin n → Fin r → F)
      (D : Fin k → Fin r → Fin n → F), ∀ a b c d,
    ∑ i, C b c i * A i a * D b i d = if a = b ∧ c = d then 1 else 0

private theorem from_riffle {F : Type} [Field F] {n r : ℕ}
    (h : RiffleRankLe r (pairId (Fin n) F)) : Dictionary F r n n := by
  obtain ⟨g, basic, decode⟩ := h
  choose A C D form using basic
  refine ⟨A, fun b c i => C i b c, fun b i d => D i b d, ?_⟩
  intro a b c d
  simpa only [form, pairId, mul_comm (A _ _)] using (decode a b c d).symm

private theorem pivot {F : Type} [Field F] {k n r : ℕ} (hn : 0 < n)
    (A : Fin r → Fin (k+1) → F) (C : Fin (k+1) → Fin n → Fin r → F)
    (D : Fin (k+1) → Fin r → Fin n → F)
    (decode : ∀ a b c d, ∑ i, C b c i * A i a * D b i d =
      if a = b ∧ c = d then 1 else 0) : ∃ i, A i 0 ≠ 0 := by
  by_contra! hz
  have h := decode 0 0 ⟨0, hn⟩ ⟨0, hn⟩
  simp [hz] at h

private theorem shorten {F : Type} [Field F] {k n r : ℕ} (hn : 0 < n)
    (h : Dictionary F (r+1) (k+1) n) : Dictionary F r k n := by
  classical
  obtain ⟨A, C, D, decode⟩ := h
  obtain ⟨p, hp⟩ := pivot hn A C D decode
  let q a := A p (Fin.succ a) / A p 0
  let B (i : Fin (r+1)) (a : Fin k) := A i a.succ - q a * A i 0
  have erased (a : Fin k) : B p a = 0 := by simp [B, q, hp]
  refine ⟨fun i => B (p.succAbove i), fun b c i => C b.succ c (p.succAbove i),
    fun b i d => D b.succ (p.succAbove i) d, ?_⟩
  intro a b c d
  let term i := C b.succ c i * B i a * D b.succ i d
  have all : ∑ i, term i = if a = b ∧ c = d then 1 else 0 := by
    calc
      _ = ∑ i, (C b.succ c i * A i a.succ * D b.succ i d -
          q a * (C b.succ c i * A i 0 * D b.succ i d)) := by
            apply sum_congr rfl; intro i _; dsimp [term, B]; ring
      _ = _ := by rw [sum_sub_distrib, ← mul_sum, decode, decode]; simp [Ne.symm b.succ_ne_zero]
  rw [Fin.sum_univ_succAbove term p] at all
  simpa [term, erased] using all

private theorem pack {F : Type} [Field F] [Infinite F] {k n r : ℕ}
    (hk : 0 < k) (dict : Dictionary F r k n) : k*(2*n) ≤ (k+1)*r := by
  classical
  obtain ⟨A, C, D, decode⟩ := dict
  let col (i : Fin r) : Fin k :=
    if h : ∃ b, A i b ≠ 0 then h.choose else ⟨0,hk⟩
  let v (i : Fin r) (a : Fin k) : F :=
    if ∃ b, A i b ≠ 0 then A i a else if a = col i then 1 else 0
  let L (b : Fin k) : Matrix (Fin n) (Fin r) F := fun c i =>
    if ∃ a, A i a ≠ 0 then C b c i else 0
  let R (b : Fin k) : Matrix (Fin r) (Fin n) F := fun i d => D b i d
  have nonzero (i : Fin r) : v i (col i) ≠ 0 := by
    by_cases h : ∃ b, A i b ≠ 0
    · simpa [v, col, h] using h.choose_spec
    · simp [v, h]
  have coord (a b : Fin k) (c d : Fin n) :
      ∑ i, L b c i * v i a * D b i d = if a = b ∧ c = d then 1 else 0 := by
    rw [← decode]
    apply sum_congr rfl
    intro i _
    by_cases h : ∃ u, A i u ≠ 0
    · simp [L, v, h]
    · have hz : A i a = 0 := by simpa using not_exists.mp h a
      simp [L, v, h, hz]
  let fiber (b : Fin k) := (univ : Finset (Fin r)).filter (fun i => col i = b)
  have each (b : Fin k) : 2*n ≤ r + (fiber b).card := by
    let ev (i : Fin r) : (Fin k → F) →ₗ[F] F :=
      ∑ a : Fin k, (if a = b then 0 else v i a) • LinearMap.proj a
    have exists_one (i : {i // col i ≠ b}) : ∃ x, ev i x ≠ 0 := by
      refine ⟨Pi.single (col i) 1, ?_⟩
      simp only [ev, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
        smul_eq_mul, Pi.single_apply]
      rw [sum_eq_single (col i)]
      · simpa [i.property] using nonzero i
      · intro a _ ha; simp [ha]
      · simp
    obtain ⟨x, hx⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists
      (fun i : {i // col i ≠ b} => ev i) exists_one
    let w (a : Fin k) := if a = b then (0 : F) else x a
    have eval_eq (i : Fin r) : ev i x = ∑ a, w a * v i a := by
      simp only [ev, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        LinearMap.proj_apply]
      apply sum_congr rfl; intro a _; by_cases ha : a = b <;> simp [ha, w, mul_comm]
    have detect : L b * Matrix.diagonal (fun i => v i b) * R b = 1 := by
      ext c d
      rw [sandwich_apply, Matrix.one_apply]
      simpa [R] using coord b b c d
    have kill : L b * Matrix.diagonal (fun i => ev i x) * R b = 0 := by
      ext c d
      rw [sandwich_apply, Matrix.zero_apply]
      simp only [eval_eq, R]
      calc
        _ = ∑ i, ∑ a, w a * (L b c i * v i a * D b i d) := by
          apply sum_congr rfl; intro i _
          rw [mul_sum, sum_mul]
          apply sum_congr rfl; intro a _; ring
        _ = ∑ a, w a * (if a = b ∧ c = d then (1:F) else 0) := by
          rw [sum_comm]; apply sum_congr rfl; intro a _; rw [← mul_sum, coord]
        _ = 0 := sum_eq_zero fun a _ => by by_cases h : a = b <;> simp [h, w]
    have mat := RifflePencil.annihilator_count (L b) (R b) _ _ detect kill
    have incl : (univ.filter (fun i : Fin r => col i ≠ b)).card ≤
        (univ.filter (fun i : Fin r => ev i x ≠ 0)).card :=
      card_le_card (fun i hi => mem_filter.mpr ⟨mem_univ _, hx ⟨i,(mem_filter.mp hi).2⟩⟩)
    have split := card_filter_add_card_filter_not (s := (univ : Finset (Fin r))) (p := fun i => col i = b)
    simp only [Fintype.card_subtype] at mat
    simp only [card_univ, Fintype.card_fin] at split
    change (univ.filter (fun i : Fin r => ¬ col i = b)).card ≤ _ at incl
    change 2*n ≤ r + (univ.filter _).card
    omega
  have hsum := sum_le_sum (s := (univ : Finset (Fin k))) (fun b _ => each b)
  have hf : ∑ b : Fin k, (fiber b).card = r := by
    simpa [fiber] using (card_eq_sum_card_fiberwise (s := (univ : Finset (Fin r)))
      (t := (univ : Finset (Fin k))) (f := col) (by simp)).symm
  simpa [sum_add_distrib, hf, Nat.add_mul] using hsum

/-- Every exact two-block riffle dictionary over an infinite field satisfies
the quotient bound at each remaining input dimension m. -/
theorem pair_lower {F : Type} [Field F] [Infinite F] {n r : ℕ}
    (dec : RiffleRankLe r (pairId (Fin n) F)) {m : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    m*(2*n) + (m+1)*(n-m) ≤ (m+1)*r := by
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  have reduce (s : ℕ) : ∀ r', Dictionary F r' (m+s) n →
      m*(2*n) + (m+1)*s ≤ (m+1)*r' := by
    induction s with
    | zero => intro r' h; simpa using pack hm h
    | succ s ih =>
      intro r' h
      cases r' with
      | zero =>
        obtain ⟨A, C, D, hd⟩ := h
        obtain ⟨i, _⟩ := pivot hn A C D hd
        exact Fin.elim0 i
      | succ r' =>
        have out := ih r' (shorten hn h)
        simpa only [Nat.mul_succ, ← Nat.add_assoc] using Nat.add_le_add_right out (m+1)
  apply reduce (n-m) r
  simpa [Nat.add_sub_of_le hmn] using from_riffle dec

#print axioms pair_lower

/-- Scalar extension preserves every rank-one term, so the same lower bound
also applies over finite fields. -/
theorem pair_lower_all_fields {F : Type} [Field F] {n r : ℕ}
    (dec : RiffleRankLe r (pairId (Fin n) F)) {m : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    m*(2*n) + (m+1)*(n-m) ≤ (m+1)*r := by
  classical
  let K := RatFunc F
  let _ : Infinite K := Infinite.of_injective _ (RatFunc.algebraMap_injective F)
  let φ := algebraMap F K
  obtain ⟨g, basic, decode⟩ := dec
  have lifted : RiffleRankLe r (pairId (Fin n) K) := by
    refine ⟨fun i a b c d => φ (g i a b c d), ?_, ?_⟩
    · intro i
      obtain ⟨A,C,D,form⟩ := basic i
      refine ⟨fun a => φ (A a), fun b c => φ (C b c), fun b d => φ (D b d), ?_⟩
      intro a b c d
      simp [form]
    · intro a b c d
      have h := congrArg φ (decode a b c d)
      simpa only [pairId, apply_ite φ, map_one, map_zero, map_sum] using h
  exact pair_lower lifted hm hmn

#print axioms pair_lower_all_fields

theorem pair_lower_near_three {F : Type} [Field F] {n r m : ℕ}
    (dec : RiffleRankLe r (pairId (Fin n) F)) (hm : 0 < m) (hmn : m ≤ n)
    (cap : 2*n ≤ (m+1)^2) : 3*n + 1 ≤ r + 2*(m+1) := by
  have h := pair_lower_all_fields dec hm hmn
  have he := Nat.sub_add_cancel hmn
  by_contra! hn
  have bad : r + 2*(m+1) ≤ 3*n := by omega
  have hb := Nat.mul_le_mul_left (m+1) bad
  have hs := congrArg (fun x => (m+1)*x) he
  nlinarith only [hb, hs, h, cap]

theorem pair_lower_32 {F : Type} [Field F] {r : ℕ}
    (dec : RiffleRankLe r (pairId (Fin 32) F)) : 81 ≤ r := by
  have h := pair_lower_all_fields dec (m := 7) (by decide) (by decide)
  omega

#print axioms pair_lower_near_three
#print axioms pair_lower_32

end RiffleLower
