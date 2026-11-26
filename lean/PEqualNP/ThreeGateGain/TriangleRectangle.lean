import Mathlib.Combinatorics.Configuration
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

namespace TriangleOptimality
open Finset

variable {P L : Type*}

/-- No rectangle on distinct rows and distinct columns has four true entries. -/
def NoSquare (G : P → L → Prop) : Prop :=
  ∀ p r l m, G p l → G r l → G p m → G r m → p = r ∨ l = m

noncomputable def hit (G : P → L → Prop) (p : P) (l : L) : ℤ :=
  @ite _ (G p l) (Classical.propDecidable _) 1 0

noncomputable def edges (G : P → L → Prop) (A : Finset P) (B : Finset L) : ℤ :=
  ∑ p ∈ A, ∑ l ∈ B, hit G p l

noncomputable def gain (G : P → L → Prop) (A : Finset P) (B : Finset L) : ℤ :=
  2 * edges G A B - (A.card : ℤ) * B.card

private theorem pair_bound (G : P → L → Prop) (hs : NoSquare G) (B : Finset L)
    {p r : P} (ne : p ≠ r) : (∑ l ∈ B, hit G p l * hit G r l) ≤ 1 := by
  classical
  by_cases ex : ∃ l ∈ B, G p l ∧ G r l
  · obtain ⟨l,hl,hp,hr⟩ := ex
    have h (m : L) : hit G p m * hit G r m ≤ if m=l then 1 else 0 := by
      by_cases a : G p m <;> by_cases b : G r m
      · have eq := (hs p r m l a b hp hr).resolve_left ne
        subst m
        simp [hit,hp,hr]
      all_goals simp [hit,a,b]; split <;> decide
    calc
      _ ≤ ∑ m ∈ B, (if m=l then (1:ℤ) else 0) := sum_le_sum (fun m _ => h m)
      _ = 1 := by simp [hl]
  · have h (m : L) (hm : m ∈ B) : hit G p m * hit G r m = 0 := by
      by_cases a : G p m
      · have b : ¬G r m := fun b => ex ⟨m,hm,a,b⟩
        simp [hit,b]
      · simp [hit,a]
    rw [sum_eq_zero h]; decide

/-- Double-count pairs of distinct points in a column, treating the diagonal exactly. -/
theorem moments (G : P → L → Prop) (hs : NoSquare G) (A : Finset P) (B : Finset L) :
    (edges G A B)^2 ≤ (B.card : ℤ) * (edges G A B + A.card * ((A.card : ℤ)-1)) := by
  classical
  let k (l : L) := ∑ p ∈ A, hit G p l
  have first : ∑ l ∈ B, k l = edges G A B := by
    exact sum_comm
  have diag (p : P) (l : L) : hit G p l * hit G p l = hit G p l := by
    by_cases h : G p l <;> simp [hit,h]
  have second : (∑ l ∈ B, (k l)^2) ≤ edges G A B + A.card * ((A.card : ℤ)-1) := by
    calc
      _ = ∑ p ∈ A, ∑ r ∈ A, ∑ l ∈ B, hit G p l * hit G r l := by
        simp only [k,pow_two,Finset.sum_mul,Finset.mul_sum]
        rw [sum_comm]
        apply sum_congr rfl; intro p _
        rw [sum_comm]
        exact sum_congr rfl (fun r _ => sum_congr rfl (fun l _ => mul_comm _ _))
      _ ≤ ∑ p ∈ A, ∑ r ∈ A, (if r=p then (∑ l ∈ B, hit G p l) else (1:ℤ)) := by
        apply sum_le_sum; intro p _
        apply sum_le_sum; intro r _
        split
        · rename_i e; subst r; simp only [diag,le_refl]
        · rename_i n; exact pair_bound G hs B (Ne.symm n)
      _ = _ := by
        have row (p : P) (hp : p ∈ A) :
            (∑ r ∈ A, (if r=p then (∑ l ∈ B, hit G p l) else (1:ℤ))) =
              (∑ l ∈ B, hit G p l) + ((A.card:ℤ)-1) := by
          rw [← Finset.sum_erase_add _ _ hp]
          rw [Finset.sum_congr (s₂:=A.erase p) (g:=fun _ => (1:ℤ)) rfl
            (fun r hr => ite_eq_right (mem_erase.mp hr).1)]
          simp [Finset.card_erase_of_mem hp, Nat.cast_sub (Finset.card_pos.mpr ⟨p,hp⟩)]
          ring
        rw [sum_congr rfl row, sum_add_distrib]
        simp [edges]; ring
  have cs := sq_sum_le_card_mul_sum_sq (s:=B) (f:=k)
  rw [first] at cs
  exact cs.trans (mul_le_mul_of_nonneg_left second (by positivity))

private theorem numeric {a b e : ℤ} (ha : 2 ≤ a) (hs : a ≤ b)
    (h : e^2 ≤ b*(e+a*(a-1))) : 2*e-a*b ≤ 3 := by
  by_contra! fail
  have hb : 0 ≤ b := by omega
  have h1 : a*b+4 ≤ 2*e := by omega
  have h2 : 0 ≤ a*b+4-2*b := by nlinarith [mul_nonneg (show 0 ≤ a-2 by omega) hb]
  have h3 := mul_le_mul h1 (show a*b+4-2*b ≤ 2*e-2*b by omega) h2 (by nlinarith)
  have k : 0 ≤ b*((a-2)^3 + a*(a-2)*(b-a)) := by
    have : 0 ≤ a-2 := by omega
    have : 0 ≤ b-a := by omega
    positivity
  nlinarith

theorem signed_rectangle (G : P → L → Prop) (hs : NoSquare G)
    (A : Finset P) (B : Finset L) (ha : 2 ≤ A.card) (hb : 2 ≤ B.card) :
    gain G A B ≤ 3 := by
  by_cases h : A.card ≤ B.card
  · exact numeric (by exact_mod_cast ha) (by exact_mod_cast h) (moments G hs A B)
  · have ht : NoSquare (fun l p => G p l) := fun l m p r a b c d =>
      (hs p r l m a c b d).symm
    have hm := moments _ ht B A
    have eq : edges (fun l p => G p l) B A = edges G A B := sum_comm
    rw [eq] at hm
    unfold gain
    rw [mul_comm (A.card : ℤ)]
    exact numeric (by exact_mod_cast hb) (by exact_mod_cast le_of_not_ge h) hm

theorem plane_rectangle {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L]
    (A : Finset P) (B : Finset L) (ha : 2 ≤ A.card) (hb : 2 ≤ B.card) :
    gain (fun p l => p ∈ l) A B ≤ 3 :=
  signed_rectangle _ (fun _ _ _ _ => Configuration.Nondegenerate.eq_or_eq) A B ha hb

#print axioms plane_rectangle
end TriangleOptimality
