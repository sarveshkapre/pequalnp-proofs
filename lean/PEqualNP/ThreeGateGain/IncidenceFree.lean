import Mathlib.Combinatorics.Configuration
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/- The incidence-free estimate of Stinson, together with its consequence
   for a set omitting at least two centers on each shore. -/
namespace PlaneCenterSupports
open Finset Configuration

variable {P L : Type*} [Membership P L] [ProjectivePlane P L] [Fintype P] [Fintype L]

noncomputable def flag (p : P) (l : L) : ℕ :=
  @ite _ (p ∈ l) (Classical.propDecidable _) 1 0

theorem sum_flag (p : P) : (∑ l : L, flag p l) = ProjectivePlane.order P L + 1 := by
  classical
  have h := ProjectivePlane.lineCount_eq L p
  rw [lineCount, Nat.card_eq_fintype_card, Fintype.card_of_subtype
    (univ.filter (fun l : L => p ∈ l)) (by simp)] at h
  simpa [flag, Finset.sum_boole] using h

theorem sum_two_flags [DecidableEq P] (a b : P) :
    (∑ l : L, flag a l * flag b l) =
      (if a = b then ProjectivePlane.order P L else 0) + 1 := by
  classical
  by_cases eq : a=b
  · subst b
    have same (l : L) : flag a l * flag a l = flag a l := by
      by_cases h : a∈l <;> simp [flag,h]
    simp only [same,ite_true,eq_self]
    exact sum_flag a
  · obtain ⟨m,hm,unique⟩ := HasLines.existsUnique_line P L a b eq
    have pin (l : L) : flag a l * flag b l = if l=m then 1 else 0 := by
      by_cases h : l=m
      · subst l; simp [flag,hm.1,hm.2]
      · by_cases ha : a∈l <;> by_cases hb : b∈l <;> simp_all [flag]
    simp [pin,eq]

theorem excluded_sets_bound (X : Finset P) (Y : Finset L)
    (disjoint : ∀ p ∈ X, ∀ l ∈ Y, p ∉ l) :
    X.card * Y.card + ProjectivePlane.order P L * (X.card+Y.card)
      ≤ ProjectivePlane.order P L * Fintype.card L := by
  classical
  let q := ProjectivePlane.order P L
  let count (l : L) := ∑ p ∈ X, flag p l
  have zero_l (l : L) (hl : l∈Y) : count l = 0 := by
    apply sum_eq_zero
    exact fun p hp => by simp [flag,disjoint p hp l hl]
  have m1 : ∑ l : L, count l = X.card * (q+1) := by
    dsimp [count]
    rw [sum_comm]
    simp [sum_flag,q]
  have m2 : ∑ l : L, (count l)^2 = X.card^2+q*X.card := by
    simp only [count, pow_two, sum_mul, mul_sum]
    rw [sum_comm]
    calc
      _ = ∑ a ∈ X, ∑ b ∈ X, ((if a=b then q else 0) + 1) := by
        apply sum_congr rfl
        intro a _
        rw [sum_comm]
        simp_rw [sum_two_flags]
        simp only [q,eq_comm]
      _ = X.card*X.card + q*X.card := by
        simp only [sum_add_distrib,sum_ite_eq,sum_const,nsmul_eq_mul]
        simp [sum_congr rfl (fun a (ha : a∈X) => ite_eq_left ha), mul_comm,add_comm]
  have m1' : ∑ l ∈ univ \ Y, count l = X.card*(q+1) := by
    rw [← m1]
    apply sum_subset (by simp)
    intro l _ hl
    exact zero_l _ (by simpa using hl)
  have m2' : ∑ l ∈ univ \ Y, (count l)^2 = X.card^2+q*X.card := by
    rw [← m2]
    apply sum_subset (by simp)
    intro l _ hl
    simp [zero_l l (by simpa using hl)]
  have cs : (∑ l ∈ univ \ Y, count l)^2 ≤ (univ \ Y).card * (∑ l ∈ univ \ Y, (count l)^2) := by
    exact_mod_cast sq_sum_le_card_mul_sum_sq (s:=univ \ Y) (f:=fun l => (count l : ℤ))
  rw [m1',m2',card_sdiff_of_subset (subset_univ _),card_univ] at cs
  have hy : Y.card ≤ Fintype.card L := card_le_univ _
  have n_all : Fintype.card L = q^2+q+1 := ProjectivePlane.card_lines P L
  by_cases hx : X.card=0
  · simpa [hx] using Nat.mul_le_mul_left q hy
  have factor : X.card * (X.card*(q+1)^2) ≤
      X.card * ((Fintype.card L - Y.card)*(X.card+q)) := by
    convert cs using 1 <;> ring
  have reduced := Nat.le_of_mul_le_mul_left factor (Nat.pos_of_ne_zero hx)
  have sub := Nat.sub_add_cancel hy
  change X.card*Y.card+q*(X.card+Y.card) ≤ q*Fintype.card L
  nlinarith [congrArg (fun z => z*X.card) sub,congrArg (fun z => z*q) sub,
    congrArg (fun z => z*X.card) n_all]

#print axioms excluded_sets_bound

/-- Choosing a common lower bound for the two omissions makes the product
   estimate into a bound on their sum. -/
theorem sum_from_product {x y q n a : ℕ} (hx : a ≤ x) (hy : a ≤ y)
    (bound : x*y + q*(x+y) ≤ q*n) :
    (q+a)*(x+y) ≤ q*n+a^2 := by
  obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le hx
  obtain ⟨v,rfl⟩ := Nat.exists_eq_add_of_le hy
  nlinarith [Nat.zero_le (u*v)]

theorem mixed_sizes {x y q : ℕ} (hx : 0<x) (hy : 0<y)
    (bound : x*y+q*(x+y) ≤ q*(q^2+q+1)) :
    x+y ≤ q^2+1 := by
  have h := sum_from_product (a:=1) hx hy bound
  have prod : (q+1)*(x+y) ≤ (q+1)*(q^2+1) := by nlinarith
  exact Nat.le_of_mul_le_mul_left prod (by omega)

theorem two_omissions {x y q : ℕ} (hx : 2≤x) (hy : 2≤y)
    (bound : x*y+q*(x+y) ≤ q*(q^2+q+1)) :
    x+y+q ≤ q^2+2 := by
  have h := sum_from_product hx hy bound
  by_contra! bad
  have strict : q^2+3 ≤ x+y+q := by omega
  have multiplied := Nat.mul_le_mul_left (q+2) strict
  nlinarith

theorem three_omissions {x y q : ℕ} (hq : 4≤q) (hx : 3≤x) (hy : 3≤y)
    (bound : x*y+q*(x+y) ≤ q*(q^2+q+1)) :
    x+y+q < q^2+2 := by
  have h := sum_from_product hx hy bound
  by_contra! bad
  have multiplied := Nat.mul_le_mul_left (q+3) bad
  obtain ⟨a,rfl⟩ := Nat.exists_eq_add_of_le hq
  nlinarith [Nat.zero_le (a*a)]

/-- In an actual projective plane a vertex cover omitting at least two
   vertices on each shore has at least n+2q−1 distinct centers. -/
theorem two_missing_center_bound (X : Finset P) (Y : Finset L)
    (hx : 2≤X.card) (hy : 2≤Y.card) (away : ∀ p ∈ X, ∀ l ∈ Y, p ∉ l) :
    X.card+Y.card+ProjectivePlane.order P L ≤ (ProjectivePlane.order P L)^2+2 := by
  apply two_omissions hx hy
  simpa [ProjectivePlane.card_lines P L] using excluded_sets_bound X Y away

#print axioms two_missing_center_bound
end PlaneCenterSupports
