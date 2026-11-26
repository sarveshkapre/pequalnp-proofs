import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! Evaluations at packed prefixes give an exact riffle decomposition over a field
with enough sampling points. Indices i, j below start at zero. -/
namespace PackedRiffle
open Finset Polynomial
open scoped BigOperators Polynomial
variable {F : Type} [Field F] {s k : ℕ}

noncomputable def basis {m : ℕ} (v : Fin m → F) (i : Fin m) : F[X] :=
  Lagrange.basis univ v i

private theorem basis_degree {m : ℕ} {v : Fin m → F} (hv : Function.Injective v) (i : Fin m) :
    (basis v i).natDegree = m - 1 := by
  simpa [basis] using Lagrange.natDegree_basis hv.injOn (mem_univ i)

theorem interpolate_eval {m : ℕ} (v : Fin m → F) (hv : Function.Injective v)
    (p : F[X]) (hp : p.natDegree < m) (z : F) :
    p.eval z = ∑ j, p.eval (v j) * (basis v j).eval z := by
  have hd : p.degree < ↑(univ : Finset (Fin m)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact p.degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hp)
  have he := congrArg (fun f : F[X] => f.eval z) (Lagrange.eq_interpolate hv.injOn hd)
  simpa [Lagrange.interpolate_apply, eval_finsetSum, basis] using he

def addr (v : Fin s → F) (b : ℕ → Fin s) (e : F) (i : ℕ) : F :=
  ∑ j ∈ range i, v (b j) * e ^ j

noncomputable def tailPoly (v : Fin s → F) (b : ℕ → Fin s) (i k : ℕ) : F[X] :=
  ∑ j ∈ range (k-i), C (v (b (i+j))) * X ^ j

private theorem tail_eval (v : Fin s → F) (b : ℕ → Fin s) (e : F) (he : e ≠ 0)
    {i k : ℕ} (hik : i ≤ k) :
    (addr v b e k - addr v b e i) * (e^i)⁻¹ = (tailPoly v b i k).eval e := by
  have hs := Finset.sum_range_add (fun j => v (b j) * e^j) i (k-i)
  rw [Nat.add_sub_of_le hik] at hs
  simp only [addr, hs, add_sub_cancel_left, tailPoly, eval_finsetSum, eval_mul, eval_C,
    eval_pow, eval_X, Finset.sum_mul, pow_add]
  apply Finset.sum_congr rfl
  intro j hj
  field_simp

private theorem tail_zero (v : Fin s → F) (b : ℕ → Fin s) {i k : ℕ} (hi : i < k) :
    (tailPoly v b i k).eval 0 = v (b i) := by
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.sub_pos_of_lt hi).ne'
  simp [tailPoly, hr, Finset.sum_range_succ', eval_finsetSum]

private theorem tail_degree (v : Fin s → F) (b : ℕ → Fin s) (i k : ℕ) :
    (tailPoly v b i k).natDegree ≤ k-1-i := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  have h := mem_range.mp hj
  exact (Polynomial.natDegree_mul_le.trans (by simp)).trans (show j ≤ k-1-i by omega)

noncomputable def inputPoly (v : Fin s → F) (a : Fin s) (p e : F) (i : ℕ) : F[X] :=
  (basis v a).comp ((X - C p) * C ((e^i)⁻¹))

private theorem input_degree (v : Fin s → F) (hv : Function.Injective v)
    (a : Fin s) (p e : F) (i : ℕ) :
    (inputPoly v a p e i).natDegree ≤ s-1 := by
  have h : ((X - C p) * C ((e ^ i)⁻¹)).natDegree ≤ 1 := by
    refine Polynomial.natDegree_mul_le.trans ?_
    simp
  exact Polynomial.natDegree_comp_le.trans (by
    rw [basis_degree hv]
    simpa using Nat.mul_le_mul_left (s-1) h)

def sampleCount (s k : ℕ) := k*(s-1)+1
def outerDegree (s k : ℕ) := ∑ i ∈ range k, (s-1)*(k-1-i)

noncomputable def digitPolynomial (v : Fin s → F) (a b : ℕ → Fin s) (k : ℕ) : F[X] :=
  ∏ i ∈ range k, (basis v (a i)).comp (tailPoly v b i k)

private theorem digit_degree (v : Fin s → F) (hv : Function.Injective v) (a b : ℕ → Fin s) :
    (digitPolynomial v a b k).natDegree ≤ outerDegree s k := by
    refine (Polynomial.natDegree_prod_le ..).trans (Finset.sum_le_sum fun i _ => ?_)
    exact Polynomial.natDegree_comp_le.trans (by
      rw [basis_degree hv]
      exact Nat.mul_le_mul_left _ (tail_degree v b i k))

private theorem digit_zero (v : Fin s → F) (hv : Function.Injective v) (a b : ℕ → Fin s) :
    (digitPolynomial v a b k).eval 0 = (if ∀ i < k, a i = b i then (1:F) else 0) := by
    simp only [digitPolynomial, eval_prod, eval_comp]
    split_ifs with h
    · refine Finset.prod_eq_one fun i hi => ?_
      rw [tail_zero v b (mem_range.mp hi), h i (mem_range.mp hi)]
      exact Lagrange.eval_basis_self hv.injOn (mem_univ _)
    · push Not at h
      obtain ⟨i, hi, hab⟩ := h
      refine Finset.prod_eq_zero (mem_range.mpr hi) ?_
      rw [tail_zero v b hi]
      exact Lagrange.eval_basis_of_ne hab (mem_univ _)

private theorem digit_sample (v : Fin s → F) (hv : Function.Injective v)
    (nodes : Fin (sampleCount s k) → F) (hn : Function.Injective nodes)
    (a b : ℕ → Fin s) (e : F) (he : e ≠ 0) :
    (digitPolynomial v a b k).eval e = ∑ u,
      (basis nodes u).eval (addr v b e k) *
        ∏ i ∈ range k, (inputPoly v (a i) (addr v b e i) e i).eval (nodes u) := by
  let H : F[X] := ∏ i ∈ range k, inputPoly v (a i) (addr v b e i) e i
  have hd : H.natDegree < sampleCount s k := by
    refine Nat.lt_succ_of_le ((Polynomial.natDegree_prod_le ..).trans ?_)
    calc
      _ ≤ ∑ _i ∈ range k, (s-1) := Finset.sum_le_sum fun i _ => input_degree v hv _ _ _ i
      _ = k*(s-1) := by simp
  have value : (digitPolynomial v a b k).eval e = H.eval (addr v b e k) := by
    simp only [digitPolynomial, H, inputPoly, eval_prod, eval_comp, eval_mul, eval_sub, eval_X, eval_C]
    exact Finset.prod_congr rfl fun i hi =>
      congrArg (fun z => (basis v (a i)).eval z)
        (tail_eval v b _ he (le_of_lt (mem_range.mp hi))).symm
  rw [value, interpolate_eval nodes hn H hd]
  apply Finset.sum_congr rfl
  intro u _
  simp only [H, eval_prod, mul_comm]

/-- One common interpolation step for all t digits. The inner summand has one
decoder depending only on b, and for each i a factor using only a_i and b_{<i}. -/
theorem exact_decomposition {t : ℕ}
    (v : Fin s → F) (hv : Function.Injective v)
    (nodes : Fin (sampleCount s k) → F) (hn : Function.Injective nodes)
    (steps : Fin (t * outerDegree s k + 1) → F) (hs : Function.Injective steps)
    (hnz : ∀ j, steps j ≠ 0) (a b : Fin t → ℕ → Fin s) :
    (if ∀ h, ∀ i < k, a h i = b h i then (1:F) else 0) =
      ∑ j, ∑ u : Fin t → Fin (sampleCount s k),
        ((basis steps j).eval 0 * ∏ h, (basis nodes (u h)).eval (addr v (b h) (steps j) k)) *
          ∏ i ∈ range k, ∏ h, (inputPoly v (a h i) (addr v (b h) (steps j) i)
            (steps j) i).eval (nodes (u h)) := by
  classical
  let G : F[X] := ∏ h, digitPolynomial v (a h) (b h) k
  have gd : G.natDegree ≤ t * outerDegree s k := by
    refine (Polynomial.natDegree_prod_le ..).trans ?_
    calc
      _ ≤ ∑ _h : Fin t, outerDegree s k := Finset.sum_le_sum fun h _ => digit_degree v hv _ _
      _ = t * outerDegree s k := by simp
  have gz : G.eval 0 = (if ∀ h, ∀ i < k, a h i = b h i then (1:F) else 0) := by
    simp only [G, eval_prod, digit_zero v hv]
    split_ifs with hall
    · exact Finset.prod_eq_one fun h _ => ite_eq_left (hall h)
    · obtain ⟨h, hh⟩ := Classical.not_forall.mp hall
      exact Finset.prod_eq_zero (mem_univ h) (ite_eq_right hh)
  rw [← gz, interpolate_eval steps hs G (Nat.lt_succ_of_le gd) 0]
  apply Finset.sum_congr rfl
  intro j _
  simp only [G, eval_prod, digit_sample v hv nodes hn _ _ _ (hnz j)]
  rw [Fintype.prod_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.prod_mul_distrib, Finset.prod_comm (s := univ) (t := range k)]
  ring

#print axioms exact_decomposition
end PackedRiffle
