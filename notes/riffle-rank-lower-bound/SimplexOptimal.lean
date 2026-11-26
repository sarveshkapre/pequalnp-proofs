import ThreeLinear
import Mathlib.Data.Fin.Tuple.Basic

open Finset
open scoped BigOperators
namespace RiffleLower

private abbrev Word (j : ℕ) := Fin j → Bool

private def entry {j : ℕ} (F : Type) [Field F] (s : Word j) (a : Fin j) : F :=
  if s a then 1 else 0

/-- Turning on one bit of a subset adds that coordinate over every field. -/
private theorem edge_difference {F : Type} [Field F] {j : ℕ}
    (b a : Fin (j+1)) (v : Word j) :
    entry F (b.insertNth true v) a - entry F (b.insertNth false v) a =
      if a = b then 1 else 0 := by
  induction a using b.succAboveCases <;> simp [entry, Fin.succAbove_ne]

/-- t copies of the nonzero Boolean columns, with one disjoint recovery
for each copy and each Boolean word on the coordinates other than b. -/
theorem simplex_upper (F : Type) [Field F] (j t : ℕ) :
    Dictionary F (t*(2^(j+1)-1)) (j+1) (t*2^j) := by
  classical
  let S := (univ : Finset (Word (j+1))).erase (fun _ => false)
  let slots := Fin t × ↥S
  let labels := Fin t × Word j
  have sc : S.card = 2^(j+1)-1 := by simp [S]
  let index : Fin (t*(2^(j+1)-1)) ≃ slots :=
    (Fintype.equivFinOfCardEq (by simp [slots, sc])).symm
  let label : Fin (t*2^j) ≃ labels :=
    (Fintype.equivFinOfCardEq (by simp [labels])).symm
  let insert (b : Fin (j+1)) (flag : Bool) (p : labels) : Fin t × Word (j+1) :=
    (p.1, b.insertNth flag p.2)
  let readLabel (b : Fin (j+1)) (s : Fin t × Word (j+1)) : labels :=
    (s.1, b.removeNth s.2)
  have label_insert b flag p : readLabel b (insert b flag p) = p := by
    simp [readLabel,insert]
  let incl (s : slots) : Fin t × Word (j+1) := (s.1,s.2)
  let coef (b : Fin (j+1)) (p : labels) (s : Fin t × Word (j+1)) : F :=
    (if s = insert b true p then 1 else 0) - (if s = insert b false p then 1 else 0)
  let out (b : Fin (j+1)) (s : Fin t × Word (j+1)) (p : labels) : F :=
    if readLabel b s = p then 1 else 0
  refine ⟨fun i a => entry F (index i).2 a,
    fun b c i => coef b (label c) (incl (index i)),
    fun b i d => out b (incl (index i)) (label d), ?_⟩
  intro a b c d
  let f (s : Fin t × Word (j+1)) := coef b (label c) s * entry F s.2 a * out b s (label d)
  have all : ∑ s : slots, f (incl s) = ∑ s, f s := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    apply sum_congr rfl; intro u _
    change (∑ s : ↥S, f (u, (s : Word (j+1)))) = _
    rw [Finset.sum_coe_sort S (fun v => f (u,v))]
    simp [S, f, entry]
  have sample (flag : Bool) :
      (∑ s : Fin t × Word (j+1), (if s = insert b flag (label c) then (1:F) else 0) *
        entry F s.2 a * out b s (label d)) =
      entry F (b.insertNth flag (label c).2) a * (if c = d then 1 else 0) := by
    rw [sum_eq_single (insert b flag (label c))]
    · simp only [ite_true, one_mul, out, label_insert, label.injective.eq_iff]
      rfl
    · intro s _ hs; simp [hs]
    · simp
  calc
    _ = ∑ s : slots, f (incl s) := index.sum_comp (fun s => f (incl s))
    _ = ∑ s, f s := all
    _ = _ := by
      simp only [f,coef,sub_mul,sum_sub_distrib]
      rw [sample,sample,← sub_mul,edge_difference]
      by_cases hab : a = b <;> by_cases hcd : c = d <;> simp [hab,hcd]

/-- Exact optimality of the simplex dictionary, allowing arbitrary coefficients
and overlapping rank-one decoders. The output dimension is a multiple of 2^j. -/
theorem simplex_optimal (F : Type) [Field F] (j t : ℕ) :
    Dictionary F (t*(2^(j+1)-1)) (j+1) (t*2^j) ∧
    ∀ r, Dictionary F r (j+1) (t*2^j) → t*(2^(j+1)-1) ≤ r := by
  refine ⟨simplex_upper F j t, ?_⟩
  intro r h
  have bound := rectangular_dyadic h
  have hp : 0 < 2^j := by positivity
  rw [Nat.mul_div_cancel _ hp] at bound
  rw [pow_succ, Nat.mul_sub, Nat.mul_one, ← Nat.mul_assoc]
  omega

#print axioms simplex_upper
#print axioms simplex_optimal
end RiffleLower
