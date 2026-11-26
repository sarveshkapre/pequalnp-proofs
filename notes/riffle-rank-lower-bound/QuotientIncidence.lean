import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

open Finset
open scoped BigOperators
namespace RiffleQuotients

/-- Counts on every coordinate subspace determine the multiplicity of every exact support. -/
theorem support_counts_unique {I : Type} [DecidableEq I] (f g : Finset I → ℕ)
    (h : ∀ S : Finset I, ∑ T ∈ S.powerset, f T = ∑ T ∈ S.powerset, g T) :
    ∀ S, f S = g S := by
  intro S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    have sub : ∑ T ∈ S.powerset.erase S, f T = ∑ T ∈ S.powerset.erase S, g T := by
      apply sum_congr rfl; intro T hT
      obtain ⟨hne, hin⟩ := mem_erase.mp hT
      exact ih T (ssubset_of_subset_of_ne (mem_powerset.mp hin) hne)
    have mf := sum_erase_add (s := S.powerset) f (mem_powerset_self S)
    have mg := sum_erase_add (s := S.powerset) g (mem_powerset_self S)
    have total := h S
    omega

/-- If the point on each support is projectively compatible with deleting one
coordinate, it is the restriction of the full-support point, up to scaling. -/
theorem compatible_supports {I F : Type} [Fintype I] [DecidableEq I] [Field F]
    (v : Finset I → I → F)
    (step : ∀ (S : Finset I) (b : I), b ∉ S → S.Nonempty →
      ∃ c : F, c ≠ 0 ∧ ∀ i ∈ S, v S i = c * v (insert b S) i) :
    ∀ S : Finset I, S.Nonempty → ∃ c : F, c ≠ 0 ∧ ∀ i ∈ S, v S i = c * v univ i := by
  classical
  have aux (m : ℕ) : ∀ S : Finset I, (univ \ S).card = m → S.Nonempty →
      ∃ c : F, c ≠ 0 ∧ ∀ i ∈ S, v S i = c * v univ i := by
    induction m with
    | zero =>
      intro S hc _
      have hu : S = univ := by
        apply eq_univ_of_forall; intro b
        by_contra hb
        have hm : b ∈ (univ \ S) := mem_sdiff.mpr ⟨mem_univ _, hb⟩
        rw [card_eq_zero.mp hc] at hm
        exact notMem_empty _ hm
      exact ⟨1,one_ne_zero,by simp [hu]⟩
    | succ m ih =>
      intro S hc hs
      obtain ⟨b,hb⟩ := Finset.card_pos.mp (show 0 < (univ \ S).card by omega)
      have hn := (mem_sdiff.mp hb).2
      have he : univ \ insert b S = (univ \ S).erase b := by ext; simp
      have hc' : (univ \ insert b S).card = m := by rw [he, card_erase_of_mem hb, hc]; omega
      obtain ⟨c,hc0,hc1⟩ := step S b hn hs
      obtain ⟨d,hd0,hd1⟩ := ih (insert b S) hc' (insert_nonempty _ _)
      refine ⟨c*d,mul_ne_zero hc0 hd0,?_⟩
      intro i hi; rw [hc1 i hi, hd1 i (mem_insert_of_mem hi), mul_assoc]
  intro S; exact aux _ S rfl

/-- The second point on a surviving target line identifies the two adjacent
support vectors projectively. The point T is given in the span of v(S) and e_b. -/
theorem cube_rigidity {I F : Type} [Fintype I] [DecidableEq I] [Field F]
    (v : Finset I → I → F) (supp : ∀ (S : Finset I) (i : I), v S i ≠ 0 ↔ i ∈ S)
    (mate : ∀ (S : Finset I) (b : I), b ∉ S → S.Nonempty →
      ∃ (T : Finset I) (l m : F), T.Nonempty ∧ T ≠ {b} ∧ T ≠ S ∧
        ∀ i, v T i = l * v S i + (if i = b then m else 0)) :
    ∀ S : Finset I, S.Nonempty → ∃ c : F, c ≠ 0 ∧ ∀ i ∈ S, v S i = c * v univ i := by
  classical
  apply compatible_supports
  intro S b hb hs
  obtain ⟨T,l,m,ht,htb,hts,eq⟩ := mate S b hb hs
  have hl : l ≠ 0 := by
    intro hz
    apply htb
    have sub : T ⊆ {b} := by
      intro i hi
      by_contra bad
      have hne : i ≠ b := by simpa using bad
      have hn := (supp T i).2 hi
      exact hn (by simp [eq i, hz, hne])
    exact ht.subset_singleton_iff.mp sub
  have hm : m ≠ 0 := by
    intro hz
    apply hts
    ext i; rw [← supp, ← supp, eq i]
    simp [hz,hl]
  have vsb : v S b = 0 := by simpa only [← supp,not_not] using hb
  have ht' : T = insert b S := by
    ext i
    by_cases h : i = b
    · subst i; simpa [← supp T b,eq b,vsb] using hm
    · rw [← supp T i, eq i]; simp [h,hl,supp]
  subst T
  refine ⟨l⁻¹,inv_ne_zero hl,?_⟩
  intro i hi
  have hib : i ≠ b := fun h => hb (h ▸ hi)
  rw [eq i,ite_eq_right hib,add_zero,← mul_assoc,inv_mul_cancel₀ hl,one_mul]

/-- Count incidences between all t-subsets and a uniform family of k-subsets. -/
theorem incidence_identity {I : Type} [Fintype I] [DecidableEq I]
    (blocks : Finset (Finset I)) (t k d : ℕ)
    (uniform : ∀ B ∈ blocks, B.card = k)
    (regular : ∀ A ∈ (univ : Finset I).powersetCard t,
      (blocks.filter (fun B => A ⊆ B)).card = d) :
    (Fintype.card I).choose t * d = blocks.card * k.choose t := by
  classical
  let pairs := (univ : Finset I).powersetCard t
  let rel (A B : Finset I) := A ⊆ B
  have left (A) (hA : A ∈ pairs) : (blocks.bipartiteAbove rel A).card = d := regular A hA
  have right (B) (hB : B ∈ blocks) : (pairs.bipartiteBelow rel B).card = k.choose t := by
    have eq : pairs.bipartiteBelow rel B = B.powersetCard t := by
      ext A; simp [pairs,rel,mem_powersetCard,and_comm]
    rw [eq,card_powersetCard,uniform B hB]
  have double := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := pairs) (t := blocks) rel
  calc
    _ = ∑ A ∈ pairs, d := by simp [pairs]
    _ = ∑ A ∈ pairs, (blocks.bipartiteAbove rel A).card :=
      sum_congr rfl fun A hA => (left A hA).symm
    _ = _ := double
    _ = ∑ _B ∈ blocks, k.choose t := sum_congr rfl fun B hB => right B hB
    _ = _ := by simp

/-- The last two column quotients cannot yield seven distinguished points per pair. -/
theorem no_65_triple_family (blocks : Finset (Finset (Fin 65)))
    (hsize : ∀ B ∈ blocks, B.card = 3)
    (hpair : ∀ A ∈ (univ : Finset (Fin 65)).powersetCard 2,
      (blocks.filter (fun B => A ⊆ B)).card = 7) : False := by
  have h := incidence_identity blocks 2 3 7 hsize hpair
  change 14560 = blocks.card * 3 at h
  omega

/-- Independent obstruction, counting all nine-element dependencies after six contractions. -/
theorem no_69_nine_family (blocks : Finset (Finset (Fin 69)))
    (hsize : ∀ B ∈ blocks, B.card = 9)
    (hsix : ∀ A ∈ (univ : Finset (Fin 69)).powersetCard 6,
      (blocks.filter (fun B => A ⊆ B)).card = 301) : False := by
  have h := incidence_identity blocks 6 9 301 hsize hsix
  have h6 : (Fintype.card (Fin 69)).choose 6 = 119877472 := by decide
  rw [h6] at h
  change 36083119072 = blocks.card * 84 at h
  omega

#print axioms support_counts_unique
#print axioms compatible_supports
#print axioms cube_rigidity
#print axioms no_65_triple_family
#print axioms no_69_nine_family
end RiffleQuotients
