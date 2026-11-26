import PEqualNP.ThreeGateGain.FiniteCatalogue
import PEqualNP.ThreeGateGain.GainGeometry
import PEqualNP.ThreeGateGain.TriangleTrim

namespace GainTrim
open GainFinite GainGeometry TriangleOptimality Finset Configuration
open scoped Classical

private theorem monoAnd {a b c d : Bool} (ha : a = true → c = true) (hb : b = true → d = true) :
    (a && b) = true → (c && d) = true := by simp only [Bool.and_eq_true]; tauto

private theorem monoOr {a b c d : Bool} (ha : a = true → c = true) (hb : b = true → d = true) :
    (a || b) = true → (c || d) = true := by simp only [Bool.or_eq_true]; tauto

private theorem compare_word (w x y : BitVec 6) (k : BitVec 9)
    (h : ∀ i, w.getLsbD i = true → (x ||| y).getLsbD i = true) :
    threeValue k w = true → threeValue k (x ||| y) = true := by
  unfold threeValue
  dsimp only
  repeat first | exact h _ | exact id | apply monoAnd | apply monoOr

variable {P L : Type*} [Fintype P] [Fintype L] [Membership P L] [ProjectivePlane P L]

theorem score_errors (Q : P → L → Prop) :
    score (fun p l => p ∈ l) Q univ univ =
      (Fintype.card P : ℤ) * (ProjectivePlane.order P L + 1) -
      errors (fun p l => p ∈ l) {x : P × L | ¬ Q x.1 x.2} := by
  classical
  let G (p:P) (l:L) := p∈l
  have cell (p:P) (l:L) : weight G Q p l =
      hit G p l - hit (fun a b => ¬ (¬ (a,b) ∈ ({x : P × L | ¬ Q x.1 x.2} : Set _) ↔ G a b)) p l := by
    by_cases g : G p l <;> by_cases z : Q p l <;> simp [weight,signedCell,hit,g,z]
  change score G Q _ _ = _ - errors G _
  simp only [score,cell,errors,sum_sub_distrib]
  simp only [G,row_total,sum_const,card_univ,nsmul_eq_mul]

/-- Remove the complete stars paid for by a raw output or an intrinsically
true input word, then take a positive core in the actual finite host. -/
theorem normalize (w : BitVec 9) (r : P → BitVec 6) (c : L → BitVec 6)
    (rawP : P → Bool) (rawL : L → Bool) (hq : 3 ≤ ProjectivePlane.order P L) :
    let Q := fun p l => (rawP p || rawL l || threeValue w (r p ||| c l)) = true
    let H := fun p l => hostEdge (scalarHost (wiringScalar w)) (wordType (wiringScalar w) (r p))
      (wordType (wiringScalar w) (c l)) = true
    ∃ A : Finset P, ∃ B : Finset L,
      score (fun p l => p∈l) Q univ univ ≤ score (fun p l => p∈l) H A B ∧
      (∀ p ∈ A, 0 < ∑ l ∈ B, weight (fun p l => p∈l) H p l) ∧
      (∀ l ∈ B, 0 < ∑ p ∈ A, weight (fun p l => p∈l) H p l) := by
  classical
  intro Q H
  let G (p:P) (l:L) := p∈l
  let X := univ.filter (fun p => rawP p = true ∨ threeValue w (r p) = true)
  let Y := univ.filter (fun l => rawL l = true ∨ threeValue w (c l) = true)
  let A := univ \ X
  let B := univ \ Y
  let z : Set (P × L) := {u | ¬ Q u.1 u.2}
  have full (p:P) (l:L) (h : p∈X ∨ l∈Y) : (p,l) ∉ z := by
    suffices Q p l by simpa [z]
    change (rawP p || rawL l || threeValue w (r p ||| c l)) = true
    simp only [X,Y,mem_filter,mem_univ,true_and] at h
    simp only [Bool.or_eq_true]
    rcases h with (hp|hp)|(hl|hl)
    · tauto
    · right; exact compare_word _ _ _ _ (fun i hi => by simp [BitVec.getLsbD_or,hi]) hp
    · tauto
    · right; exact compare_word _ _ _ _ (fun i hi => by simp [BitVec.getLsbD_or,hi]) hl
  have eq (p:P) (l:L) (hp : p∈A) (hl : l∈B) : Q p l ↔ H p l := by
    simp only [A,B,mem_sdiff,mem_univ,true_and,X,Y,mem_filter,not_or] at hp hl
    dsimp [Q,H]
    rw [← trimmed_host]
    simp_all
  let Q' := fun p l => p ∈ A ∧ l ∈ B ∧ H p l
  have sets : z ∪ {u : P × L | u.1 ∈ X ∨ u.2 ∈ Y} = {u | ¬ Q' u.1 u.2} := by
    ext u
    rcases u with ⟨p,l⟩
    change (¬Q p l ∨ p ∈ X ∨ l ∈ Y) ↔ ¬ Q' p l
    by_cases e : p∈A <;> by_cases f : l∈B
    · have same := eq p l e f
      simp [A,B] at e f
      simp [Q',A,B,e,f,same]
    all_goals simp [A,B] at e f; simp [Q',A,B,e,f]
  have trimmed := trim_full_stars X Y z hq full
  dsimp only at trimmed
  rw [sets] at trimmed
  have bound : score G Q univ univ ≤ score G Q' univ univ := by
    rw [score_errors,score_errors]; exact sub_le_sub_left trimmed _
  have reduced : score G Q' univ univ = score G H A B := by
    have cell (p:P) (l:L) : weight G Q' p l =
        if p∈A then (if l∈B then weight G H p l else 0) else 0 := by
      by_cases a : p∈A <;> by_cases b : l∈B <;> simp [weight,Q',a,b]
    have row (p:P) : (∑ l : L, weight G Q' p l) =
        if p∈A then (∑ l ∈ B, weight G H p l) else 0 := by
      by_cases a : p ∈ A
      · simp only [cell,ite_eq_left a,← sum_filter]; simp
      · simp [cell,a]
    simp only [score,row,← sum_filter]
    simp
  obtain ⟨S,_,T,_,leq,hs,ht⟩ := positive_core G H A B
  exact ⟨S,T,(bound.trans_eq reduced).trans leq,hs,ht⟩

#print axioms normalize
end GainTrim
