import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace ChainHamming

variable {α : Type*} [DecidableEq α]

abbrev Row (α : Type*) := Finset α × Finset α

def falseNeg (r : Row α) : ℕ := (r.1 \ r.2).card
def falsePos (r : Row α) : ℕ := (r.2 \ r.1).card
def loss (xs : List (Row α)) : ℕ := (xs.map (fun r => falseNeg r + falsePos r)).sum

def firstPos : List (Row α) → ℕ
  | [] => 0
  | r :: _ => falsePos r

def Chain (gap : ℕ) : List (Row α) → Prop
  | a :: b :: t => a.2 ⊆ b.2 ∧ gap ≤ (a.1 \ b.1).card ∧ Chain gap (b :: t)
  | _ => True

theorem adjacent (a b : Row α) (h : a.2 ⊆ b.2) :
    (a.1 \ b.1).card ≤ falseNeg a + falsePos b := by
  have sub : a.1 \ b.1 ⊆ (a.1 \ a.2) ∪ (b.2 \ b.1) := by
    intro x hx
    obtain ⟨ha, hb⟩ := Finset.mem_sdiff.mp hx
    by_cases p : x ∈ a.2
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h p, hb⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ha, p⟩)
  exact (Finset.card_le_card sub).trans (Finset.card_union_le _ _)

theorem single_chain (gap : ℕ) : ∀ (xs : List (Row α)), Chain gap xs →
    firstPos xs + gap * xs.length ≤ loss xs + gap
  | [], _ => by simp [firstPos, loss]
  | [a], _ => by simp [firstPos, loss]
  | a :: b :: t, h => by
    obtain ⟨inc, sep, tail⟩ := h
    have edge := sep.trans (adjacent a b inc)
    have ih := single_chain gap (b :: t) tail
    change falsePos b + gap * (b :: t).length ≤ loss (b :: t) + gap at ih
    change falsePos a + gap * ((b :: t).length + 1) ≤
      (falseNeg a + falsePos a + loss (b :: t)) + gap
    rw [Nat.mul_succ]
    omega

theorem partition (gap : ℕ) (chains : List (List (Row α)))
    (h : ∀ xs ∈ chains, Chain gap xs) :
    gap * (chains.map List.length).sum ≤ (chains.map loss).sum + gap * chains.length := by
  induction chains with
  | nil => simp
  | cons xs tail ih =>
    have head := single_chain gap xs (h xs (by simp))
    have rest := ih (fun ys hy => h ys (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_succ]
    omega

#print axioms adjacent
#print axioms single_chain
#print axioms partition

end ChainHamming
