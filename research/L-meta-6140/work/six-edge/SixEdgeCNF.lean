import Mathlib.Tactic
import Std.Sat.CNF.Sat

namespace SixEdge.CNFEncoding

open Std.Sat

abbrev Lit := Std.Sat.Literal ℕ

def holds (a : ℕ → Bool) (lit : Lit) : Prop := a lit.1 = lit.2

def flip (lit : Lit) : Lit := (lit.1, !lit.2)

theorem flip_holds (a : ℕ → Bool) (lit : Lit) : holds a (flip lit) ↔ ¬ holds a lit := by
  rcases lit with ⟨v, bit⟩
  cases bit <;> cases h : a v <;> simp [holds, flip, h]

def clause (terms : List Lit) : CNF.Clause ℕ := .ofLiterals terms

theorem clause_holds (a : ℕ → Bool) (terms : List Lit) :
    (clause terms).Sat a ↔ ∃ lit ∈ terms, holds a lit := by
  simp only [CNF.Clause.sat_iff_exists_mem_eq, ← CNF.Clause.mem_literals_iff,
    clause, CNF.Clause.literals_ofLiterals, holds]

/-- Clauses for an auxiliary literal equal to the disjunction of its inputs.
The clause order is the one used by the replay encoder. -/
def disjunction (out : Lit) (terms : List Lit) : List (CNF.Clause ℕ) :=
  clause (flip out :: terms) :: terms.map (fun t => clause [flip t, out])

theorem disjunction_holds (a : ℕ → Bool) (out : Lit) (terms : List Lit) :
    (∀ c ∈ disjunction out terms, c.Sat a) ↔
      (holds a out ↔ ∃ t ∈ terms, holds a t) := by
  classical
  constructor
  · intro ok
    constructor
    · intro outTrue
      obtain ⟨lit, mem, yes⟩ := (clause_holds a (flip out :: terms)).mp
        (ok (clause (flip out :: terms)) (List.mem_cons_self))
      rcases List.mem_cons.mp mem with eq | inTerms
      · subst lit
        exact ((flip_holds _ _).mp yes outTrue).elim
      · exact ⟨lit, inTerms, yes⟩
    · rintro ⟨t, mem, yes⟩
      have tc : clause [flip t, out] ∈ disjunction out terms := by
        exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_, mem, rfl⟩)
      obtain ⟨lit, mem, fire⟩ := (clause_holds a _).mp (ok _ tc)
      rcases List.mem_cons.mp mem with eq | last
      · subst lit
        exact ((flip_holds _ _).mp fire yes).elim
      · rw [List.mem_singleton.mp last] at fire
        exact fire
  · intro compare c hm
    rcases List.mem_cons.mp hm with eq | rest
    · subst c
      apply (clause_holds a _).mpr
      by_cases outTrue : holds a out
      · obtain ⟨t, mem, yes⟩ := compare.mp outTrue
        exact ⟨t, List.mem_cons_of_mem _ mem, yes⟩
      · exact ⟨flip out, List.mem_cons_self, (flip_holds _ _).mpr outTrue⟩
    · obtain ⟨t, mem, eq⟩ := List.mem_map.mp rest
      subst c
      apply (clause_holds a _).mpr
      by_cases tTrue : holds a t
      · exact ⟨out, by simp, compare.mpr ⟨t, mem, tTrue⟩⟩
      · exact ⟨flip t, List.mem_cons_self, (flip_holds _ _).mpr tTrue⟩

/-- The encoder's conjunction uses De Morgan's law and the same OR clauses. -/
theorem conjunction_holds (a : ℕ → Bool) (out : Lit) (terms : List Lit) :
    (∀ c ∈ disjunction (flip out) (terms.map flip), c.Sat a) ↔
      (holds a out ↔ ∀ t ∈ terms, holds a t) := by
  classical
  rw [disjunction_holds, flip_holds]
  have deMorgan : (∃ t ∈ terms.map flip, holds a t) ↔ ¬ ∀ t ∈ terms, holds a t := by
    simp only [List.mem_map, exists_exists_and_eq_and, flip_holds]
    push Not
    rfl
  rw [deMorgan, not_iff_not]

theorem implication_clause (a : ℕ → Bool) (select : Lit) (choices : List Lit) :
    (clause (flip select :: choices)).Sat a ↔
      (holds a select → ∃ lit ∈ choices, holds a lit) := by
  classical
  simp only [clause_holds, List.mem_cons, or_and_right, exists_or,
    exists_eq_left, flip_holds]
  tauto

/-- Defining a fresh disjunction variable extends a satisfying assignment
    and leaves every earlier clause satisfied. -/
theorem extend_disjunction (formula : CNF ℕ) (a : ℕ → Bool) (out : ℕ) (terms : List Lit)
    (freshFormula : ¬ formula.VarMem out) (freshTerms : ∀ t ∈ terms, t.1 ≠ out)
    (sat : formula.Sat a) :
    ∃ b : ℕ → Bool, (∀ v ≠ out, b v = a v) ∧ formula.Sat b ∧
      ∀ c ∈ disjunction (out,true) terms, c.Sat b := by
  classical
  let bit := decide (∃ t ∈ terms, holds a t)
  let b := Function.update a out bit
  have same (v : ℕ) (neq : v ≠ out) : b v = a v := Function.update_of_ne neq _ _
  refine ⟨b, same, ?_, (disjunction_holds b _ _).mpr ?_⟩
  · have eq := CNF.eval_congr b a formula
        (fun v hv => same v (fun e => freshFormula (e ▸ hv)))
    exact eq.trans sat
  · have h : b out = bit := Function.update_self _ _ _
    constructor
    · intro yes
      have on : bit = true := h.symm.trans yes
      obtain ⟨t, mem, fire⟩ := of_decide_eq_true on
      exact ⟨t, mem, (same _ (freshTerms t mem)).trans fire⟩
    · rintro ⟨t, mem, fire⟩
      have old : holds a t := (same _ (freshTerms t mem)).symm.trans fire
      exact h.trans (decide_eq_true ⟨t, mem, old⟩)

/-- Each column of the encoder's counter says whether at least that many
inputs are true. The rows use an OR and an AND for the inductive step. -/
def threshold : List Bool → ℕ → Bool
  | _, 0 => true
  | [], _+1 => false
  | bit :: rest, k+1 => threshold rest (k+1) || (bit && threshold rest k)

theorem threshold_spec (bits : List Bool) (k : ℕ) :
    threshold bits k = true ↔ k ≤ bits.count true := by
  induction bits generalizing k with
  | nil => cases k <;> simp [threshold]
  | cons bit rest ih =>
    cases k with
    | zero => simp [threshold]
    | succ k =>
      cases bit <;> simp [threshold, ih]
      omega

theorem exact_count (bits : List Bool) (k : ℕ) :
    threshold bits k = true ∧ threshold bits (k+1) = false ↔ bits.count true = k := by
  rw [threshold_spec]
  have off : threshold bits (k+1) = false ↔ ¬ k+1 ≤ bits.count true := by
    rw [Bool.eq_false_iff]
    exact not_congr (threshold_spec _ _)
  rw [off]
  omega

#print axioms disjunction_holds
#print axioms conjunction_holds

end SixEdge.CNFEncoding
