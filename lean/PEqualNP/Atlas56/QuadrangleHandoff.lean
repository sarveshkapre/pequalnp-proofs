import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Fin

namespace QuadrangleHandoff

abbrev Cell := Fin 6 × Fin 6

-- Duplicate row A in position 5 to fit the square grid used in L-gct-233.
def mask (r : Nat) := ([49, 42, 22, 13, 3] : List Nat).getD r 0
def graph : Finset Cell :=
  Finset.univ.filter fun p => (mask (p.1.val % 5)).testBit p.2.val

-- The circuit premises of L-gct-233, specialized to N = 6.
def Represents (k : Nat) (G : Finset Cell) : Prop :=
  ∃ (I : Fin (k+1) → Finset Cell)
    (A B : Fin (k+1) → Fin 2 → Finset (Fin 6))
    (S : Fin (k+1) → Fin 2 → Finset (Fin (k+1))),
    (∀ t e, ∀ r ∈ S t e, r < t) ∧
    (∀ t, t ≠ Fin.last k → ∀ p : Cell, p ∈ I t ↔ ∀ e : Fin 2,
      (p.1 ∈ A t e ∨ p.2 ∈ B t e ∨ ∃ r ∈ S t e, p ∈ I r)) ∧
    (∀ p : Cell, p ∈ I (Fin.last k) ↔
      (p.1 ∈ A (Fin.last k) 0 ∨ p.2 ∈ B (Fin.last k) 0 ∨
        ∃ r ∈ S (Fin.last k) 0, p ∈ I r)) ∧ I (Fin.last k) = G

-- Gate 0 intersects clauses 0 and 1. Gates 1, 2, 3 each append one clause.
-- Index 4 is the final free union and selects the output of gate 3.
def rawClause (t : Fin 5) (e : Fin 2) : Option Nat :=
  if t.val = 4 then none else if e.val = 1 then some (t.val+1)
  else if t.val = 0 then some 0 else none
def a (t : Fin 5) (e : Fin 2) : Finset (Fin 6) :=
  match rawClause t e with
  | none => ∅
  | some r => Finset.univ.filter fun i => i.val % 5 ≠ r
def b (t : Fin 5) (e : Fin 2) : Finset (Fin 6) :=
  match rawClause t e with
  | none => ∅
  | some r => Finset.univ.filter fun j => (mask r).testBit j.val
def s (t : Fin 5) (e : Fin 2) : Finset (Fin 5) :=
  Finset.univ.filter fun r => e.val = 0 ∧ r.val+1 = t.val
def wires (t : Fin 5) : Finset Cell :=
  Finset.univ.filter fun p => p.1.val % 5 > t.val+1 ∨ (mask (p.1.val % 5)).testBit p.2.val

set_option maxRecDepth 10000 in
theorem four : Represents 4 graph := by
  refine ⟨wires, a, b, s, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

#print axioms four
end QuadrangleHandoff
