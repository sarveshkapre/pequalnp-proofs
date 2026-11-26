import PEqualNP.Quadrangle.Handoff
import PEqualNP.Library.LRAT.Checker
import Mathlib.Tactic.FinCases

namespace PEqualNP.Quadrangle.Encoding
open QuadrangleHandoff PEqualNP.Library.LRAT

/-- Selectors and wire values of a hypothetical original representation.
All six rows and arbitrary reuse of previous intersections are retained. -/
structure Model where
  I : Fin 4 → Finset Cell
  A : Fin 4 → Fin 2 → Finset (Fin 6)
  B : Fin 4 → Fin 2 → Finset (Fin 6)
  S : Fin 4 → Fin 2 → Finset (Fin 4)
  earlier : ∀ t e k, k ∈ S t e → k < t
  gate : ∀ t, t ≠ Fin.last 3 → ∀ p : Cell, p ∈ I t ↔ ∀ e : Fin 2,
    p.1 ∈ A t e ∨ p.2 ∈ B t e ∨ ∃ k ∈ S t e, p ∈ I k
  output : ∀ p : Cell, p ∈ I (Fin.last 3) ↔
    p.1 ∈ A (Fin.last 3) 0 ∨ p.2 ∈ B (Fin.last 3) 0 ∨ ∃ k ∈ S (Fin.last 3) 0, p ∈ I k
  correct : I (Fin.last 3) = graph

inductive Role where
  | empty
  | row (t : Fin 4) (e : Fin 2) (i : Fin 6)
  | col (t : Fin 4) (e : Fin 2) (j : Fin 6)
  | sel (t : Fin 4) (e : Fin 2) (k : Fin 4)
  | hit (t : Fin 4) (e : Fin 2) (k : Fin 4) (i j : Fin 6)
  | side (t : Fin 4) (e : Fin 2) (i j : Fin 6)
  | wire (t : Fin 4) (i j : Fin 6)
  deriving DecidableEq, Inhabited

def holds (m : Model) : Role → Prop
  | .empty => False
  | .row t e i => i ∈ m.A t e
  | .col t e j => j ∈ m.B t e
  | .sel t e k => k ∈ m.S t e
  | .hit t e k i j => k ∈ m.S t e ∧ (i,j) ∈ m.I k
  | .side t e i j => i ∈ m.A t e ∨ j ∈ m.B t e ∨ ∃ k ∈ m.S t e, (i,j) ∈ m.I k
  | .wire t i j => (i,j) ∈ m.I t

def Role.andInputs : Role → Option (Role × Role)
  | .hit t e k i j => some (.sel t e k, .wire k i j)
  | .wire t i j => if t = Fin.last 3 then none else some (.side t 0 i j, .side t 1 i j)
  | _ => none

def Role.orInputs : Role → Option (List Role)
  | .side t e i j => some (.row t e i :: .col t e j ::
      (((List.finRange 4).filter (· < t)).map fun k => .hit t e k i j))
  | _ => none

def Role.outputBit : Role → Option Bool
  | .side t e i j => if t = Fin.last 3 ∧ e = 0 then some (decide ((i,j) ∈ graph)) else none
  | _ => none

theorem and_meaning (m : Model) {r x y : Role}
    (h : r.andInputs = some (x,y)) : holds m r ↔ holds m x ∧ holds m y := by
  cases r <;> simp [Role.andInputs] at h
  case hit t e k i j =>
    obtain ⟨rfl, rfl⟩ := h
    rfl
  case wire t i j =>
    obtain ⟨ht, rfl, rfl⟩ := h
    change (i,j) ∈ m.I t ↔ _
    rw [m.gate t ht]
    constructor
    · intro hh
      exact ⟨hh 0, hh 1⟩
    · rintro ⟨h₀, h₁⟩ e
      fin_cases e <;> assumption

theorem or_meaning (m : Model) {r : Role} {xs : List Role}
    (h : r.orInputs = some xs) : holds m r ↔ ∃ x ∈ xs, holds m x := by
  cases r <;> simp [Role.orInputs] at h
  case side t e i j =>
    subst xs
    simp [holds, List.mem_cons, List.mem_map, List.mem_filter]
    grind [m.earlier]

theorem output_meaning (m : Model) {r : Role} {b : Bool}
    (h : r.outputBit = some b) : holds m r ↔ b = true := by
  cases r <;> simp [Role.outputBit] at h
  case side t e i j =>
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    have out := m.output (i,j)
    rw [m.correct] at out
    simpa [holds] using out.symm

end PEqualNP.Quadrangle.Encoding
