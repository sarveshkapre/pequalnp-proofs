import PEqualNP.Quadrangle.Bridge
namespace PEqualNP.Quadrangle.Encoding
open PEqualNP.Library.LRAT

/-- The clauses are emitted in the order used by check_obstruction.py. -/
inductive Rule where
  | both (z x y : Nat)
  | anyOf (z : Nat) (xs : List Nat)
  | requireBit (z : Nat) (b : Bool)

def positive (v : Nat) := 2 * v
def negative (v : Nat) := 2 * v + 1

def Rule.clauses : Rule → List (List Nat)
  | .both z x y => [[negative x,negative y,positive z],
      [positive x,negative z],[positive y,negative z]]
  | .anyOf z xs => (xs.map positive ++ [negative z]) :: xs.map (fun x => [negative x,positive z])
  | .requireBit z b => [[if b then positive z else negative z]]

def Rule.wellFormed (f : Nat → Role) : Rule → Bool
  | .both z x y => (f z).andInputs == some (f x, f y)
  | .anyOf z xs => (f z).orInputs == some (xs.map f)
  | .requireBit z b => (f z).outputBit == some b

noncomputable def assignment (m : Model) (f : Nat → Role) (v : Nat) : Bool :=
  @decide (holds m (f v)) (Classical.propDecidable _)

private theorem pos_true (m : Model) (f : Nat → Role) (v : Nat) :
    litVal (assignment m f) (positive v) = true ↔ holds m (f v) := by
  classical
  have hd : (2*v)/2 = v := by omega
  have hr : (2*v)%2 = 0 := by omega
  unfold litVal positive
  rw [hd, hr]
  change decide (holds m (f v)) = true ↔ _
  exact decide_eq_true_iff

private theorem neg_true (m : Model) (f : Nat → Role) (v : Nat) :
    litVal (assignment m f) (negative v) = true ↔ ¬holds m (f v) := by
  have hd : (2*v+1)/2 = v := by omega
  have hr : (2*v+1)%2 = 1 := by omega
  classical
  unfold litVal negative
  rw [hd, hr]
  change (decide (holds m (f v)) == false) = true ↔ _
  simp

private theorem cons_sat (a : Nat → Bool) (x : Nat) (xs : List Nat) :
    ClauseSat a (x :: xs) ↔ litVal a x = true ∨ ClauseSat a xs := by
  simp [ClauseSat]

private theorem nil_sat (a : Nat → Bool) : ¬ClauseSat a [] := by simp [ClauseSat]

private theorem append_sat (a : Nat → Bool) (xs ys : List Nat) :
    ClauseSat a (xs ++ ys) ↔ ClauseSat a xs ∨ ClauseSat a ys := by
  simp [ClauseSat, exists_or, or_and_right]

private theorem pos_list (m : Model) (f : Nat → Role) (xs : List Nat) :
    ClauseSat (assignment m f) (xs.map positive) ↔ ∃ v ∈ xs, holds m (f v) := by
  induction xs with
  | nil => simp [nil_sat]
  | cons x xs ih => simp [cons_sat, pos_true, ih]

theorem rule_sound (m : Model) (f : Nat → Role) (g : Rule) (h : g.wellFormed f = true) :
    ∀ c ∈ g.clauses, ClauseSat (assignment m f) c := by
  cases g with
  | both z x y =>
    have eq := and_meaning m (beq_iff_eq.mp h)
    simp [Rule.clauses, cons_sat, nil_sat, pos_true, neg_true]
    tauto
  | anyOf z xs =>
    have eq := or_meaning m (beq_iff_eq.mp h)
    have eq' : holds m (f z) ↔ ∃ x ∈ xs, holds m (f x) := by simpa using eq
    simp [Rule.clauses, append_sat, cons_sat, nil_sat, pos_true, neg_true, pos_list]
    grind
  | requireBit z b =>
    have eq := output_meaning m (beq_iff_eq.mp h)
    cases b <;> simp_all [Rule.clauses, cons_sat, nil_sat, pos_true, neg_true]

end PEqualNP.Quadrangle.Encoding
