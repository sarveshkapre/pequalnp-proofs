import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace PlaneCut

abbrev Bits := BitVec 4
abbrev Part := Fin 15

/-- The fifteen partitions of four labelled lines, represented by their nonempty blocks. -/
def blocks (p : Part) : List Bits :=
  ([[1,2,4,8],[3,4,8],[5,2,8],[9,2,4],[6,1,8],[10,1,4],[12,1,2],
    [3,12],[5,10],[9,6],[7,8],[11,4],[13,2],[14,1],[15]] : List (List Bits)).getD p.val []
def cost (p : Part) := 4 - (blocks p).length
def fits (p : Part) (v : Bits) := (blocks p).any fun s => v &&& s == v
def extendsP (p q : Part) := (blocks p).all (fits q)
def tiny (v : Bits) := ([0,1,2,4,8] : List Bits).contains v

theorem initial : cost 0 = 0 := rfl
theorem tiny_fits : ∀ (p : Part) (v : Bits), tiny v → fits p v := by decide
theorem preserves : ∀ (p q : Part) (v : Bits), extendsP p q → fits p v → fits q v := by decide
theorem and_left : ∀ (p : Part) (a b : Bits), fits p a → fits p (a &&& b) := by decide
theorem and_right (p : Part) (a b : Bits) (hb : fits p b) : fits p (a &&& b) := by
  rw [BitVec.and_comm]
  exact and_left p b a hb
set_option maxRecDepth 10000 in
theorem merge : ∀ (p : Part) (a b : Bits), fits p a → fits p b →
    ∃ q : Part, extendsP p q = true ∧ fits q (a ||| b) = true ∧ cost q ≤ cost p + 1 := by decide

/-- A row's four singleton-line values, and its value with every outside line high. -/
structure View where
  bits : Bits
  outside : Bool

def combine (andGate : Bool) (a b : View) : View :=
  if andGate then ⟨a.bits &&& b.bits, a.outside && b.outside⟩
  else ⟨a.bits ||| b.bits, a.outside || b.outside⟩
def good (p : Part) (v : View) := v.outside = false → fits p v.bits = true
def charge (andGate : Bool) (v : View) : Bool := !andGate && !v.outside && !tiny v.bits

/-- A safe AND inherits a block from a safe operand. A safe OR can join at most two blocks. -/
theorem advance {p : Part} {a b : View} (op : Bool) (ha : good p a) (hb : good p b) :
    ∃ q, (∀ v, good p v → good q v) ∧ good q (combine op a b) ∧
      cost q ≤ cost p + (charge op (combine op a b)).toNat := by
  cases op with
  | true =>
    refine ⟨p,fun _ h => h,?_,by simp [charge]⟩
    intro h
    change (a.outside && b.outside) = false at h
    change fits p (a.bits &&& b.bits) = true
    cases ea : a.outside
    · exact and_left p _ _ (ha ea)
    · exact and_right p _ _ (hb (by simpa [ea] using h))
  | false =>
    by_cases dirty : (combine false a b).outside = true
    · exact ⟨p,fun _ h => h,fun h => by simp [dirty] at h,by omega⟩
    by_cases small : tiny (a.bits ||| b.bits) = true
    · exact ⟨p,fun _ h => h,fun _ => tiny_fits p _ small,by omega⟩
    have outside : (a.outside || b.outside) = false := by
      change ¬ (a.outside || b.outside) = true at dirty
      simpa using dirty
    obtain ⟨la,lb⟩ := Bool.or_eq_false_iff.mp outside
    obtain ⟨q,le,fitsNew,step⟩ := merge p _ _ (ha la) (hb lb)
    exact ⟨q,fun v h neg => preserves p q _ le (h neg),fun _ => fitsNew,
      by simpa [combine,charge,outside,small] using step⟩

#print axioms advance
end PlaneCut
