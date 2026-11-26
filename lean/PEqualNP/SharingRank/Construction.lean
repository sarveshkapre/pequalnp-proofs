import PEqualNP.SharingRank.Formula
import PEqualNP.SharingRank.FamilyRank

namespace SharingRank.Family
open Formulas Set

def pull {X Y : Type} (f : X → Y) : Expr Y Y → Expr X X
  | .rect r c => .rect (f ⁻¹' r) (f ⁻¹' c)
  | .meet a b => .meet (pull f a) (pull f b)
  | .join a b => .join (pull f a) (pull f b)

@[simp] theorem pull_cost {X Y : Type} (f : X → Y) (e : Expr Y Y) :
    (pull f e).cost = e.cost := by induction e <;> simp_all [pull,Expr.cost]

@[simp] theorem pull_cell {X Y : Type} (f : X → Y) (e : Expr Y Y) (x y : X) :
    (pull f e).cell x y ↔ e.cell (f x) (f y) := by induction e <;> simp_all [pull,Expr.cell]

private def bitset (i : Nat) : Set Four := {x | x.val.testBit i = true}
private def onePair : Expr Four Four := .join (.rect (bitset 0) (bitset 0)) (.rect (bitset 1) (bitset 1))
@[simp] private theorem pair_cell (x y : Four) : onePair.cell x y ↔ someBit x y = true := by
  simp [onePair,bitset,Expr.cell,someBit,firstBit,otherBit]

private def allOr : (d : Nat) → Expr (Words d) (Words d)
  | 0 => .rect univ univ
  | d+1 => .meet (pull Prod.fst onePair) (pull Prod.snd (allOr d))
@[simp] private theorem allOr_cost (d : Nat) : (allOr d).cost = d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change (pull (Prod.fst : Four × Words d → Four) onePair).cost +
      (pull (Prod.snd : Four × Words d → Words d) (allOr d)).cost = _
    rw [pull_cost,pull_cost,ih]
    change 1 + d = d + 1
    omega
@[simp] private theorem allOr_cell (d : Nat) (x y : Words d) :
    (allOr d).cell x y ↔ allPairs someBit d x y = true := by
  induction d with
  | zero => simp [allOr,Expr.cell,allPairs]
  | succ d ih =>
    obtain ⟨a,x⟩ := x
    obtain ⟨b,y⟩ := y
    change (pull (Prod.fst : Four × Words d → Four) onePair).cell (a,x) (b,y) ∧
      (pull (Prod.snd : Four × Words d → Words d) (allOr d)).cell (a,x) (b,y) ↔ _
    simp [pull_cell,pair_cell,allPairs,ih]

private theorem first_factor (d : Nat) (x y : Words d) :
    allPairs firstBit d x y = true ↔ allPairs firstBit d x x = true ∧ allPairs firstBit d y y = true := by
  induction d with
  | zero => simp [allPairs]
  | succ d ih =>
    simp only [allPairs,Bool.and_eq_true,firstBit,Bool.and_self]
    have tail := ih x.2 y.2
    tauto

def explicitFormula (d : Nat) : Expr (Four × Words d) (Four × Words d) :=
  let r := {x : Four × Words d | allPairs firstBit d x.2 x.2 = true}
  .join (.rect r r) (.meet (pull Prod.fst onePair) (pull Prod.snd (allOr d)))

theorem explicit_cost (d : Nat) : (explicitFormula d).cost = d+2 := by
  simp [explicitFormula,onePair,Expr.cost,Nat.add_comm,Nat.add_left_comm]

theorem explicit_cell (d : Nat) (x y : Four × Words d) :
    (explicitFormula d).cell x y ↔ cell d x y = true := by
  simp only [explicitFormula,Expr.cell,Set.mem_setOf_eq,pull_cell,pair_cell,allOr_cell,
    cell,Bool.or_eq_true,Bool.and_eq_true]
  rw [← first_factor]
end SharingRank.Family
