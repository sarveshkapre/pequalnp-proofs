import Init.Data.Nat.Bitwise.Lemmas
import Lean.Elab.Tactic.Decide

namespace FanoFiveUpper

abbrev Point := Fin 7
abbrev Line := Fin 7

/-- The labels 0 through 6 denote the nonzero binary vectors 1 through 7. -/
def incident (p : Point) (l : Line) : Bool :=
  let overlap := (p.val + 1) &&& (l.val + 1)
  !(xor (xor (overlap.testBit 0) (overlap.testBit 1)) (overlap.testBit 2))

/-- A free union of any selected point stars, line stars and earlier paid gates. -/
structure Arm (n : Nat) where
  pointMask : Nat
  lineMask : Nat
  earlier : List (Fin n)

def Arm.eval {R C : Nat} (a : Arm n) (p : Fin R) (l : Fin C) (old : Fin n → Bool) : Bool :=
  a.pointMask.testBit p.val || a.lineMask.testBit l.val || a.earlier.any old

/-- One constructor adds precisely one paid binary intersection. -/
inductive Circuit : Nat → Type where
  | empty : Circuit 0
  | gate : Circuit n → Arm n → Arm n → Circuit (n+1)

def Circuit.eval {R C : Nat} : {n : Nat} → Circuit n → Fin R → Fin C → Fin n → Bool
  | _, .empty, _, _, i => Fin.elim0 i
  | _, .gate prev a b, p, l, i =>
    let old := prev.eval p l
    Fin.lastCases (a.eval p l old && b.eval p l old) old i

def circuit : Circuit 5 :=
  let g₁ := Circuit.empty.gate ⟨32,20,[]⟩ ⟨66,99,[]⟩
  let g₂ := g₁.gate ⟨3,5,[]⟩ ⟨40,10,[]⟩
  let g₃ := g₂.gate ⟨4,3,[]⟩ ⟨10,76,[]⟩
  let g₄ := g₃.gate ⟨93,121,[]⟩ ⟨0,0,[0,1,2]⟩
  g₄.gate ⟨65,82,[0,1,2]⟩ ⟨16,32,[3]⟩

theorem verifies : ∀ p l, circuit.eval p l 4 = incident p l := by decide +kernel

theorem exists_five : ∃ c : Circuit 5, ∀ p l, c.eval p l 4 = incident p l :=
  ⟨circuit, verifies⟩

#print axioms FanoFiveUpper.verifies
#print axioms FanoFiveUpper.exists_five


def differenceIncident (p : Point) (l : Line) : Bool :=
  let d := (l.val + 7 - p.val) % 7
  d == 0 || d == 1 || d == 3

def pointLabel (i : Point) : Point := [0,1,3,4,6,2,5].getD i.val 0
def lineLabel (i : Line) : Line := [5,3,0,1,4,2,6].getD i.val 0

theorem labels_agree : ∀ p l, differenceIncident p l = incident (pointLabel p) (lineLabel l) :=
  by decide +kernel

/-- Pull a free star mask back from its binary-vector label to its difference-set label. -/
def reindexMask (perm : Fin 7 → Fin 7) (mask : Nat) : Nat :=
  (List.finRange 7).foldl (fun m i =>
    if mask.testBit (perm i).val then m ||| (1 <<< i.val) else m) 0

def Arm.reindex (a : Arm n) : Arm n :=
  ⟨reindexMask pointLabel a.pointMask, reindexMask lineLabel a.lineMask, a.earlier⟩

def Circuit.reindex : {n : Nat} → Circuit n → Circuit n
  | _, .empty => .empty
  | _, .gate prev a b => .gate prev.reindex a.reindex b.reindex

theorem exists_five_difference : ∃ c : Circuit 5, ∀ p l, c.eval p l 4 = differenceIncident p l :=
  ⟨circuit.reindex, by decide +kernel⟩

#print axioms FanoFiveUpper.exists_five_difference

end FanoFiveUpper
