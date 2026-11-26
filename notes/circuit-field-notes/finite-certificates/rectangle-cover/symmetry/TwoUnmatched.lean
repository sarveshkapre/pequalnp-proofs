import Std

namespace Desk9348.TwoUnmatched

variable {α : Type} (a b c d : α → Prop)

def box (s t : α → Prop) (i j : α) : Prop := s i ∧ t j

def both (s t : α → Prop) (i : α) : Prop := s i ∧ t i

def either (s t : α → Prop) (i : α) : Prop := s i ∨ t i

def shadow (x y u v : α → Prop) (i j : α) : Prop :=
  box x x i j ∨ box y y i j ∨ box u v i j ∨ box v u i j

-- Exact contribution to a symmetric remainder, including diagonal cells.
theorem symmetric_part (i j : α) :
    ((box a b i j ∨ box c d i j) ∧ (box a b j i ∨ box c d j i)) ↔
      shadow (both a b) (both c d) (both a d) (both b c) i j := by
  dsimp [shadow, box, both]
  grind

variable (x y u v : α → Prop) (ok : α → α → Prop)
def legal (ok : α → α → Prop) (s t : α → Prop) : Prop :=
  ∀ i j, box s t i j → ok i j

theorem constraints (symm : ∀ i j, ok i j → ok j i)
    (hab : legal ok a b) (hcd : legal ok c d) :
    let x := both a b
    let y := both c d
    let u := both a d
    let v := both b c
    legal ok x x ∧ legal ok y y ∧ legal ok u v ∧ legal ok (either x y) (either u v) := by
  dsimp [both, either, legal, box] at *
  grind

-- Two actual rectangles implement the shadow. They may cover extra legal cells.
theorem restore (symm : ∀ i j, ok i j → ok j i)
    (hx : legal ok x x) (hy : legal ok y y) (huv : legal ok u v)
    (cross : legal ok (either x y) (either u v)) :
    legal ok (either x u) (either x v) ∧ legal ok (either y v) (either y u) ∧
      ∀ i j, shadow x y u v i j →
        box (either x u) (either x v) i j ∨ box (either y v) (either y u) i j := by
  dsimp [legal, box, either, shadow] at *
  grind

-- With a legal combined square the shadow costs only two symmetric rectangles.
theorem merge_squares (symm : ∀ i j, ok i j → ok j i)
    (hw : legal ok (either x y) (either x y)) (huv : legal ok u v)
    (cross : legal ok (either x y) (either u v)) :
    let w := either x y
    legal ok (either w u) (either w v) ∧ legal ok (either w v) (either w u) ∧
      ∀ i j, shadow x y u v i j →
        box (either w u) (either w v) i j ∨ box (either w v) (either w u) i j := by
  dsimp [legal, either, box, shadow] at *
  grind

theorem merge_cut (symm : ∀ i j, ok i j → ok j i)
    (hx : legal ok x x) (hy : legal ok y y) (hz : legal ok (either u v) (either u v))
    (cross : legal ok (either x y) (either u v)) :
    let z := either u v
    legal ok (either x z) (either x z) ∧ legal ok (either y z) (either y z) ∧
      ∀ i j, shadow x y u v i j →
        box (either x z) (either x z) i j ∨ box (either y z) (either y z) i j := by
  dsimp [legal, either, box, shadow] at *
  grind

#print axioms symmetric_part
#print axioms constraints
#print axioms restore
#print axioms merge_squares
#print axioms merge_cut

end Desk9348.TwoUnmatched
