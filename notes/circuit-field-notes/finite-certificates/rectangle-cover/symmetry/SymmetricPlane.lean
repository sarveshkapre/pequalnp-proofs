import Std

namespace Desk9348.SymmetricPlane

-- The two parts of an Edge are disjoint two-subsets of a five-element set.
-- Such two-subsets are adjacent vertices of the Petersen graph.
inductive Label where
  | absolute (bit : Nat)
  | pole
  | edge (first second : Nat)
  deriving DecidableEq, BEq, Inhabited

def allowed : Label → Label → Bool
  | .pole, .absolute _ | .absolute _, .pole => false
  | .pole, _ | _, .pole => true
  | .absolute x, .absolute y => x != y
  | .absolute x, .edge a b | .edge a b, .absolute x => (x &&& (a ||| b)) != 0
  | .edge a b, .edge c d =>
    (a == c && b == d) || (a != c && a != d && b != c && b != d)

def rows : List Nat := [1179809, 262467, 524934, 1049868, 2585, 5170, 10340,
  20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778,
  102405, 204810, 409620, 819240, 1638480]

def column (i : Fin 21) : Fin 21 :=
  (#[2, 3, 7, 0, 8, 14, 17, 1, 9, 4, 13, 19, 11, 15, 10, 12, 20, 6, 5, 18, 16] : Array (Fin 21))[i.val]!

def point (i : Fin 21) : Label :=
  (#[.edge 10 20, .edge 6 17, .absolute 1, .edge 10 17,
    .edge 12 17, .edge 3 24, .edge 9 20, .edge 6 24,
    .edge 12 18, .edge 3 12, .edge 9 18, .pole,
    .absolute 2, .edge 5 18, .absolute 4, .edge 5 24,
    .edge 5 10, .edge 6 9, .edge 3 20, .absolute 8,
    .absolute 16] : Array Label)[i.val]!

def twoSubsets : List Nat := [3, 5, 6, 9, 10, 12, 17, 18, 20, 24]
def labels : List Label := [.pole] ++ ([1, 2, 4, 8, 16].map .absolute) ++
  twoSubsets.flatMap fun a =>
    (twoSubsets.filter fun b => a < b && (a &&& b) == 0).map (.edge a)

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem bijective_labels :
    (List.ofFn point).Nodup ∧ labels.Nodup ∧ labels.length = 21 ∧
    (labels.all fun x => (List.ofFn point).contains x) = true := by decide +kernel

theorem bijective_columns : (List.ofFn column).Nodup := by decide +kernel

theorem match_desk : ∀ i j : Fin 21,
    allowed (point i) (point j) = !((rows.getD i.val 0).testBit (column j).val) := by
  decide +kernel

-- If only one rectangle is unmatched, the cells still required occur in
-- transpose pairs. The square on the intersection of its sides covers both.
theorem one_unmatched {α : Type} (target covered : α → α → Prop) (a b : α → Prop)
    (ht : ∀ i j, target i j → target j i)
    (hc : ∀ i j, covered i j → covered j i)
    (finish : ∀ i j, target i j → covered i j ∨ (a i ∧ b j)) :
    ∀ i j, target i j → covered i j ∨ ((a i ∧ b i) ∧ (a j ∧ b j)) := by
  intro i j hij
  rcases finish i j hij with h | ⟨ai, bj⟩
  · exact Or.inl h
  · rcases finish j i (ht i j hij) with h | ⟨aj, bi⟩
    · exact Or.inl (hc j i h)
    · exact Or.inr ⟨⟨ai, bi⟩, ⟨aj, bj⟩⟩


def covers (boxes : List (Nat × Nat)) (i j : Fin 21) : Bool :=
  boxes.any fun b => b.1.testBit i.val && b.2.testBit j.val

def transposeClosed (boxes : List (Nat × Nat)) : Bool :=
  boxes.all fun b => boxes.any fun c => (List.finRange 21).all fun i =>
    (b.1.testBit i.val == c.2.testBit (column i).val) &&
    (c.1.testBit i.val == b.2.testBit (column i).val)

def fourteen : List (Nat × Nat) :=
  [(141361, 573764), (1282640, 263296), (282722, 1147528),
   (1049260, 436225), (537672, 82067), (1122566, 150568),
   (21904, 1376294), (198274, 1574928), (72192, 1056858),
   (540676, 1251664), (1608210, 143364), (33857, 856344),
   (428296, 528993), (1900673, 12034)]

def fifteen : List (Nat × Nat) :=
  [(21904, 1376294), (33793, 864540), (72192, 1056858),
   (282722, 1147528), (537672, 82067), (540676, 1251664),
   (1900673, 12034), (1609235, 12292), (198274, 1574928),
   (1122566, 150568), (1049260, 436225), (1282640, 263296),
   (141361, 573764), (428296, 528993), (34896, 659712)]

theorem fourteen_witness :
    fourteen.length = 14 ∧ transposeClosed fourteen = true ∧
    ∀ i j : Fin 21, covers fourteen i j =
      (!(rows.getD i.val 0).testBit j.val &&
        !((i.val == 6 && j.val == 17) || (i.val == 10 && j.val == 13))) := by
  decide +kernel

theorem fifteen_witness :
    fifteen.length = 15 ∧ transposeClosed fifteen = true ∧
    ∀ i j : Fin 21, covers fifteen i j = !(rows.getD i.val 0).testBit j.val := by
  decide +kernel

#print axioms fourteen_witness
#print axioms fifteen_witness
#print axioms match_desk
#print axioms bijective_labels
#print axioms bijective_columns
#print axioms one_unmatched

end Desk9348.SymmetricPlane
