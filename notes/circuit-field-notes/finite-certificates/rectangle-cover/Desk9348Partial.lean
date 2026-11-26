import PEqualNP.Defs

namespace PEqualNP.Outside.Desk9348Partial

def rows : List Nat := [1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405, 204810, 409620, 819240, 1638480]

def rectangles : List (Nat × Nat) := [
  (141361, 573764),
  (1282640, 263296),
  (282722, 1147528),
  (1049260, 436225),
  (537672, 82067),
  (1122566, 150568),
  (21904, 1376294),
  (198274, 1574928),
  (72192, 1056858),
  (540676, 1251664),
  (1608210, 143364),
  (33857, 856344),
  (428296, 528993),
  (1900673, 12034)]

def covers (i j : Fin 21) : Bool :=
  rectangles.any fun p => p.1.testBit i.val && p.2.testBit j.val

end PEqualNP.Outside.Desk9348Partial

theorem PEqualNP.Outside.Desk9348Partial :
    PEqualNP.Outside.Desk9348Partial.rectangles.length = 14 ∧
    ∀ i j : Fin 21,
       PEqualNP.Outside.Desk9348Partial.covers i j =
        (!((PEqualNP.Outside.Desk9348Partial.rows.getD i.val 0).testBit j.val) &&
          !(((i.val == 6) && (j.val == 17)) || ((i.val == 10) && (j.val == 13)))) := by
  decide +kernel
