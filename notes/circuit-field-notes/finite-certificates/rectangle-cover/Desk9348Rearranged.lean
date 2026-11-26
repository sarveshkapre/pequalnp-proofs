import PEqualNP.Defs

namespace PEqualNP.Outside.Desk9348Rearranged

def rows : List Nat := [1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405, 204810, 409620, 819240, 1638480]

def rectangles : List (Nat × Nat) := [
  (141361, 573764),
  (1282640, 263296),
  (282722, 1147528),
  (1049260, 436225),
  (537672, 82067),
  (1122566, 150568),
  (1608210, 143364),
  (428296, 528993),
  (1900673, 12034),
  (1154, 1648692),
  (737796, 1050704),
  (50245, 332056),
  (20752, 1376358),
  (68160, 1703962)]

def covers (i j : Fin 21) : Bool :=
  rectangles.any fun p => p.1.testBit i.val && p.2.testBit j.val

end PEqualNP.Outside.Desk9348Rearranged

theorem PEqualNP.Outside.Desk9348Rearranged :
    PEqualNP.Outside.Desk9348Rearranged.rectangles.length = 14 ∧
    ∀ i j : Fin 21,
       PEqualNP.Outside.Desk9348Rearranged.covers i j =
        (!((PEqualNP.Outside.Desk9348Rearranged.rows.getD i.val 0).testBit j.val) &&
          !(((i.val == 12) && (j.val == 13)) || ((i.val == 14) && (j.val == 17)))) := by
  decide +kernel
