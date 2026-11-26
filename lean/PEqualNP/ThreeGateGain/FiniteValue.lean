import Mathlib.Data.BitVec

namespace GainFinite

/-- A set bit in 0,1 reuses gate zero at gate one's left, right arms.
    Bits 2,3 and 4,5 select the two earlier gates for gate two's arms.
    Bits 6,7,8 select gate outputs for the final free union. -/
def threeValue (w : BitVec 9) (x : BitVec 6) : Bool :=
  let first := x.getLsbD 0 && x.getLsbD 1
  let second := (x.getLsbD 2 || (w.getLsbD 0 && first)) &&
    (x.getLsbD 3 || (w.getLsbD 1 && first))
  let third := (x.getLsbD 4 || (w.getLsbD 2 && first) || (w.getLsbD 3 && second)) &&
    (x.getLsbD 5 || (w.getLsbD 4 && first) || (w.getLsbD 5 && second))
  (w.getLsbD 6 && first) || (w.getLsbD 7 && second) || (w.getLsbD 8 && third)

end GainFinite
