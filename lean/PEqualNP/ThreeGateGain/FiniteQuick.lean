import PEqualNP.ThreeGateGain.FiniteFrame

namespace GainFinite

def activeMask (h : Host) : Nat :=
  #[0, 6, 126, 510, 32766, 524286, 0, 0, 2097150, 0, 134217726, 0, 33554430, 0, 0, 0][h.val]!

def remaining (h : Host) (blocked : Leaves) : Nat :=
  size27 (activeMask h &&& ((2^27-1) ^^^ unionMask h blocked))

def quickFrame (h : Host) (rl cl : Leaves) : Bool :=
  let t := rl.length + cl.length
  decide (t ≤ 10) && (
    decide (17*t + 3*(remaining h cl + remaining h rl) ≤ 158) ||
    (let live := liveRows h rl cl
     decide (17*t + 3*(live.length + size27 (live.foldr (· ||| ·) 0)) ≤ 158)) ||
    testFrame h rl cl)

def quickCols (h : Host) (rl : Leaves) : Bool :=
  visit (eligible h) (quickFrame h rl) [] (available h rl)

def quickHost (h : Host) : Bool :=
  visit (eligible h) (quickCols h) [] allTypes

end GainFinite
