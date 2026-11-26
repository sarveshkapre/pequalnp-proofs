import MatchProjected
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace MatchProjected

def portOK (c : Cross) (s : Selector) : Bool := s.direct || allowed c s.raw

def testRow (c : Cross) (h : Fin 4 → Wire) (p : TopSel) (r : Raw) : Bool :=
  !(independent c r) || !(topVal p h r)

def topTest (c : Cross) (h : Fin 4 → Wire) (p : TopSel) (pos : Raw) : Bool :=
  allowed c p.leaf && leafOK c p.center p.leaf && topVal p h pos &&
  testRow c h p 7 && testRow c h p 14 && testRow c h p 21 &&
  testRow c h p 28 && testRow c h p 35 && testRow c h p 42 &&
  testRow c h p 49 && testRow c h p 56 && testRow c h p 10 && testRow c h p 17

def window (c : Cross) (o : Fin 4 → Bool) (s t : Fin 4 → Selector) (ts : Fin 3 → TopSel) : Bool :=
  let h := schedule o s t
  graphOK c &&
  portOK c (s 0) && portOK c (t 0) && portOK c (s 1) && portOK c (t 1) &&
  portOK c (s 2) && portOK c (t 2) && portOK c (s 3) && portOK c (t 3) &&
  topTest c h (ts 0) (positive 0) && topTest c h (ts 1) (positive 1) &&
  topTest c h (ts 2) (positive 2)

theorem Realizes.window_true {c o s t ts} (p : Realizes c o s t ts) : window c o s t ts = true := by
  have l (i : Fin 4) : portOK c (s i) = true := by
    cases hx : (s i).direct <;> simp [portOK,hx,p.left i]
  have r (i : Fin 4) : portOK c (t i) = true := by
    cases hx : (t i).direct <;> simp [portOK,hx,p.right i]
  have quiet (i : Fin 3) (v : Raw) : testRow c (schedule o s t) (ts i) v = true := by
    cases hv : independent c v <;> simp [testRow,hv,p.rejects i v]
  have accepts (i : Fin 3) : topTest c (schedule o s t) (ts i) (positive i) = true := by
    simp only [topTest,p.leaf,p.center,p.accepts,quiet,Bool.and_self]
  simp only [window,p.graph,l,r,accepts,Bool.and_self]

theorem lookup4 {α : Type} (a b c d : α) (i : Fin 4) :
    ![a,b,c,d] i = if (decide (i = 0)) then a else if (decide (i = 1)) then b else
      if (decide (i = 2)) then c else d := by fin_cases i <;> rfl

theorem portRaw (s : Selector) (h : Fin 4 → Wire) :
    (port s h).raw = if s.direct then (h s.idx).raw else s.raw := by
  cases k : s.direct <;> simp [port,k]
theorem portNz (s : Selector) (h : Fin 4 → Wire) :
    (port s h).nz = if s.direct then (h s.idx).nz else true := by
  cases k : s.direct <;> simp [port,k]
theorem portVal (s : Selector) (h : Fin 4 → Wire) (r : Raw) :
    (port s h).val r = if s.direct then (h s.idx).val r else side s.raw s.take h r := by
  cases k : s.direct <;> simp [port,k]
theorem rawIte (q : Bool) (x y : Wire) :
    (if q then x else y).raw = if q then x.raw else y.raw := by cases q <;> rfl
theorem valIte (q : Bool) (x y : Wire) (r : Raw) :
    (if q then x else y).val r = if q then x.val r else y.val r := by cases q <;> rfl
theorem nzIte (q : Bool) (x y : Wire) :
    (if q then x else y).nz = if q then x.nz else y.nz := by cases q <;> rfl
theorem bitIte {w : Nat} (q : Bool) (x y : BitVec w) (i : Nat) :
    (if q then x else y).getLsbD i = if q then x.getLsbD i else y.getLsbD i := by cases q <;> rfl

theorem beq6 (x y : Raw) :
    (x == y) = ((x.getLsbD 0 == y.getLsbD 0) && (x.getLsbD 1 == y.getLsbD 1) &&
      (x.getLsbD 2 == y.getLsbD 2) && (x.getLsbD 3 == y.getLsbD 3) &&
      (x.getLsbD 4 == y.getLsbD 4) && (x.getLsbD 5 == y.getLsbD 5)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,Bool.and_eq_true]
  constructor
  · rintro rfl; simp
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    rcases this with rfl|rfl|rfl|rfl|rfl|rfl <;> simp_all

end MatchProjected
