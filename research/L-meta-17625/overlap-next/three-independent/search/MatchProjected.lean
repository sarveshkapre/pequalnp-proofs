import Std.Tactic.BVDecide
import Mathlib.Data.Fin.VecNotation

namespace MatchProjected

abbrev Raw := BitVec 6
abbrev Cross := BitVec 4

structure Wire where
  raw : Raw
  nz : Bool
  val : Raw → Bool

def zero : Wire := ⟨0, false, fun _ => false⟩

structure Selector where
  raw : Raw
  take : BitVec 4
  direct : Bool
  idx : Fin 4

structure TopSel where
  center : Raw
  leaf : Raw
  ctake : BitVec 4
  ltake : BitVec 4

def subset (a b : Raw) : Bool := (a &&& ~~~b) == 0
def hit (a b : Raw) : Bool := (a &&& b) != 0

/-- Codes 0,...,3 denote L2-R0, L2-R1, L0-R2 and L1-R2. -/
def graphOK (c : Cross) : Bool :=
  !(c.getLsbD 0 && c.getLsbD 2) && !(c.getLsbD 1 && c.getLsbD 3)

def allowed (c : Cross) (a : Raw) : Bool :=
  (subset a 7 || subset a 56) &&
  (!(c.getLsbD 0 || c.getLsbD 2) || !(subset 5 a || subset 40 a)) &&
  (!(c.getLsbD 1 || c.getLsbD 3) || !(subset 6 a || subset 48 a))

def positive (i : Fin 3) : Raw := ![9,18,36] i

def independent (c : Cross) (v : Raw) : Bool :=
  !(subset 9 v || subset 18 v || subset 36 v ||
    (c.getLsbD 0 && subset 12 v) || (c.getLsbD 1 && subset 20 v) ||
    (c.getLsbD 2 && subset 33 v) || (c.getLsbD 3 && subset 34 v))

def leafOK (c : Cross) (z m : Raw) : Bool :=
  (z == 0) ||
  ((z == 4) && subset m ((if c.getLsbD 0 then 8 else 0) ||| (if c.getLsbD 1 then 16 else 0))) ||
  ((z == 32) && subset m ((if c.getLsbD 2 then 1 else 0) ||| (if c.getLsbD 3 then 2 else 0)))

def included (raw : Raw) (select : Bool) (w : Wire) (v : Raw) : Bool :=
  select && w.nz && subset w.raw raw && w.val v

def side (raw : Raw) (take : BitVec 4) (h : Fin 4 → Wire) (v : Raw) : Bool :=
  hit raw v || included raw (take.getLsbD 0) (h 0) v ||
    included raw (take.getLsbD 1) (h 1) v ||
    included raw (take.getLsbD 2) (h 2) v ||
    included raw (take.getLsbD 3) (h 3) v

def port (s : Selector) (h : Fin 4 → Wire) : Wire :=
  if s.direct then h s.idx else ⟨s.raw, true, side s.raw s.take h⟩

def gate (isOr : Bool) (a b : Wire) : Wire :=
  if isOr then ⟨a.raw ||| b.raw, a.nz || b.nz, fun v => a.val v || b.val v⟩
  else ⟨0, false, fun v => a.val v && b.val v⟩

def extend (isOr : Bool) (s t : Selector) (h : Fin 4 → Wire) : Wire :=
  gate isOr (port s h) (port t h)

def schedule (o : Fin 4 → Bool) (s t : Fin 4 → Selector) : Fin 4 → Wire :=
  let a := extend (o 0) (s 0) (t 0) (fun _ => zero)
  let b := extend (o 1) (s 1) (t 1) ![a,zero,zero,zero]
  let d := extend (o 2) (s 2) (t 2) ![a,b,zero,zero]
  let e := extend (o 3) (s 3) (t 3) ![a,b,d,zero]
  ![a,b,d,e]

def topVal (top : TopSel) (h : Fin 4 → Wire) (r : Raw) : Bool :=
  side top.center top.ctake h r && side top.leaf top.ltake h r

/-- Any physical realization maps to one of these schedules. Direct operands
can select a future slot; such slots currently hold the identically zero wire. -/
structure Realizes (c : Cross) (o : Fin 4 → Bool) (s t : Fin 4 → Selector)
    (tops : Fin 3 → TopSel) : Prop where
  graph : graphOK c = true
  operations : (List.ofFn o).count true = 2
  left : ∀ i, (s i).direct = false → allowed c (s i).raw = true
  right : ∀ i, (t i).direct = false → allowed c (t i).raw = true
  leaf : ∀ i, allowed c (tops i).leaf = true
  center : ∀ i, leafOK c (tops i).center (tops i).leaf = true
  accepts : ∀ i, topVal (tops i) (schedule o s t) (positive i) = true
  rejects : ∀ i v, independent c v = true → topVal (tops i) (schedule o s t) v = false

end MatchProjected
