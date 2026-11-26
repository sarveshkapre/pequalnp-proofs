import Std.Tactic.BVDecide

/-! Finite port-and-guard model. The ten assignment rows are
ab, bc, de, ce, bd, acd, be, ace, ad, ae. One bit per test row. -/
namespace DisjointProjected
abbrev T := BitVec 10
abbrev R := BitVec 5
abbrev P := BitVec 8

structure Wire where
  val : T
  raw : R
  nz : Bool

def rawMask (i : BitVec 4) : R :=
  if i == 1 then 1 else if i == 2 then 2 else if i == 3 then 4 else
  if i == 4 then 8 else if i == 5 then 16 else if i == 6 then 9 else
  if i == 7 then 12 else if i == 8 then 18 else 0

def literal (m : R) : T :=
  (if m.getLsbD 0 then 929 else 0) ||| (if m.getLsbD 1 then 83 else 0) |||
  (if m.getLsbD 2 then 170 else 0) ||| (if m.getLsbD 3 then 308 else 0) |||
  (if m.getLsbD 4 then 716 else 0)

def zero : Wire := ⟨0,0,false⟩
def gate (op : Bool) (l r : Wire) : Wire :=
  if op then ⟨l.val ||| r.val,l.raw ||| r.raw,l.nz || r.nz⟩ else ⟨l.val &&& r.val,0,false⟩

def includeOr (m : R) (yes : Bool) (g : Wire) : T :=
  if yes && g.nz && (g.raw &&& ~~~m == 0) then g.val else 0

def mux (b : Bool) (u v : Wire) : Wire :=
  ⟨if b then u.val else v.val, if b then u.raw else v.raw, if b then u.nz else v.nz⟩

def port (s : P) (u v w : Wire) : Wire :=
  let m := rawMask (s.extractLsb' 0 4)
  mux (s.getLsbD 7) (mux (s.getLsbD 0) u (mux (s.getLsbD 1) v w))
    ⟨literal m ||| includeOr m (s.getLsbD 4) u ||| includeOr m (s.getLsbD 5) v |||
      includeOr m (s.getLsbD 6) w,m,true⟩

/-- A top operand after the four charged gates. -/
def side (m : R) (sel : BitVec 4) (g h i j : Wire) : T :=
  literal m ||| includeOr m (sel.getLsbD 0) g ||| includeOr m (sel.getLsbD 1) h |||
    includeOr m (sel.getLsbD 2) i ||| includeOr m (sel.getLsbD 3) j

def outsideTop (inside : Bool) (neg : T) (s : BitVec 12) (g h i j : Wire) : T :=
  let center := side 0 (s.extractLsb' 0 4) g h i j
  let m := rawMask (s.extractLsb' 8 4)
  let leaf := side m (s.extractLsb' 4 4) g h i j
  let guarded := if inside then center &&& 848 == 0 else
    center &&& neg == 0 || m == 4 || m == 12
  if guarded then center &&& leaf else 0

def centerTop (cross : Bool) (s : BitVec 9) (g h i j : Wire) : T :=
  let m : R := if cross && s.getLsbD 8 then 16 else 0
  side 4 (s.extractLsb' 0 4) g h i j &&& side m (s.extractLsb' 4 4) g h i j

def realizes (inside cross op0 op1 op2 op3 : Bool) (p q r s t u v w : P)
    (top0 top1 : BitVec 12) (topC : BitVec 9) : Bool :=
  let g := gate op0 (port p zero zero zero) (port q zero zero zero)
  let h := gate op1 (port r g zero zero) (port s g zero zero)
  let i := gate op2 (port t g h zero) (port u g h zero)
  let j := gate op3 (port v g h i) (port w g h i)
  let neg : T := if cross then 880 else 1016
  let pos : T := if cross then 15 else 7
  let out := outsideTop inside neg top0 g h i j ||| outsideTop inside neg top1 g h i j |||
    (if inside then centerTop cross topC g h i j else 0)
  out &&& neg == 0 && out &&& pos == pos

end DisjointProjected
