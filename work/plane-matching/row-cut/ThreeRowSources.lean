import ThreeRowData

namespace ThreeRowSources

def rows := [29,225,1793,294,586,1170]
def hints := [3,40,1064,272,336,516,644,48,560,264,392,68,1092]
def bits (n m : Nat) := (List.range n).filter m.testBit
def active (s : Nat) := (bits 6 s).map (fun r => rows.getD r 0)
def lineUnion (s : Nat) := (active s).foldl (· ||| ·) 0
def shared (s : Nat) := ((bits 11 (lineUnion s)).filter fun l =>
    ((active s).filter (fun r => r.testBit l)).length ≥ 2).foldl (fun v l => v ||| 2^l) 0
def subsets (r : Nat) := (bits 11 r).foldl (fun xs l => xs ++ xs.map (fun v => v ||| 2^l)) [0]
def sources (s : Nat) :=
  let fixedRows := ((List.range 6).filter fun r => !s.testBit r).map (fun r => rows.getD r 0)
  let rawLines := (List.range 11).map fun l => 2^l
  ((rawLines ++ hints ++ fixedRows.flatMap subsets).map (· &&& lineUnion s)).eraseDups

abbrev Test := Nat × Nat × Nat -- active point, positive line index, negative line mask
def valid (s : Nat) (t : Test) :=
  let (r,l,m) := t
  r < 6 && l < 11 && s.testBit r && (rows.getD r 0).testBit l &&
    (m &&& lineUnion s == m) && (m &&& rows.getD r 0 == 0) &&
    (rows ++ hints).all (fun q => (bits 11 (m &&& q)).length ≤ 2)
def separates (v : Nat) (t : Test) := v.testBit t.2.1 && (v &&& t.2.2 == 0)

def checkFamily (s omitted : Nat) (ts : List Test) :=
  let core := shared s
  let bank := sources s
  let count := fun v => (ts.filter (separates v)).length
  ts.all (valid s) &&
    if omitted == 0 then
      ts.length == 6 && bank.all fun v => count v ≤ (if v &&& core == 0 then 1 else 0)
    else
      (ts.length == 12 || ts.length == 1) &&
        bank.all fun v => v == omitted || count v ≤ (if ts.length == 1 then 0 else 1)

def shapeOK (s : Nat) :=
  let core := shared s
  let a := active s
  let kept := lineUnion s
  a.all (fun r => (bits 11 r).length == 4) &&
    if (bits 11 core).length == 1 then
      (bits 11 kept).length == 10 && a.all (fun r => r &&& core == core) &&
      (sources s).all (fun v => a.all (fun r => (bits 11 (r &&& v)).length ≤ 1))
    else
      (bits 11 core).length == 3 && a.all (fun r => (bits 11 (r &&& core)).length == 2) &&
      (bits 11 core).all (fun l => (a.filter (fun r => r.testBit l)).length == 2) &&
      (sources s).all (fun v => (bits 11 (v &&& core)).length ≤ 1)

def expectedKeys := ((List.range 64).filter (fun s => (bits 6 s).length == 3)).flatMap fun s =>
  if (bits 11 (shared s)).length == 1 then (bits 11 (lineUnion s)).map (fun l => (s, 2^l))
  else [(s,0)]

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem allGeometry : ((List.range 64).filter (fun s => (bits 6 s).length == 3)).all shapeOK = true := by
  decide +kernel

theorem coversAllChoices :
    expectedKeys.length = 38 ∧ gridSourceData.length = 38 ∧
    expectedKeys.all (fun k => gridSourceData.any (fun z => (z.1, z.2.1) == k)) = true := by
  decide +kernel

theorem allComparisons : gridSourceData.all (fun z => checkFamily z.1 z.2.1 z.2.2) = true := by
  decide +kernel

#print axioms allGeometry
#print axioms coversAllChoices
#print axioms allComparisons
end ThreeRowSources
