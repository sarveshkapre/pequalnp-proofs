import SixEdgeCertificates

/-! Lean generation of the DIMACS inputs used by the certificate replay.
The trace identifies the primary variables, the OR definitions introducing
auxiliary variables, and the remaining clauses a circuit witness must satisfy. -/
namespace SixEdge.Formula

abbrev Lit := Int

inductive Input where
  | leaf (line point : Nat)
  | direct (gate operand prior : Nat)
  | atomMode (gate operand : Nat)
  | atom (gate operand vertex : Nat)
  | host (gate operand host : Nat)
  | promotion (gate operand prior : Nat)
  | topCentre (line prior : Nat)
  | topLeaf (line prior : Nat)
  deriving Repr, DecidableEq

inductive Rule where
  | nonemptyLeaf | residualCount | anchorResidual
  | portMode | nonemptyAtom | atomMode | hostMode | hostChoice | hostSupport
  | nontrivialHost | promotionMode | rawNonempty | rawSubset | portOrder
  | firstShape | firstActivity | canonicalOrder | centreExclusion
  | centreAnchor | centreMask | negativeTest | positiveTest | dirtyUsed
  deriving Repr, DecidableEq

inductive Event where
  | choice (index : Nat) (name : Input)
  | defineOr (index : Nat) (terms : List Lit)
  | require (rule : Rule) (terms : List Lit)
  deriving Repr

structure BuildState where
  variableCount : Nat := 1
  events : Array Event := #[]
  uses : Array (Array Lit) := #[]

abbrev Build := StateM BuildState

def normalizeClause (terms : List Lit) : Option (List Lit) :=
  let terms := (terms.filter (· != -1)).eraseDups
  if terms.contains 1 || terms.any (fun x => terms.contains (-x)) then none
  else some (terms.mergeSort (fun a b => a.natAbs ≤ b.natAbs))

def Event.rawClauses : Event → List (List Lit)
  | .choice .. => []
  | .defineOr i terms => (-(i : Int) :: terms) :: terms.map (fun t => [-t, i])
  | .require _ terms => [terms]

def BuildState.clauses (state : BuildState) : List (List Lit) :=
  [1] :: state.events.toList.flatMap (fun e => e.rawClauses.filterMap normalizeClause)

def require (rule : Rule) (terms : List Lit) : Build Unit :=
  modify fun s => {s with events := s.events.push (.require rule terms)}

def choose (name : Input) : Build Lit := do
  let i := (← get).variableCount + 1
  modify fun s => {s with variableCount := i, events := s.events.push (.choice i name)}
  pure i

def makeOr (terms : List Lit) : Build Lit := do
  if terms.contains 1 then return 1
  let terms := (terms.filter (· != -1)).eraseDups
  match terms with
  | [] => return -1
  | [x] => return x
  | _ =>
    let i := (← get).variableCount + 1
    modify fun s => {s with variableCount := i, events := s.events.push (.defineOr i terms)}
    return i

def makeAnd (terms : List Lit) : Build Lit := do
  return -(← makeOr (terms.map Neg.neg))

def pairs (xs : List α) : List (α × α) :=
  match xs with
  | [] => []
  | x :: rest => (rest.map (x, ·)) ++ pairs rest

def one (rule : Rule) (xs : List Lit) : Build Unit := do
  require rule xs
  (pairs xs).forM fun (i,j) => require rule [-i,-j]

def counterNext (row : List Lit) (x : Lit) : Build (List Lit) := do
  let rest ← (List.range 7).mapM fun i => do
    let added ← makeAnd [x,row[i]!]
    makeOr [row[i+1]!,added]
  pure (1 :: rest)

def exactSix (xs : List Lit) : Build Unit := do
  let row ← xs.foldlM counterNext [1, -1, -1, -1, -1, -1, -1, -1]
  require .residualCount [row[6]!]
  require .residualCount [-row[7]!]

def edgeRows : Array (Nat × Nat) := ((List.range 13).flatMap fun p =>
  [0,1,3,9].map fun d => (p,13+(p+13-d)%13)).toArray

def neighbours (line : Nat) : List Nat :=
  (List.range 13).filter fun p => edgeRows.contains (p,line)

def negativeMasks : Array Nat :=
  #[67100672,8191,25018369,50036738,32972804,65945608,64790544,62480416,
    57860160,48619648,30138624,60277248,53453824,39806976,12513280,16779133,
    4196831,33558266,69543,8393662,2102511,38867,1055351,23529,
    531771,15860,269981,139086,7405575,21757977,44564522,26222644,
    23199820,38830162,19939425,4309377,42041986,25363204,2434180,754946,
    16819536,17139201,38029448,616736,34753088,34352144,8695952,9064712,
    1857537,35676384,58982936,4335940,11669510,2659331,13140242,35783754,
    35194914,1509892,2379913,185152,59851296,53027872,12087328,1348113,
    924680,14942348,6324419,17318185,8462756,5515284,2274368,38406154,
    50479688,19137549,33851024,37759184,346753,9605634,22020181,4786435]

def samples : Array (List Nat) :=
  (edgeRows.map fun (p,l) => [p,l]) ++
  negativeMasks.map fun mask => (List.range 26).filter mask.testBit

abbrev Leaf := List (Nat × Lit)
def rawAt (leaf : Leaf) (v : Nat) : Lit := ((leaf.lookup v).getD (-1))

def modeInput (i b : Nat) : Nat → Input
  | 0 => .atomMode i b
  | j+1 => .direct i b j

def portHosts (leaves : Array Leaf) : Array Leaf :=
  ((List.range 26).map (fun v => [(v,(1 : Lit))])).toArray ++ leaves

structure Stage where
  dirty : Bool
  raw : Array Lit
  values : Array Lit
  ancestors : Array Lit
  operandModes : Fin 2 → List Lit
  deriving Inhabited

structure Port where
  modes : List Lit
  raw : Array Lit
  values : Array Lit
  ancestors : Array Lit

def recordUse (i : Nat) (r : Lit) : Build Unit :=
  modify fun s => {s with uses := s.uses.modify i (·.push r)}

def eligible (previous raw : Array Lit) (select : Lit) : Build Unit := do
  require .rawNonempty (-select :: previous.toList)
  (previous.toList.zip raw.toList).forM fun (old,new) =>
    require .rawSubset [-select,-old,new]

def checkPortHost (bank : Leaf) (j : Nat) (h : Lit) (atom : Array Lit) : Build Unit := do
  (List.range 26).forM fun v => require .hostSupport [-h,-atom[v]!,rawAt bank v]
  if 26 ≤ j then
    let pairs ← (pairs (bank.map Prod.fst)).mapM fun (u,v) => makeAnd [atom[u]!,atom[v]!]
    require .nontrivialHost (-h :: pairs)

def checkPortHosts (hosts : Array Leaf) (i b : Nat) (mode : Lit) (atom : Array Lit) : Build Unit := do
  require .nonemptyAtom (-mode :: atom.toList)
  atom.toList.forM fun w => require .atomMode [-w,mode]
  let host ← (List.range hosts.size).mapM fun j => choose (.host i b j)
  host.forM fun h => require .hostMode [-h,mode]
  require .hostChoice (-mode :: host)
  (pairs host).forM fun (h,k) => require .hostChoice [-h,-k]
  (List.range hosts.size).forM fun j => checkPortHost hosts[j]! j host[j]! atom

def promotionSlots (stages : Array Stage) : List Nat :=
  (List.range stages.size).filter fun j => !stages[j]!.dirty

def choosePromotion (stages : Array Stage) (i b j : Nat) (mode : Lit)
    (atom : Array Lit) : Build (Nat × Lit) := do
  let sel ← choose (.promotion i b j)
  require .promotionMode [-sel,mode]
  eligible stages[j]!.raw atom sel
  recordUse j sel
  pure (j,sel)

def gatedReads (reads : List (Nat × Lit)) (read : Nat → Lit) : Build (List Lit) :=
  reads.mapM fun (j,sel) => makeAnd [sel,read j]

def directReads (direct : Array Lit) : List (Nat × Lit) :=
  (List.range direct.size).map fun j => (j,direct[j]!)

def buildLitArray (size : Nat) (emit : Nat → Build Lit) : Build (Array Lit) := do
  let lits ← (List.range size).mapM emit
  pure lits.toArray

def portRaw (stages : Array Stage) (atom : Array Lit) (direct : List (Nat × Lit)) : Build (Array Lit) :=
  buildLitArray 26 fun v => do
    let terms ← gatedReads direct (fun j => stages[j]!.raw[v]!)
    makeOr (atom[v]! :: terms)

def portSamples (stages : Array Stage) (atom : Array Lit) (direct promoted : List (Nat × Lit)) :
    Build (Array Lit) :=
  buildLitArray samples.size fun k => do
    let promotedTerms ← gatedReads promoted (fun j => stages[j]!.values[k]!)
    let directTerms ← gatedReads direct (fun j => stages[j]!.values[k]!)
    makeOr ((samples[k]!).map (fun v => atom[v]!) ++ promotedTerms ++ directTerms)

def portAncestors (stages : Array Stage) (direct promoted : List (Nat × Lit))
    (canonical : Bool) : Build (Array Lit) :=
  if canonical then do
    let lits ← (List.range 5).mapM fun q => do
      let directTerms ← gatedReads direct (fun j => stages[j]!.ancestors[q]!)
      let promotedTerms ← gatedReads promoted (fun j => stages[j]!.ancestors[q]!)
      makeOr (directTerms ++ promotedTerms)
    pure lits.toArray
  else pure #[]

def buildPort (stages : Array Stage) (hosts : Array Leaf)
    (i b : Nat) (canonical : Bool) : Build Port := do
  let direct ← (List.range stages.size).mapM fun j => choose (.direct i b j)
  let direct := direct.toArray
  let reads := directReads direct
  reads.forM fun (j,sel) => recordUse j sel
  let mode ← choose (.atomMode i b)
  let modes := mode :: direct.toList
  one .portMode modes
  let atom ← (List.range 26).mapM fun v => choose (.atom i b v)
  let atom := atom.toArray
  checkPortHosts hosts i b mode atom
  let selected ← (promotionSlots stages).mapM fun j => choosePromotion stages i b j mode atom
  let raw ← portRaw stages atom reads
  let values ← portSamples stages atom reads selected
  let ancestors ← portAncestors stages reads selected canonical
  return ⟨modes,raw,values,ancestors⟩

def mode (r : Refinement) : Option Bool × Int × Bool :=
  match r with
  | .base => (none,-1,false)
  | .inactive => (some false,-1,false)
  | .canonicalInactive => (some false,-1,true)
  | .active => (some true,-1,true)
  | .points => (some true,0,true)
  | .centreLine => (some true,1,true)
  | .otherLine => (some true,2,true)

def firstBit (bits : BitVec 5) : Nat :=
  ((List.range 5).find? bits.getLsbD).getD 5

def declareLeaf (line : Nat) : Build Leaf :=
  (neighbours line).mapM fun p => do
    let bit ← choose (.leaf line p)
    pure (p,bit)

def checkLeaves (leaves : List Leaf) : Build Unit :=
  leaves.forM fun leaf => require .nonemptyLeaf (leaf.map Prod.snd)

def prepare (extra : BitVec 5) : Build (Array Leaf) := do
  let bank ← (List.range' 13 13).mapM declareLeaf
  checkLeaves bank
  let leaves := bank.toArray
  let retained := edgeRows.map fun (p,l) => rawAt leaves[l-13]! p
  exactSix ((retained.map Neg.neg).toList)
  if extra = 0 then require .anchorResidual [-retained[0]!]
  pure leaves

abbrev TopSelector := Nat × Lit × Lit

def topSlots (stages : Array Stage) (firstAnd : Nat) : List Nat :=
  (List.range 5).filter fun i => !stages[i]!.dirty && firstAnd < i

def topCentreRule (extra : BitVec 5) (line i : Nat) (select : Lit) : Build Unit :=
  if extra.getLsbD i then
    if i == firstBit extra && line == 13 then require .centreAnchor [select] else pure ()
  else require .centreMask [-select]

def selectTop (stages : Array Stage) (firstAnd : Nat) (extra : BitVec 5)
    (line : Nat) (leaf : Leaf) : Build (List TopSelector) :=
  (topSlots stages firstAnd).mapM fun i => do
    let z ← choose (.topCentre line i)
    let l ← choose (.topLeaf line i)
    recordUse i z
    recordUse i l
    eligible stages[i]!.raw ((Array.range 26).map fun v => if v == line then 1 else -1) z
    eligible stages[i]!.raw ((Array.range 26).map (rawAt leaf)) l
    topCentreRule extra line i z
    pure (i,z,l)

def topCentreLit (line : Nat) (selectors : List TopSelector) (read : Nat → Lit)
    (input : List Nat) : Build Lit :=
  if input.contains line then pure 1 else do
    let z ← selectors.mapM fun (i,s,_) => makeAnd [s,read i]
    makeOr z

def topHit (line : Nat) (leaf : Leaf) (selectors : List TopSelector)
    (read : Nat → Lit) (input : List Nat) : Build Lit := do
  let c ← topCentreLit line selectors read input
  let l ← selectors.mapM fun (i,_,s) => makeAnd [s,read i]
  let d ← makeOr (input.filterMap (fun n => leaf.lookup n) ++ l)
  makeAnd [c,d]

def lineHits (line : Nat) (leaf : Leaf) (selectors : List TopSelector)
    (stages : Array Stage) : Build (List Lit) :=
  (List.range samples.size).mapM fun k => do
    let hit ← topHit line leaf selectors (fun i => stages[i]!.values[k]!) samples[k]!
    if 52 ≤ k then require .negativeTest [-hit]
    pure hit

def positiveTests (hits : List (List Lit)) : Build Unit :=
  (List.range 52).forM fun k => require .positiveTest (hits.map fun row => row[k]!)

def collectLineTests (dirty extra : BitVec 5) (line : Nat) (leaf : Leaf) (stages : Array Stage) :
    Build (List TopSelector × List Lit) := do
  let selectors ← selectTop stages (firstBit dirty) extra line leaf
  let hits ← lineHits line leaf selectors stages
  pure (selectors,hits)

def collectOutputTests (dirty extra : BitVec 5) (leaves : Array Leaf) (stages : Array Stage) :
    Build (List (List TopSelector × List Lit)) := do
  let results ← (List.range' 13 13).mapM fun line => collectLineTests dirty extra line leaves[line-13]! stages
  positiveTests (results.map Prod.snd)
  pure results

def centreTerms (results : List (List TopSelector × List Lit)) (i : Nat) : List Lit :=
  results.flatMap fun row => row.1.filterMap fun (j,z,_) => if j == i then some z else none

/-- A dirty AND can only be read directly by a later charged gate. Each
    operand lists its atom mode first, followed by its direct-read selectors. -/
def dirtyTerms (stages : Array Stage) (i : Nat) : List Lit :=
  ((List.range stages.size).filter (i < ·)).flatMap fun k =>
    [(stages[k]!.operandModes 0)[i+1]!, (stages[k]!.operandModes 1)[i+1]!]

def finishSlot (key : CertificateKey) (stages : Array Stage)
    (results : List (List TopSelector × List Lit)) (i : Nat) : Build Unit := do
  if key.1.1.getLsbD i then require .dirtyUsed (dirtyTerms stages i)
  if key.1.2.getLsbD i then require .centreMask (centreTerms results i)

def finishOutputs (key : CertificateKey) (leaves : Array Leaf) (stages : Array Stage) : Build Unit := do
  let results ← collectOutputTests key.1.1 key.1.2 leaves stages
  (List.range 5).forM (finishSlot key stages results)

def combineSampleValues (dirty : Bool) (a b : Array Lit) : Build (Array Lit) := do
  let rows ← (List.range samples.size).mapM fun k =>
    (if dirty then makeAnd else makeOr) [a[k]!,b[k]!]
  pure rows.toArray

def combineRawSupport (dirty : Bool) (a b : Array Lit) : Build (Array Lit) := do
  let rows ← (List.range 26).mapM fun j => if dirty then pure (-1) else makeOr [a[j]!,b[j]!]
  pure rows.toArray

def orderPortModes (a b : List Lit) : Build Unit :=
  (List.range a.length).forM fun i => (b.take i).forM fun mode => require .portOrder [-a[i]!,-mode]

def buildStagePorts (stages : Array Stage) (hosts : Array Leaf) (i : Nat) (canonical : Bool) :
    Build (Port × Port) := do
  let a ← buildPort stages hosts i 0 canonical
  let b ← buildPort stages hosts i 1 canonical
  orderPortModes a.modes b.modes
  pure (a,b)

def constrainFirstActivity (extra : BitVec 5) (active : Bool) (retained values : Array Lit) : Build (Array Lit) := do
  let witness ← (List.range 52).mapM fun k => makeAnd [-retained[k]!,values[k]!]
  if active then
    require .firstActivity (if extra == 0 then [values[0]!] else witness)
    pure values
  else
    witness.forM fun lit => require .firstActivity [-lit]
    pure (Array.replicate values.size (-1))

def retainedInputs (leaves : Array Leaf) : Array Lit :=
  edgeRows.map fun (p,l) => rawAt leaves[l-13]! p

def activityAt (key : CertificateKey) (i : Nat) : Option Bool :=
  if key.1.1.getLsbD i && i == firstBit key.1.1 then (mode key.2).1 else none

def applyStageActivity (key : CertificateKey) (leaves : Array Leaf) (i : Nat) (values : Array Lit) :
    Build (Array Lit) :=
  match activityAt key i with
  | none => pure values
  | some active => constrainFirstActivity key.1.2 active (retainedInputs leaves) values

def checkFirstShape (dirty : Bool) (i : Nat) (geometry : Int) (a b : Array Lit) : Build Unit := do
  if dirty && i == 0 && geometry ≥ 0 then
    if geometry == 0 then
      (List.range' 13 13).forM fun v => do
        require .firstShape [-a[v]!]
        require .firstShape [-b[v]!]
    else
      let line := (12+geometry).toNat
      (List.range' 13 13).forM fun v => require .firstShape [-a[v]!]
      require .firstShape [b[line]!]
      require .firstShape ((List.range 13).filterMap fun v =>
        if (neighbours line).contains v then none else some a[v]!)

def stageAncestors (dirty : Bool) (i : Nat) (a b : Port) : Build (Array Lit) :=
  buildLitArray 5 fun j =>
    if dirty then pure (if j == i then 1 else -1)
    else makeOr [a.ancestors[j]!,b.ancestors[j]!]

def requireWhen (condition : Bool) (rule : Rule) (terms : List Lit) : Build Unit :=
  if condition then require rule terms else pure ()

def checkAncestorRules (dirty order centre : Bool) (anc : Array Lit) : Build Unit := do
  requireWhen (!dirty && order) .canonicalOrder anc.toList
  requireWhen (!dirty && centre) .centreExclusion [-anc[0]!]

def checkStageAncestors (key : CertificateKey) (i : Nat) (a b : Port) : Build (Array Lit) := do
  let isDirty := key.1.1.getLsbD i
  if (mode key.2).2.2 then
    let anc ← stageAncestors isDirty i a b
    checkAncestorRules isDirty (decide (i > firstBit key.1.1))
      ((mode key.2).2.1 == 0 && key.1.2.getLsbD i) anc
    pure anc
  else pure #[]

def appendStage (key : CertificateKey) (leaves : Array Leaf) (stages : Array Stage)
    (i : Nat) : Build (Array Stage) := do
  let ports ← buildStagePorts stages (portHosts leaves) i (mode key.2).2.2
  let a := ports.1
  let b := ports.2
  let dirty := key.1.1.getLsbD i
  let samples ← combineSampleValues dirty a.values b.values
  let raw ← combineRawSupport dirty a.raw b.raw
  checkFirstShape dirty i (mode key.2).2.1 a.raw b.raw
  let values ← applyStageActivity key leaves i samples
  let anc ← checkStageAncestors key i a b
  modify fun s => {s with uses := s.uses.push #[]}
  pure (stages.push ⟨dirty,raw,values,anc,fun operand => if operand = 0 then a.modes else b.modes⟩)

def buildStages (key : CertificateKey) (leaves : Array Leaf) : Build (Array Stage) :=
  (List.range' 0 5).foldlM (appendStage key leaves) #[]

def emitStages (key : CertificateKey) (leaves : Array Leaf) : Build Unit := do
  let stages ← buildStages key leaves
  finishOutputs key leaves stages

def program (key : CertificateKey) : Build Unit := do
  let leaves ← prepare key.1.2
  emitStages key leaves

def build (key : CertificateKey) : BuildState := ((program key).run {}).2

end SixEdge.Formula
