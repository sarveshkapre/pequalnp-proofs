import Mathlib.Tactic.Sat.FromLRAT
import Std.Sat.CNF.Dimacs


open Lean Meta Elab Tactic
/-! The finite model is normalized to Boolean connectives. Each truth-table clause
gets a Lean proof. An LRAT refutation of these clauses then excludes the original
expression under its actual bit-selector valuation. -/
namespace MatchingKernelProp
theorem oneClause (v : Sat.Valuation) (c : Sat.Clause) (h : v.satisfies c) :
    v.satisfies_fmla (Sat.Fmla.one c) := by
  refine ⟨?_⟩
  rintro k hk
  have : k = c := by simpa [Sat.Fmla.one] using hk
  exact this ▸ h
theorem both (v : Sat.Valuation) (a b : Sat.Fmla) (l : v.satisfies_fmla a)
    (r : v.satisfies_fmla b) : v.satisfies_fmla (Sat.Fmla.and a b) :=
  ⟨fun c h => (List.mem_append.mp h).elim (l.prop c) (r.prop c)⟩
def branch (n k : Nat) (left right : Prop) : Prop := if n < k then left else right
theorem negated (p : Bool) (h : (p=true) → False) : p=false := Bool.eq_false_iff.mpr h
theorem assumed (p : Bool) (h : p=true) : (¬ p=true) → False := fun x => x h
theorem rowAnd0 (a b : Bool) : (¬ a = true) → (¬ b = true) → ((a && b) = true) → False := by
  cases a <;> cases b <;> decide
theorem rowAnd1 (a b : Bool) : (a = true) → (¬ b = true) → ((a && b) = true) → False := by
  cases a <;> cases b <;> decide
theorem rowAnd2 (a b : Bool) : (¬ a = true) → (b = true) → ((a && b) = true) → False := by
  cases a <;> cases b <;> decide
theorem rowAnd3 (a b : Bool) : (a = true) → (b = true) → (¬ (a && b) = true) → False := by
  cases a <;> cases b <;> decide
theorem rowOr0 (a b : Bool) : (¬ a = true) → (¬ b = true) → ((a || b) = true) → False := by
  cases a <;> cases b <;> decide
theorem rowOr1 (a b : Bool) : (a = true) → (¬ b = true) → (¬ (a || b) = true) → False := by
  cases a <;> cases b <;> decide
theorem rowOr2 (a b : Bool) : (¬ a = true) → (b = true) → (¬ (a || b) = true) → False := by
  cases a <;> cases b <;> decide
theorem rowOr3 (a b : Bool) : (a = true) → (b = true) → (¬ (a || b) = true) → False := by
  cases a <;> cases b <;> decide
theorem rowXnor0 (a b : Bool) : (¬ a = true) → (¬ b = true) → (¬ (a == b) = true) → False := by
  cases a <;> cases b <;> decide
theorem rowXnor1 (a b : Bool) : (a = true) → (¬ b = true) → ((a == b) = true) → False := by
  cases a <;> cases b <;> decide
theorem rowXnor2 (a b : Bool) : (¬ a = true) → (b = true) → ((a == b) = true) → False := by
  cases a <;> cases b <;> decide
theorem rowXnor3 (a b : Bool) : (a = true) → (b = true) → (¬ (a == b) = true) → False := by
  cases a <;> cases b <;> decide
theorem rowNot0 (a : Bool) : (¬ a = true) → (¬ (!a) = true) → False := by
  cases a <;> decide
theorem rowNot1 (a : Bool) : (a = true) → ((!a) = true) → False := by
  cases a <;> decide
theorem rowIf0 (a b c : Bool) : (¬ a = true) → (¬ b = true) → (¬ c = true) → ((if a then b else c) = true) → False := by
  cases a <;> cases b <;> cases c <;> decide
theorem rowIf1 (a b c : Bool) : (a = true) → (¬ b = true) → (¬ c = true) → ((if a then b else c) = true) → False := by
  cases a <;> cases b <;> cases c <;> decide
theorem rowIf2 (a b c : Bool) : (¬ a = true) → (b = true) → (¬ c = true) → ((if a then b else c) = true) → False := by
  cases a <;> cases b <;> cases c <;> decide
theorem rowIf3 (a b c : Bool) : (a = true) → (b = true) → (¬ c = true) → (¬ (if a then b else c) = true) → False := by
  cases a <;> cases b <;> cases c <;> decide
theorem rowIf4 (a b c : Bool) : (¬ a = true) → (¬ b = true) → (c = true) → (¬ (if a then b else c) = true) → False := by
  cases a <;> cases b <;> cases c <;> decide
theorem rowIf5 (a b c : Bool) : (a = true) → (¬ b = true) → (c = true) → ((if a then b else c) = true) → False := by
  cases a <;> cases b <;> cases c <;> decide
theorem rowIf6 (a b c : Bool) : (¬ a = true) → (b = true) → (c = true) → (¬ (if a then b else c) = true) → False := by
  cases a <;> cases b <;> cases c <;> decide
theorem rowIf7 (a b c : Bool) : (a = true) → (b = true) → (c = true) → (¬ (if a then b else c) = true) → False := by
  cases a <;> cases b <;> cases c <;> decide
theorem rowYes0 : (¬ true = true) → False := by
  decide
theorem rowNo0 : (false = true) → False := by
  decide
structure State where
  index : Std.HashMap Expr Nat := {}
  values : Array Expr := #[]
  rows : Array (Array Int) := #[]
  proofs : Array Expr := #[]
  atoms : Array (Nat × Expr) := #[]
abbrev M := StateT State MetaM
private def bit (r i : Nat) := r.testBit i
private def positive (v : Nat) : Int := Int.ofNat (v+1)
private def sign (v : Nat) (yes : Bool) : Int := if yes then positive v else -(positive v)

private partial def build (e : Expr) : M Nat := do
  if let some k := (← get).index[e]? then return k
  let n := e.getAppFn.constName
  let (op,args) ← do
    if !e.hasFVar then
      if ← isDefEq e (mkConst ``Bool.true) then pure ("Yes",#[])
      else if ← isDefEq e (mkConst ``Bool.false) then pure ("No",#[])
      else pure ("",#[])
    else if n == ``Bool.and then pure ("And",e.getAppArgs)
    else if n == ``Bool.or then pure ("Or",e.getAppArgs)
    else if n == ``Bool.not then pure ("Not",e.getAppArgs)
    else if n == ``BEq.beq then pure ("Xnor",e.getAppArgs.extract 2 4)
    else if n == ``ite then
      let a := e.getAppArgs
      if let some (_,p,t) := a[1]!.eq? then
        if t.isConstOf ``Bool.true then pure ("If",#[p,a[3]!,a[4]!])
        else pure ("",#[])
      else pure ("",#[])
    else pure ("",#[])
  if op.isEmpty then
    for (id,atom) in (← get).atoms do
      if ← isDefEq e atom then
        modify fun st => {st with index := st.index.insert e id}
        return id
  let ids ← args.mapM build
  let k := (← get).values.size
  modify fun st => {st with values := st.values.push e, index := st.index.insert e k}
  if op.isEmpty then modify fun st => {st with atoms := st.atoms.push (k,e)}
  if !op.isEmpty then
    for r in [0:2^args.size] do
      let y := match op with
        | "And" => bit r 0 && bit r 1
        | "Or" => bit r 0 || bit r 1
        | "Xnor" => bit r 0 == bit r 1
        | "If" => if bit r 0 then bit r 1 else bit r 2
        | "Not" => !(bit r 0)
        | _ => op == "Yes"
      let mut clause := #[]
      for i in [0:ids.size] do clause := clause.push (sign ids[i]! (!(bit r i)))
      clause := clause.push (sign k y)
      let name := Name.str `MatchingKernelProp s!"row{op}{r}"
      let pf := mkAppN (mkConst name) args
      modify fun st => {st with rows := st.rows.push clause, proofs := st.proofs.push pf}
  return k

/-- A balanced lookup tree keeps constant-index reductions logarithmic. -/
private partial def valuation (a : Array Expr) (n : Expr) (lo hi : Nat) : Expr := Id.run do
  if hi-lo ≤ 1 then return mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) a[lo]! (mkConst ``Bool.true)
  let k := (lo+hi)/2
  return mkApp4 (mkConst ``branch) n (mkRawNatLit k) (valuation a n lo k) (valuation a n k hi)

/-- Mirror the same balanced conjunction tree as Mathlib's clause refutation. -/
private partial def discharge (rows : Array (Array Int)) (pfs : Array Expr) (v : Expr)
    (lo hi : Nat) : Expr × Expr := Id.run do
  if hi-lo ≤ 1 then
    let c := Mathlib.Tactic.Sat.buildClause rows[lo]!
    return (mkApp (mkConst ``Sat.Fmla.one) c, mkApp3 (mkConst ``oneClause) v c pfs[lo]!)
  let k := lo+(hi-lo)/2
  let (cl,l) := discharge rows pfs v lo k
  let (cr,r) := discharge rows pfs v k hi
  return (mkApp2 (mkConst ``Sat.Fmla.and) cl cr,mkApp5 (mkConst ``both) v cl cr l r)

register_option matching.dump : Bool := { defValue := false, descr := "Write the propositional CNF for an isolated certificate search" }

elab "matching_kernel_sat" : tactic => withMainContext do
  let some (_,lhs,_) := (← getMainTarget).eq? | throwError "expected a Boolean equality"
  let (k,st) ← (build lhs).run {}
  let rows := st.rows.push #[positive k]
  let cnf : Std.Sat.CNF Nat := ⟨rows.map fun r => Std.Sat.CNF.Clause.ofLiterals
    (r.toList.map fun i => (i.natAbs-1, decide (0 < i)))⟩
  IO.println s!"Propositional circuit: {st.values.size} nodes, {rows.size} clauses."
  let src := System.FilePath.mk (← getFileName)
  let some dir := src.parent | throwError "Missing source directory."
  let some stem := src.fileStem | throwError "Missing source filename."
  let path := dir / "certificates" / (stem ++ ".lrat")
  if matching.dump.get (← getOptions) then
    IO.FS.writeFile (dir / (stem ++ ".cnf")) cnf.dimacs
    let ls ← st.atoms.mapM fun (id,e) => do return s!"{id+1} {(← ppExpr e)}"
    IO.FS.writeFile (dir / (stem ++ ".atoms")) (String.intercalate "\n" ls.toList)
    throwError "Wrote matching CNF."
  let cert ← IO.FS.readFile path
  do
    let name ← mkAuxDeclName `clauses
    let (_,_,_,refute) ← Mathlib.Tactic.Sat.fromLRATAux cnf.dimacs cert name
    let eqt ← mkEq lhs (mkConst ``Bool.true)
    withLocalDeclD `positive eqt fun h => do
      let v ← withLocalDeclD `idx (mkConst ``Nat) fun i => mkLambdaFVars #[i] (valuation st.values i 0 st.values.size)
      let pfs := st.proofs.push (mkApp2 (mkConst ``assumed) lhs h)
      let (_,evidence) := discharge rows pfs v 0 rows.size
      let contradiction := mkApp2 refute v evidence
      let implies ← mkLambdaFVars #[h] contradiction
      let pf := mkApp2 (mkConst ``negated) lhs implies
      (← getMainGoal).assign pf
      replaceMainGoal []
end MatchingKernelProp
