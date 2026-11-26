import Std.Tactic

namespace RestrictedGateFrontier

inductive Op where | conj | disj
deriving DecidableEq, Repr

def Op.eval : Op → Bool → Bool → Bool
  | .conj, a, b => a && b
  | .disj, a, b => a || b

structure Gate where
  op : Op
  left : Nat
  right : Nat
  out : Nat

inductive Residual where
  | const (v : Bool)
  | alias (wire : Nat)
  | gate (op : Op) (left right : Nat)
deriving DecidableEq, Repr

def Residual.eval (σ : Nat → Bool) : Residual → Bool
  | .const v => v
  | .alias i => σ i
  | .gate op i j => op.eval (σ i) (σ j)

def Residual.fixed : Residual → Option Bool
  | .const v => some v
  | _ => none

def Residual.deleted : Residual → Nat
  | .gate _ _ _ => 0
  | _ => 1

def simplifySide : Op → Bool → Nat → Residual
  | .conj, false, _ => .const false
  | .conj, true, other => .alias other
  | .disj, true, _ => .const true
  | .disj, false, other => .alias other

def simplify (g : Gate) (left right : Option Bool) : Residual :=
  match left, right with
  | some a, some b => .const (g.op.eval a b)
  | some a, none => simplifySide g.op a g.right
  | none, some b => simplifySide g.op b g.left
  | none, none => .gate g.op g.left g.right

/-- Folding is semantically exact for every assignment extending the restriction. -/
theorem simplify_correct (g : Gate) (σ : Nat → Bool) (l r : Option Bool)
    (hl : ∀ b, l = some b → σ g.left = b)
    (hr : ∀ b, r = some b → σ g.right = b) :
    (simplify g l r).eval σ = g.op.eval (σ g.left) (σ g.right) := by
  rcases g with ⟨op, i, j, out⟩
  cases op <;> cases l with
  | none => cases r with
    | none => rfl
    | some b => cases b <;> simp_all [simplify, simplifySide, Residual.eval, Op.eval]
  | some a => cases a <;> cases r with
    | none => simp_all [simplify, simplifySide, Residual.eval, Op.eval]
    | some b => cases b <;> simp_all [simplify, Residual.eval, Op.eval]

theorem deleted_eq (g : Gate) (l r : Option Bool) :
    (simplify g l r).deleted = (l.isSome || r.isSome).toNat := by
  rcases g with ⟨op, i, j, out⟩
  cases op <;> cases l with
  | none => cases r with
    | none => rfl
    | some b => cases b <;> rfl
  | some a => cases a <;> cases r <;> rfl

/-- The outgoing constant when two input constants meet. -/
theorem two_constants (g : Gate) (a b : Bool) :
    (simplify g (some a) (some b)).fixed = some (g.op.eval a b) := rfl

structure Claim where
  hit : Bool
  rest : List Nat

def claim (fixed : Bool) (wire : Nat) (ts : List Nat) : Claim :=
  if fixed ∧ wire ∈ ts then ⟨true, ts.erase wire⟩ else ⟨false, ts⟩

theorem claim_account (fixed : Bool) (wire : Nat) (ts : List Nat) :
    (claim fixed wire ts).rest.length + (claim fixed wire ts).hit.toNat = ts.length := by
  unfold claim
  split <;> rename_i h
  · have hpos := List.length_pos_of_mem h.2
    simp [List.length_erase_of_mem h.2, Bool.toNat]
    omega
  · simp [Bool.toNat]

theorem hit_only_if_fixed (b : Bool) (i : Nat) (ts : List Nat) :
    (claim b i ts).hit = true → b = true := by
  unfold claim
  split <;> simp_all

structure State where
  fixed : Nat → Option Bool
  tokens : List Nat

def put (v : Nat → Option Bool) (wire : Nat) (b : Option Bool) : Nat → Option Bool :=
  fun i => if i = wire then b else v i

def forward (out : Nat) (left right : Bool) (ts : List Nat) : List Nat :=
  if left && right then out :: ts else ts

def step (g : Gate) (s : State) : State × Nat :=
  let l := s.fixed g.left
  let r := s.fixed g.right
  let a := claim l.isSome g.left s.tokens
  let b := claim r.isSome g.right a.rest
  let residual := simplify g l r
  (⟨put s.fixed g.out residual.fixed, forward g.out a.hit b.hit b.rest⟩, residual.deleted)

private theorem accounting (out : Nat) (ts : List Nat) (a b l r : Bool)
    (ha : a = true → l = true) (hb : b = true → r = true) :
    ts.length + a.toNat + b.toNat ≤
      (forward out a b ts).length + (l || r).toNat := by
  cases a <;> cases b <;> cases l <;> cases r <;> simp_all [forward, Bool.toNat] <;> omega

theorem step_bound (g : Gate) (s : State) :
    s.tokens.length ≤ (step g s).1.tokens.length + (step g s).2 := by
  let l := (s.fixed g.left).isSome
  let r := (s.fixed g.right).isSome
  let a := claim l g.left s.tokens
  let b := claim r g.right a.rest
  have h₁ : a.rest.length + a.hit.toNat = s.tokens.length :=
    claim_account l g.left s.tokens
  have h₂ : b.rest.length + b.hit.toNat = a.rest.length :=
    claim_account r g.right a.rest
  have key := accounting g.out b.rest a.hit b.hit l r
    (hit_only_if_fixed l g.left s.tokens) (hit_only_if_fixed r g.right a.rest)
  change s.tokens.length ≤ (forward g.out a.hit b.hit b.rest).length +
    (simplify g (s.fixed g.left) (s.fixed g.right)).deleted
  rw [deleted_eq]
  change s.tokens.length ≤ (forward g.out a.hit b.hit b.rest).length + (l || r).toNat
  omega

def run : List Gate → State → State × Nat
  | [], s => (s, 0)
  | g :: gs, s =>
    let (s', cost) := step g s
    let (s'', tailCost) := run gs s'
    (s'', cost + tailCost)

/-- The number of initially marked wires is at most the eliminated gates plus remaining marks.
    The list representation claims each mark once; a repeated input cannot consume
    a single mark twice. No layering or fanout assumption enters the accounting. -/
theorem frontier_bound (gs : List Gate) (s : State) :
    s.tokens.length ≤ (run gs s).1.tokens.length + (run gs s).2 := by
  induction gs generalizing s with
  | nil => simp [run]
  | cons g gs ih =>
    have h₁ := step_bound g s
    have h₂ := ih (step g s).1
    change s.tokens.length ≤ (run gs (step g s).1).1.tokens.length +
      ((step g s).2 + (run gs (step g s).1).2)
    omega

theorem discharged_frontier_bound (gs : List Gate) (s : State)
    (done : (run gs s).1.tokens = []) : s.tokens.length ≤ (run gs s).2 := by
  simpa [done] using frontier_bound gs s

#print axioms simplify_correct
#print axioms frontier_bound
#print axioms discharged_frontier_bound

end RestrictedGateFrontier
