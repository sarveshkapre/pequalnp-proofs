import GateLedger

namespace PlaneCut.GuardRestriction
open Finset

inductive Step where
  | zero
  | copy (src : Nat)
  | gate (isAnd : Bool) (a b : Nat)
  deriving DecidableEq

def Step.val (v : Nat → Bool) : Step → Bool
  | .zero => false
  | .copy s => v s
  | .gate op a b => if op then v a && v b else v a || v b

def Step.paid : Step → Bool
  | .gate _ _ _ => true
  | _ => false

/-- The tag marks a wire built exclusively from the designated zero inputs. -/
def rewrite (N : Network) (j : Nat) : Step :=
  let a := N.left j
  let b := N.right j
  if N.purePoint a then
    if N.isAnd j then .zero else .copy b
  else if N.purePoint b then
    if N.isAnd j then .zero else .copy a
  else .gate (N.isAnd j) a b

theorem localRewrite (N : Network) (j : Nat) (v : Nat → Bool)
    (a : N.purePoint (N.left j) = true → v (N.left j) = false)
    (b : N.purePoint (N.right j) = true → v (N.right j) = false) :
    (rewrite N j).val v = (Step.gate (N.isAnd j) (N.left j) (N.right j)).val v := by
  cases ha : N.purePoint (N.left j) <;> cases hb : N.purePoint (N.right j) <;>
    cases ho : N.isAnd j <;> simp_all [rewrite,Step.val]

theorem allWires (N : Network) (k : Nat)
    (before : ∀ j < k, N.left j < N.inputs+j ∧ N.right j < N.inputs+j)
    (kind : ∀ j < k, N.purePoint (N.inputs+j) = (N.purePoint (N.left j) && N.purePoint (N.right j)))
    (v u : Nat → Bool) (raw : ∀ w < N.inputs, u w = v w)
    (off : ∀ w < N.inputs, N.purePoint w = true → v w = false)
    (old : ∀ j < k, v (N.inputs+j) = (Step.gate (N.isAnd j) (N.left j) (N.right j)).val v)
    (new : ∀ j < k, u (N.inputs+j) = (rewrite N j).val u)
    (w : Nat) (hw : w < N.inputs+k) :
    u w = v w ∧ (N.purePoint w = true → v w = false) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases base : w < N.inputs
    · exact ⟨raw w base, off w base⟩
    let j := w - N.inputs
    have eq : N.inputs+j = w := by dsimp [j]; omega
    have jlt : j < k := by dsimp [j]; omega
    obtain ⟨al,bl⟩ := before j jlt
    obtain ⟨av,ao⟩ := ih _ (by omega : N.left j < w) (by omega)
    obtain ⟨bv,bo⟩ := ih _ (by omega : N.right j < w) (by omega)
    constructor
    · rw [←eq,new j jlt,old j jlt, localRewrite N j u (fun h => av.trans (ao h)) (fun h => bv.trans (bo h))]
      simp [Step.val,av,bv]
    · rw [←eq,kind j jlt,old j jlt]
      intro h
      obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
      simp [Step.val,ao ha,bo hb]

/-- After redirecting copies, only the paid steps need a physical gate. -/
theorem paidBudget (N : Network) (k : Nat)
    (kind : ∀ j < k, N.purePoint (N.inputs+j) = (N.purePoint (N.left j) && N.purePoint (N.right j)))
    (used : ∀ w ∈ roots N k, ∃ j < k, w ∈ ports N j) :
    (roots N 0).card + ((range k).filter (fun j => (rewrite N j).paid)).card ≤ k := by
  have tag (j : Nat) : (rewrite N j).paid = !(contact N j) := by
    cases a : N.purePoint (N.left j) <;> cases b : N.purePoint (N.right j) <;>
      cases op : N.isAnd j <;> simp [rewrite,Step.paid,contact,a,b,op]
  have total (m : Nat) : (contacts N m).card + ((range m).filter (fun j => (rewrite N j).paid)).card = m := by
    induction m with
    | zero => simp [contacts]
    | succ m ih =>
      cases h : contact N m <;> simp [contacts,range_add_one,filter_insert,tag,h] at ih ⊢ <;> omega
  have lower := rawBudget N k kind used
  have sum := total k
  omega

-- Each row has one shared flag and three private flags. A private flag in
-- either row requires the cross mask indexed by its line and each opposite line.
def countFlags (s : Fin 256) := ((List.range 8).filter fun j => s.val.testBit j).length
def crossCount (s : Fin 256) := ((List.range 9).filter fun j =>
  s.val.testBit (1+j/3) || s.val.testBit (5+j%3)).length
theorem crossCapacity : ∀ s : Fin 256, 6 ≤ countFlags s →
    countFlags s + 1 < crossCount s + 2 ∧ countFlags s + 3 < crossCount s + 3 := by
  decide +kernel

#print axioms allWires
#print axioms paidBudget
#print axioms crossCapacity
end PlaneCut.GuardRestriction
