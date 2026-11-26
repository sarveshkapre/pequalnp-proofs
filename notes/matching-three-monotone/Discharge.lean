import Frontier
import Std.Tactic

namespace RestrictedGateFrontier

def Reads : List Gate → Nat → Prop
  | [], _ => False
  | g :: gs, i => i = g.left ∨ i = g.right ∨ Reads gs i

/-- Every gate reads earlier wires, produces a fresh increasing wire, and
    its output is either read later or is the designated circuit output. -/
def LiveSuffix : List Gate → Nat → Nat → Prop
  | [], _, _ => True
  | g :: gs, next, out =>
    next ≤ g.out ∧ g.left < next ∧ g.right < next ∧
      (Reads gs g.out ∨ g.out = out) ∧ LiveSuffix gs (g.out+1) out

def ValidMarks (s : State) (gs : List Gate) (next out : Nat) : Prop :=
  s.tokens.Nodup ∧ ∀ i ∈ s.tokens,
    (s.fixed i).isSome = true ∧ i < next ∧ (Reads gs i ∨ i = out)

private theorem claim_nodup (flag : Bool) (i : Nat) (ts : List Nat) (h : ts.Nodup) :
    (claim flag i ts).rest.Nodup := by
  unfold claim
  split
  · exact h.erase i
  · exact h

private theorem rest_iff (flag : Bool) (wire : Nat) (ts : List Nat) (h : ts.Nodup)
    (valid : wire ∈ ts → flag = true) (i : Nat) :
    i ∈ (claim flag wire ts).rest ↔ i ∈ ts ∧ i ≠ wire := by
  unfold claim
  split
  · simpa [and_comm] using (h.mem_erase_iff (a := i) (b := wire))
  · rename_i hh
    change i ∈ ts ↔ i ∈ ts ∧ i ≠ wire
    have hnot : wire ∉ ts := fun hw => hh ⟨valid hw, hw⟩
    exact ⟨fun hi => ⟨hi, fun eq => hnot (eq ▸ hi)⟩, And.left⟩

private theorem valid_step (g : Gate) (gs : List Gate) (next out : Nat) (s : State)
    (hvalid : ValidMarks s (g::gs) next out) (fresh : next ≤ g.out)
    (used : Reads gs g.out ∨ g.out = out) :
    ValidMarks (step g s).1 gs (g.out+1) out := by
  let l := (s.fixed g.left).isSome
  let r := (s.fixed g.right).isSome
  let a := claim l g.left s.tokens
  let b := claim r g.right a.rest
  have ha (i : Nat) : i ∈ a.rest ↔ i ∈ s.tokens ∧ i ≠ g.left :=
    rest_iff l g.left s.tokens hvalid.1 (fun h => (hvalid.2 _ h).1) i
  have hb (i : Nat) : i ∈ b.rest ↔ i ∈ a.rest ∧ i ≠ g.right :=
    rest_iff r g.right a.rest (claim_nodup l g.left s.tokens hvalid.1)
      (fun h => (hvalid.2 _ ((ha _).mp h).1).1) i
  have nd : b.rest.Nodup := claim_nodup r g.right a.rest (claim_nodup l g.left s.tokens hvalid.1)
  have old (i : Nat) (hi : i ∈ b.rest) : i ∈ s.tokens ∧ i ≠ g.left ∧ i ≠ g.right := by
    obtain ⟨inA, nr⟩ := (hb i).mp hi
    obtain ⟨inS, nl⟩ := (ha i).mp inA
    exact ⟨inS, nl, nr⟩
  have younger (i : Nat) (hi : i ∈ b.rest) : i < g.out :=
    Nat.lt_of_lt_of_le (hvalid.2 i (old i hi).1).2.1 fresh
  have restValid (i : Nat) (hi : i ∈ b.rest) :
      ((step g s).1.fixed i).isSome = true ∧ i < g.out+1 ∧ (Reads gs i ∨ i = out) := by
    obtain ⟨inside, nl, nr⟩ := old i hi
    obtain ⟨cf, early, usedOld⟩ := hvalid.2 i inside
    have ne := Nat.ne_of_lt (younger i hi)
    refine ⟨?_, by omega, ?_⟩
    · simpa [step, put, ne] using cf
    · rcases usedOld with hits | done
      · rcases hits with hl | hr | tail
        · contradiction
        · contradiction
        · exact Or.inl tail
      · exact Or.inr done
  have notOut : g.out ∉ b.rest := fun h => Nat.lt_irrefl _ (younger _ h)
  by_cases both : (a.hit && b.hit) = true
  · have hab : a.hit = true ∧ b.hit = true := by simpa using both
    have cl := hit_only_if_fixed l g.left s.tokens hab.1
    have cr := hit_only_if_fixed r g.right a.rest hab.2
    obtain ⟨L, hL⟩ := Option.isSome_iff_exists.mp cl
    obtain ⟨R, hR⟩ := Option.isSome_iff_exists.mp cr
    have con : ((step g s).1.fixed g.out).isSome = true := by
      simp [step, put, hL, hR, two_constants]
    change (forward g.out a.hit b.hit b.rest).Nodup ∧ _
    have markEq : (step g s).1.tokens = g.out :: b.rest := by
      change forward g.out a.hit b.hit b.rest = _
      exact ite_eq_left both
    constructor
    · change (step g s).1.tokens.Nodup
      rw [markEq]
      exact List.nodup_cons.mpr ⟨notOut, nd⟩
    · intro i hi
      rw [markEq, List.mem_cons] at hi
      rcases hi with rfl | hin
      · exact ⟨con, Nat.lt_succ_self _, used⟩
      · exact restValid i hin
  · have markEq : (step g s).1.tokens = b.rest := by
      change forward g.out a.hit b.hit b.rest = _
      exact ite_eq_right both
    exact ⟨markEq ▸ nd, fun i hi => restValid i (markEq ▸ hi)⟩

private theorem valid_final (gs : List Gate) (s : State) (next out : Nat)
    (live : LiveSuffix gs next out) (valid : ValidMarks s gs next out) :
    ∀ i ∈ (run gs s).1.tokens, ((run gs s).1.fixed i).isSome = true ∧ i = out := by
  induction gs generalizing s next with
  | nil =>
    intro i hi
    obtain ⟨h, _, hf | he⟩ := valid.2 i hi
    · exact False.elim hf
    · exact ⟨h, he⟩
  | cons g gs ih =>
    obtain ⟨fresh, _, _, used, tail⟩ := live
    exact ih (step g s).1 (g.out+1) tail (valid_step g gs next out s valid fresh used)

/-- Termination of the account on a live suffix with a nonconstant final wire. -/
theorem no_final_marks (gs : List Gate) (s : State) (next out : Nat)
    (live : LiveSuffix gs next out) (valid : ValidMarks s gs next out)
    (nonconst : (run gs s).1.fixed out = none) : (run gs s).1.tokens = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro i hi
  obtain ⟨hc, rfl⟩ := valid_final gs s next out live valid i hi
  simp [nonconst] at hc

/-- A variable assignment to all DAG wires agrees with all recorded constants. -/
def Agrees (known : Nat → Option Bool) (σ : Nat → Bool) : Prop :=
  ∀ i b, known i = some b → σ i = b

def Realizes (σ : Nat → Bool) (g : Gate) : Prop :=
  σ g.out = g.op.eval (σ g.left) (σ g.right)

private theorem residual_agrees (res : Residual) (σ : Nat → Bool) (b : Bool)
    (hb : res.fixed = some b) : res.eval σ = b := by
  cases res <;> simp_all [Residual.fixed, Residual.eval]

private theorem agrees_after_gate (g : Gate) (s : State) (σ : Nat → Bool)
    (ag : Agrees s.fixed σ) (sem : Realizes σ g) : Agrees (step g s).1.fixed σ := by
  intro i b hi
  by_cases he : i = g.out
  · subst i
    have hres : (simplify g (s.fixed g.left) (s.fixed g.right)).fixed = some b := by
      simpa [step, put] using hi
    have spec := simplify_correct g σ (s.fixed g.left) (s.fixed g.right) (ag _) (ag _)
    exact sem.trans (spec.symm.trans (residual_agrees _ σ b hres))
  · exact ag i b (by simpa [step, put, he] using hi)

theorem agrees_after_run (gs : List Gate) (s : State) (σ : Nat → Bool)
    (ag : Agrees s.fixed σ) (sem : ∀ g ∈ gs, Realizes σ g) :
    Agrees (run gs s).1.fixed σ := by
  induction gs generalizing s with
  | nil => exact ag
  | cons g gs ih =>
    exact ih (step g s).1 (agrees_after_gate g s σ ag (sem g (by simp)))
      (fun h hh => sem h (by simp [hh]))

/-- A live suffix eliminating all marked constants must lose at least the number
    of distinct originally marked wires. Nonconstancy uses two actual assignments
    extending the restriction and satisfying every gate, with different outputs. -/
theorem live_frontier_bound (gs : List Gate) (s : State) (next out : Nat)
    (live : LiveSuffix gs next out) (valid : ValidMarks s gs next out)
    (σ τ : Nat → Bool) (aσ : Agrees s.fixed σ) (aτ : Agrees s.fixed τ)
    (sσ : ∀ g ∈ gs, Realizes σ g) (sτ : ∀ g ∈ gs, Realizes τ g)
    (different : σ out ≠ τ out) : s.tokens.length ≤ (run gs s).2 := by
  have nn : (run gs s).1.fixed out = none := by
    cases he : (run gs s).1.fixed out with
    | none => rfl
    | some b =>
      have eσ := agrees_after_run gs s σ aσ sσ out b he
      have eτ := agrees_after_run gs s τ aτ sτ out b he
      exact False.elim (different (eσ.trans eτ.symm))
  exact discharged_frontier_bound gs s (no_final_marks gs s next out live valid nn)

#print axioms live_frontier_bound

end RestrictedGateFrontier
