import RowPartition

namespace PlaneCut
open Finset
abbrev Row := Fin 13

/-- Numbered gates start immediately after the raw inputs. The row values of a gate
are the pointwise AND or OR of two earlier wires. -/
structure Network where
  inputs : Nat
  left : Nat → Nat
  right : Nat → Nat
  isAnd : Nat → Bool
  view : Nat → Row → View
  purePoint : Nat → Bool

def contact (N : Network) (j : Nat) := N.purePoint (N.left j) || N.purePoint (N.right j)
def freePositions (N : Network) (k : Nat) := (range k).filter fun j => (contact N j || N.isAnd j) = false
def mixedAnds (N : Network) (k : Nat) := (range k).filter fun j => (!contact N j && N.isAnd j) = true

structure Wiring (N : Network) (k : Nat) : Prop where
  before : ∀ j < k, N.left j < N.inputs + j ∧ N.right j < N.inputs + j
  input : ∀ i < N.inputs, ∀ r, good 0 (N.view i r)
  eval : ∀ j < k, ∀ r, N.view (N.inputs+j) r = combine (N.isAnd j) (N.view (N.left j) r) (N.view (N.right j) r)
  unique : ∀ j < k, ∀ r s, charge (N.isAnd j) (N.view (N.inputs+j) r) →
    charge (N.isAnd j) (N.view (N.inputs+j) s) → r = s
  excluded : ∀ j < k, contact N j = true → ∀ r, charge (N.isAnd j) (N.view (N.inputs+j) r) = false

private theorem lowerPrefix (N : Network) (k : Nat) (net : Wiring N k) :
    ∃ parts : Row → Part, (∀ i < N.inputs+k, ∀ r, good (parts r) (N.view i r)) ∧
      ∑ r, cost (parts r) ≤ (freePositions N k).card := by
  induction k with
  | zero => exact ⟨fun _ => 0,net.input,by simp [initial]⟩
  | succ k ih =>
    have prior : Wiring N k :=
      ⟨fun j hj => net.before j (by omega),net.input,fun j hj => net.eval j (by omega),
        fun j hj => net.unique j (by omega),fun j hj => net.excluded j (by omega)⟩
    obtain ⟨p,valid,spent⟩ := ih prior
    obtain ⟨hl,hr⟩ := net.before k (by omega)
    let out := N.inputs+k
    have step (r : Row) := advance (N.isAnd k) (valid _ hl r) (valid _ hr r)
    choose q old new costStep using step
    refine ⟨q,?_,?_⟩
    · intro i hi r
      by_cases top : i = out
      · subst i
        rw [net.eval k (by omega)]
        exact new r
      · exact old r _ (valid i (by dsimp [out] at top; omega) r)
    · let charged := fun r => charge (N.isAnd k) (N.view out r)
      have costs (r) : cost (q r) ≤ cost (p r) + (charged r).toNat := by
        simpa only [charged,out,net.eval k (by omega)] using costStep r
      have sumCost := Finset.sum_le_sum (s:=univ) (fun r _ => costs r)
      rw [Finset.sum_add_distrib] at sumCost
      have single : ∑ r, (charged r).toNat ≤ 1 := by
        by_cases some : ∃ r, charged r = true
        · obtain ⟨r,yes⟩ := some
          have zero (s : Row) (ne : s ≠ r) : (charged s).toNat = 0 := by
            cases hs : charged s
            · rfl
            · exact (ne (net.unique k (by omega) s r hs yes)).elim
          rw [Finset.sum_eq_single r (fun s _ ne => zero s ne) (by simp)]
          simp [yes]
        · have no (r : Row) : charged r = false := by
            cases h : charged r
            · rfl
            · exact (some ⟨r,h⟩).elim
          simp [no]
      cases h : contact N k || N.isAnd k
      · have plus : (freePositions N (k+1)).card = (freePositions N k).card + 1 := by
          obtain ⟨a,b⟩ := Bool.or_eq_false_iff.mp h
          simp [freePositions,Finset.range_add_one,Finset.filter_insert,a,b]
        omega
      · have no (r) : charged r = false := by
          rcases Bool.or_eq_true_iff.mp h with hc | ha
          · exact net.excluded k (by omega) hc r
          · simp [charged,charge,ha]
        simp [no] at sumCost
        have same : freePositions N (k+1) = freePositions N k := by
          rcases Bool.or_eq_true_iff.mp h with a | b
          · simp [freePositions,Finset.range_add_one,Finset.filter_insert,a]
          · simp [freePositions,Finset.range_add_one,Finset.filter_insert,b]
        rw [same]
        exact sumCost.trans spent

def roots (N : Network) (k : Nat) := (range (N.inputs+k)).filter fun w => N.purePoint w = true
def pureGates (N : Network) (k : Nat) := (range k).filter fun j => N.purePoint (N.inputs+j) = true
def contacts (N : Network) (k : Nat) := (range k).filter fun j => contact N j = true
def ports (N : Network) (j : Nat) : Finset Nat :=
  ({N.left j,N.right j} : Finset Nat).filter fun i => N.purePoint i = true

/-- Counting operand slots pays once for every essential point input, even when
arbitrarily many point-only wires merge before reaching the lines. -/
theorem rawBudget (N : Network) (k : Nat)
    (kind : ∀ j < k, N.purePoint (N.inputs+j) = (N.purePoint (N.left j) && N.purePoint (N.right j)))
    (used : ∀ w ∈ roots N k, ∃ j < k, w ∈ ports N j) :
    (roots N 0).card ≤ (contacts N k).card := by
  have rootCount (t : Nat) : (roots N t).card = (roots N 0).card + (pureGates N t).card := by
    induction t with
    | zero => simp [pureGates]
    | succ t ih =>
      have group : N.inputs + (t+1) = (N.inputs+t)+1 := by omega
      unfold roots pureGates at ih ⊢
      simp only [group,Finset.range_add_one,Finset.filter_insert]
      cases h : N.purePoint (N.inputs+t) <;> simp [h] at * <;> omega
  have covered : roots N k ⊆ (range k).biUnion (ports N) := by
    intro w hw
    obtain ⟨j,hj,v⟩ := used w hw
    exact mem_biUnion.mpr ⟨j,mem_range.mpr hj,v⟩
  have atMost (j) (hj : j ∈ range k) : (ports N j).card ≤
      (if contact N j then 1 else 0) + (if N.purePoint (N.inputs+j) then 1 else 0) := by
    rw [kind j (mem_range.mp hj)]
    unfold ports contact
    by_cases eq : N.left j = N.right j
    · rw [eq]
      cases hb : N.purePoint (N.right j) <;> simp [Finset.filter_singleton,hb]
    · cases ha : N.purePoint (N.left j) <;> cases hb : N.purePoint (N.right j) <;>
        simp [Finset.filter_insert,Finset.filter_singleton,ha,hb,eq]
  have hsum := Finset.sum_le_sum (s:=range k) atMost
  rw [Finset.sum_add_distrib] at hsum
  have bound := (card_le_card covered).trans (card_biUnion_le.trans hsum)
  rw [rootCount k] at bound
  simp only [Finset.sum_boole] at bound
  change (roots N 0).card + (pureGates N k).card ≤ (contacts N k).card + (pureGates N k).card at bound
  omega

/-- Computable certificate for a cut. Each score is a lower bound on the number
of merges forced by the safe boundary traces in that row. -/
def scoreValid (N : Network) (F : Finset Nat) (score : Row → Nat) :=
  ∀ r p, (∀ w ∈ F, good p (N.view w r)) → score r ≤ cost p

private theorem balance (N : Network) (k : Nat) :
    (contacts N k).card + (freePositions N k).card + (mixedAnds N k).card = k := by
  induction k with
  | zero => simp [contacts,freePositions,mixedAnds]
  | succ k ih =>
    cases hc : contact N k <;> cases ha : N.isAnd k <;>
      simp [contacts,freePositions,mixedAnds,Finset.range_add_one,Finset.filter_insert,hc,ha] at ih ⊢ <;> omega

theorem positionLedger (N : Network) (k tail : Nat) (F : Finset Nat) (score : Row → Nat)
    (net : Wiring N k) (boundary : ∀ w ∈ F, w < N.inputs+k) (hscore : scoreValid N F score)
    (room : F.card ≤ tail + 1) :
    (contacts N k).card + F.card + ∑ r, score r + (mixedAnds N k).card ≤ k+tail+1 := by
  obtain ⟨p,goodness,paid⟩ := lowerPrefix N k net
  have each (r) := hscore r (p r) (fun w hw => goodness w (boundary w hw) r)
  have total := Finset.sum_le_sum (s:=univ) (fun r _ => each r)
  have account := balance N k
  omega

theorem ledger (N : Network) (k tail : Nat) (F : Finset Nat) (score : Row → Nat)
    (net : Wiring N k) (boundary : ∀ w ∈ F, w < N.inputs+k) (hscore : scoreValid N F score)
    (kind : ∀ j < k, N.purePoint (N.inputs+j) = (N.purePoint (N.left j) && N.purePoint (N.right j)))
    (used : ∀ w ∈ roots N k, ∃ j < k, w ∈ ports N j)
    (room : F.card ≤ tail + 1) :
    (roots N 0).card + F.card + ∑ r, score r + (mixedAnds N k).card ≤ k+tail+1 := by
  have h := positionLedger N k tail F score net boundary hscore room
  have raw := rawBudget N k kind used
  omega

#print axioms ledger
end PlaneCut
