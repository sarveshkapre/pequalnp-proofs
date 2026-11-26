import PEqualNP.ThreeGateGain.FiniteFrame

/-! As a new leaf is selected, its private domain is the part of its row
outside every previous row. Existing domains lose the neighbors of that row.
The two finite-state updates avoid rescanning all selected leaves. -/
namespace GainFinite

structure FastState where
  neighbors : Nat
  domains : List Nat
deriving DecidableEq

def stateFor (h : Host) (chosen : Leaves) : FastState :=
  ⟨unionMask h chosen, chosen.map (privateMask h chosen)⟩

def nextState (row : Nat) (s : FastState) : FastState :=
  let keep := (2^27-1) ^^^ row
  ⟨row ||| s.neighbors, (row &&& ((2^27-1) ^^^ s.neighbors)) :: s.domains.map (· &&& keep)⟩

def FastState.ok (s : FastState) : Bool := s.domains.all (· != 0)

def cached (h : Host) (todo : Leaves) : List (WordType × Nat) :=
  todo.map fun i => (i, rowMask h i)

def fastVisit (test : Leaves → FastState → Bool) (chosen : Leaves) (s : FastState) :
    List (WordType × Nat) → Bool
  | [] => test chosen s
  | (i, row)::rest =>
    fastVisit test chosen s rest &&
      (let next := nextState row s
       !next.ok || fastVisit test (i::chosen) next rest)

private theorem private_new (h : Host) (xs : Leaves) (i : WordType) (fresh : i ∉ xs) :
    privateMask h (i::xs) i = rowMask h i &&& ((2^27-1) ^^^ unionMask h xs) := by
  have skip : xs.filter (· != i) = xs := by
    apply List.filter_eq_self.mpr
    intro x hx
    exact bne_iff_ne.mpr (fun e => fresh (e ▸ hx))
  simp [privateMask,skip]

private theorem private_old (h : Host) (xs : Leaves) (i k : WordType) (neq : i ≠ k) :
    privateMask h (i::xs) k =
      privateMask h xs k &&& ((2^27-1) ^^^ rowMask h i) := by
  have keep : (i != k) = true := bne_iff_ne.mpr neq
  unfold privateMask
  rw [List.filter_cons_of_pos (p:=fun x => x != k) keep]
  change rowMask h k &&& ((2^27-1) ^^^ (rowMask h i ||| unionMask h (xs.filter (· != k)))) =
    rowMask h k &&& ((2^27-1) ^^^ unionMask h (xs.filter (· != k))) &&& ((2^27-1) ^^^ rowMask h i)
  apply Nat.eq_of_testBit_eq
  intro n
  simp only [Nat.testBit_and,Nat.testBit_xor,Nat.testBit_or,Nat.testBit_two_pow_sub_one]
  by_cases hn : n < 27
  · simp only [hn,decide_true,Bool.true_xor]; generalize (rowMask h k).testBit n=a
    generalize (rowMask h i).testBit n=b
    generalize (unionMask h (xs.filter (· != k))).testBit n=c
    cases a <;> cases b <;> cases c <;> rfl
  · have zero : (rowMask h k).testBit n=false := by rw [rowMask, Nat.testBit_mod_two_pow]; simp [hn]
    simp [zero]

theorem next_state_correct (h : Host) (xs : Leaves) (i : WordType) (fresh : i ∉ xs) :
    nextState (rowMask h i) (stateFor h xs) = stateFor h (i::xs) := by
  unfold nextState stateFor
  simp only [List.map_cons,private_new h xs i fresh]
  congr 2
  rw [List.map_map]
  apply List.map_congr_left
  intro x hx
  exact (private_old h xs i x (fun e => fresh (e ▸ hx))).symm

theorem ok_state_correct (h : Host) (xs : Leaves) :
    (stateFor h xs).ok = eligible h xs := by simp [FastState.ok,stateFor,eligible,Function.comp_def]

/-- Replacing the plain branch test by the cached update preserves the complete
verdict. The ordered candidate list has no duplicates and is disjoint from the
chosen prefix. Concrete masks in the input can be substituted via `cached`. -/
theorem fastVisit_correct (h : Host) (test : Leaves → FastState → Bool)
    (chosen todo : Leaves) (nd : todo.Nodup) (apart : ∀ i ∈ todo, i ∉ chosen) :
    fastVisit test chosen (stateFor h chosen) (cached h todo) =
      visit (eligible h) (fun xs => test xs (stateFor h xs)) chosen todo := by
  induction todo generalizing chosen with
  | nil => rfl
  | cons i rest ih =>
    have fresh := apart i (List.mem_cons_self ..)
    have ni := List.nodup_cons.mp nd
    have restApart : ∀ x ∈ rest, x ∉ chosen := fun x hx => apart x (List.mem_cons_of_mem i hx)
    have moreApart (x : WordType) (hx : x ∈ rest) : x ∉ i::chosen := by
      simpa using And.intro (show x ≠ i by rintro rfl; exact ni.1 hx) (restApart x hx)
    change (fastVisit test chosen (stateFor h chosen) (cached h rest) &&
      (!(nextState (rowMask h i) (stateFor h chosen)).ok ||
       fastVisit test (i::chosen) (nextState (rowMask h i) (stateFor h chosen)) (cached h rest))) = _
    rw [next_state_correct h chosen i fresh, ok_state_correct, ih chosen ni.2 restApart,
        ih (i::chosen) ni.2 moreApart]
    rfl

#print axioms fastVisit_correct
end GainFinite
