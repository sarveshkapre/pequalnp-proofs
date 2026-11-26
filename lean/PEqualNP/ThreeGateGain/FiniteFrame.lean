import PEqualNP.ThreeGateGain.FiniteCatalogue
import Mathlib.Tactic

namespace GainFinite

abbrev Leaves := List WordType

def rowMask (h : Host) (i : WordType) : Nat :=
  (hostBits h >>> (27*i.val)) % 2^27

def unionMask (h : Host) (xs : Leaves) : Nat :=
  xs.foldr (fun i m => rowMask h i ||| m) 0

def positions (m : Nat) : Leaves := (List.finRange 27).filter (fun i => m.testBit i.val)

def size27 (m : Nat) : Nat := (positions m).length

def privateMask (h : Host) (xs : Leaves) (i : WordType) : Nat :=
  rowMask h i &&& ((2^27-1) ^^^ unionMask h (xs.filter (· != i)))

def eligible (h : Host) (xs : Leaves) : Bool :=
  xs.all (fun i => privateMask h xs i != 0)

def liveRows (h : Host) (rl cl : Leaves) : List Nat :=
  let blockedRows := unionMask h cl
  let availableCols := (2^27-1) ^^^ unionMask h rl
  (((List.finRange 27).filter (fun i => !(blockedRows.testBit i.val))).map
    (fun i => rowMask h i &&& availableCols)).filter (· != 0)

def residual (h : Host) (rl cl : Leaves) : Nat :=
  let rows := liveRows h rl cl
  3 * min (rows.map size27).sum (rows.length + size27 (rows.foldr (· ||| ·) 0))

def forces (h : Host) (rl cl : Leaves) (i j : WordType) : Bool :=
  let cols := privateMask h rl i
  (positions (privateMask h cl j)).all (fun u => (rowMask h u &&& cols) == cols)

def crossings (h : Host) (rl cl : Leaves) : Nat :=
  (rl.map fun i => (cl.filter (forces h rl cl i)).length).sum

def testFrame (h : Host) (rl cl : Leaves) : Bool :=
  let t := rl.length + cl.length
  let score := 17*t+residual h rl cl
  decide (t ≤ 10) && (decide (score ≤ 158) || decide (score ≤ 158 + crossings h rl cl))

/-- Branch over every subset whose current prefix passes `ok`. -/
def visit {α : Type*} (ok test : List α → Bool) (chosen : List α) : List α → Bool
  | [] => test chosen
  | i::tail => visit ok test chosen tail &&
      (!ok (i::chosen) || visit ok test (i::chosen) tail)

def allTypes : Leaves := List.finRange 27

def available (h : Host) (rl : Leaves) : Leaves :=
  let forbidden := unionMask h rl
  allTypes.filter (fun j => !(forbidden.testBit j.val))

/-- Both leaves have private neighbors and no two opposite leaves are adjacent. -/
def checkCols (h : Host) (rl : Leaves) : Bool :=
  visit (eligible h) (testFrame h rl) [] (available h rl)

def checkHost (h : Host) : Bool := visit (eligible h) (checkCols h) [] allTypes

/-- Every selection made by `p` reaches its leaf if each of its prefixes is legal. -/
theorem visit_complete {α : Type*} (ok test : List α → Bool) (p : α → Bool)
    (hered : ∀ xs : List α, (∀ x ∈ xs, p x = true) → ok xs = true)
    (chosen todo : List α) (mem : ∀ x ∈ chosen, p x = true)
    (check : visit ok test chosen todo = true) :
    test ((todo.filter p).reverse ++ chosen) = true := by
  induction todo generalizing chosen with
  | nil => simpa [visit] using check
  | cons v tail ih =>
    simp only [visit, Bool.and_eq_true] at check
    cases hv : p v with
    | false => simpa [hv] using ih chosen mem check.1
    | true =>
      have members : ∀ x ∈ v::chosen, p x = true := by
        simpa [hv] using mem
      have valid := hered (v::chosen) members
      have next := ih (v::chosen) members (by simpa [valid] using check.2)
      simpa [hv, List.append_assoc] using next

/-- Semantic leaves can be read in their canonical order for the certificate. -/
def selected (p : WordType → Bool) : Leaves := (allTypes.filter p).reverse

theorem checkHost_sound (h : Host) (pr pc : WordType → Bool)
    (rowSubsets : ∀ xs : Leaves, (∀ i ∈ xs, pr i = true) → eligible h xs = true)
    (colSubsets : ∀ xs : Leaves, (∀ j ∈ xs, pc j = true) → eligible h xs = true)
    (apart : ∀ j, pc j = true → (unionMask h (selected pr)).testBit j.val = false)
    (verdict : checkHost h = true) : testFrame h (selected pr) (selected pc) = true := by
  have outer := visit_complete (eligible h) (checkCols h) pr rowSubsets [] allTypes
    (by simp) verdict
  have outer' : checkCols h (selected pr) = true := by simpa [selected] using outer
  have inner := visit_complete (eligible h) (testFrame h (selected pr)) pc colSubsets []
    (available h (selected pr)) (by simp) outer'
  have filt : (available h (selected pr)).filter pc = allTypes.filter pc := by
    unfold available
    rw [List.filter_filter]
    apply List.filter_congr
    intro i _
    cases hi : pc i with
    | false => simp
    | true => simp [apart i hi]
  rw [filt] at inner
  simpa only [selected, List.append_nil] using inner

end GainFinite
