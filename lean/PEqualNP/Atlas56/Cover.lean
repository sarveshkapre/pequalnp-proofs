import PEqualNP.Atlas56.Data

namespace Atlas56
structure Entry where
  pattern : Pat
  ok : Nat
  ex : Nat

def entry (p : Pat) : Entry := ⟨p, good p, exc p⟩

-- A branch selects or skips each possible column. Selection intersects the
-- surviving template bitsets. Zero budget means exactly six were selected.
def check : Nat → List Entry → Nat → Nat → Bool
  | 0, _, g, e => (g != 0) || (e != 0)
  | _+1, [], g, _ => g != 0
  | k+1, x::xs, g, e =>
      check k xs (g &&& x.ok) (e &&& x.ex) && check (k+1) xs g e
termination_by structural _ xs _ _ => xs

def finishG (g : Nat) (xs : List Entry) := xs.foldl (fun a x => a &&& x.ok) g
def finishE (e : Nat) (xs : List Entry) := xs.foldl (fun a x => a &&& x.ex) e

theorem check_sound (xs : List Entry) (k g e : Nat) (ys : List Entry)
    (sub : ys.Sublist xs) (le : ys.length ≤ k) (h : check k xs g e = true) :
    finishG g ys ≠ 0 ∨ (ys.length = k ∧ finishE e ys ≠ 0) := by
  induction xs generalizing k g e ys with
  | nil =>
    have hy : ys = [] := List.sublist_nil.mp sub
    subst ys
    cases k <;> simpa [check,finishG,finishE] using h
  | cons x xs ih =>
    cases k with
    | zero =>
      have hy : ys = [] := List.length_eq_zero_iff.mp (by omega)
      subst ys
      simpa [check,finishG,finishE] using h
    | succ k =>
      simp only [check] at h
      have hh := Bool.and_eq_true_iff.mp h
      cases sub with
      | cons _ sub => exact ih _ _ _ _ sub le hh.2
      | cons_cons _ sub =>
        have q := ih k (g &&& x.ok) (e &&& x.ex) _ sub (by simpa using le) hh.1
        simpa [finishG,finishE] using q

theorem fold_bits (xs : List Entry) (f : Entry → Nat) (g n : Nat)
    (h : (xs.foldl (fun a x => a &&& f x) g).testBit n = true) :
    g.testBit n = true ∧ ∀ x ∈ xs, (f x).testBit n = true := by
  induction xs generalizing g with
  | nil => simpa using h
  | cons x xs ih =>
    obtain ⟨h₁,h₂⟩ := ih (g &&& f x) h
    rw [Nat.testBit_and, Bool.and_eq_true] at h₁
    exact ⟨h₁.1, by simpa using And.intro h₁.2 h₂⟩

end Atlas56
