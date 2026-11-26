import Mathlib

namespace FixedBudgetGain

/-- Five centers, five kinds of private neighbor, and the unused type. -/
inductive Site where
  | center (i : Fin 5)
  | leaf (i : Fin 5)
  | unused
  deriving DecidableEq, Fintype

def cross (i j : Fin 5) : Bool :=
  if i = 4 then decide (j ≠ 4) else decide (j = i ∨ j = 4)

def wanted : Site → Site → Bool
  | .center i, .center j => cross i j
  | .center i, .leaf j | .leaf i, .center j => decide (i = j)
  | _, _ => false

def pointWord : Site → Nat
  | .center i => (![24,20,18,17,47] : Fin 5 → Nat) i
  | .leaf i => (![8,4,2,1,16] : Fin 5 → Nat) i
  | .unused => 0

def lineWord : Site → Nat
  | .center i => (![20,24,17,18,47] : Fin 5 → Nat) i
  | .leaf i => (![4,8,1,2,16] : Fin 5 → Nat) i
  | .unused => 0

/-- Each raw bit is a union of a point star selection and a line star selection. -/
def three (x y : Nat) : Bool :=
  let w := x ||| y
  let a := w.testBit 0 && w.testBit 1
  let b := w.testBit 2 && w.testBit 3
  w.testBit 4 && (w.testBit 5 || a || b)

theorem table : ∀ a b : Site, three (pointWord a) (lineWord b) = wanted a b := by decide

theorem sharedLine : ∀ a b : Fin 5, ∃ j : Fin 5, cross a j = true ∧ cross b j = true := by decide
theorem sharedPoint : ∀ a b : Fin 5, ∃ i : Fin 5, cross i a = true ∧ cross i b = true := by decide

variable {P L : Type*}
def NoSquare (I : P → L → Prop) : Prop :=
  ∀ p r l m, I p l → I p m → I r l → I r m → p = r ∨ l = m

noncomputable def site {V : Type*} (v : Fin 5 → V) (neighbor : V → Fin 5 → Prop) (x : V) : Site :=
  open Classical in
  if h : ∃ i, x = v i then .center h.choose
  else if h : ∃ i, neighbor x i then .leaf h.choose
  else .unused

theorem center_iff {V : Type*} (v : Fin 5 → V) (hv : Function.Injective v)
    (n : V → Fin 5 → Prop) (x : V) (i : Fin 5) :
    site v n x = .center i ↔ x = v i := by
  classical
  unfold site
  split_ifs with h h'
  · constructor
    · intro eq
      cases eq
      exact h.choose_spec
    · intro e
      have a := hv (h.choose_spec.symm.trans e)
      rw [a]
  · simp; exact fun e => h ⟨i,e⟩
  · simp; exact fun e => h ⟨i,e⟩

theorem leaf_iff {V : Type*} (v : Fin 5 → V) (n : V → Fin 5 → Prop) (x : V)
    (outside : ¬ ∃ i, x = v i) (unique : ∀ i j, n x i → n x j → i = j) (i : Fin 5) :
    site v n x = .leaf i ↔ n x i := by
  classical
  rw [site, dite_eq_right outside]
  by_cases h : ∃ j, n x j
  · rw [dite_eq_left h]
    constructor
    · intro e
      cases e
      exact h.choose_spec
    · intro e
      rw [unique _ _ h.choose_spec e]
  · rw [dite_eq_right h]
    simp; exact fun e => h ⟨i,e⟩

/-- On any square-free board containing the prescribed five points and five
lines, three intersections compute exactly the incidences touching those centers. -/
theorem recognizes {I : P → L → Prop} (sq : NoSquare I)
    (p : Fin 5 → P) (l : Fin 5 → L) (hp : Function.Injective p) (hl : Function.Injective l)
    (frame : ∀ i j, I (p i) (l j) ↔ cross i j = true) (x : P) (y : L) :
    three (pointWord (site p (fun z j => I z (l j)) x))
          (lineWord (site l (fun z i => I (p i) z) y)) = true ↔
    I x y ∧ ((∃ i, x = p i) ∨ (∃ j, y = l j)) := by
  classical
  rw [table]
  let a := site p (fun z j => I z (l j)) x
  let b := site l (fun z i => I (p i) z) y
  change wanted a b = true ↔ _
  have ac := center_iff p hp (fun z j => I z (l j)) x
  have bc := center_iff l hl (fun z i => I (p i) z) y
  change ∀ i, a = .center i ↔ _ at ac
  change ∀ j, b = .center j ↔ _ at bc
  have al (o : ¬ ∃ i, x = p i) (j : Fin 5) : a = .leaf j ↔ I x (l j) := by
    apply leaf_iff _ _ _ o
    intro i k hi hk
    obtain ⟨r,hr,hs⟩ := sharedPoint i k
    rcases sq x (p r) (l i) (l k) hi hk ((frame ..).mpr hr) ((frame ..).mpr hs) with e|e
    · exact (o ⟨r,e⟩).elim
    · exact hl e
  have bl (o : ¬ ∃ j, y = l j) (i : Fin 5) : b = .leaf i ↔ I (p i) y := by
    apply leaf_iff _ _ _ o
    intro j k hj hk
    obtain ⟨r,hr,hs⟩ := sharedLine j k
    rcases sq (p j) (p k) y (l r) hj ((frame ..).mpr hr) hk ((frame ..).mpr hs) with e|e
    · exact hp e
    · exact (o ⟨r,e⟩).elim
  by_cases ox : ∃ i, x = p i
  · obtain ⟨i,hi⟩ := ox
    rw [(ac i).mpr hi]
    by_cases oy : ∃ j, y = l j
    · obtain ⟨j,hj⟩ := oy
      rw [(bc j).mpr hj]
      simp [wanted,hi,hj,frame]
    · have e : wanted (.center i) b = true ↔ b = .leaf i := by
        cases h : b with
        | center j => exact (oy ⟨j,(bc j).mp h⟩).elim
        | leaf j => simp [wanted,eq_comm]
        | unused => simp [wanted]
      rw [e,bl oy,hi]; simp
  · by_cases oy : ∃ j, y = l j
    · obtain ⟨j,hj⟩ := oy
      rw [(bc j).mpr hj]
      have e : wanted a (.center j) = true ↔ a = .leaf j := by
        cases h : a with
        | center i => exact (ox ⟨i,(ac i).mp h⟩).elim
        | leaf i => simp [wanted]
        | unused => simp [wanted]
      rw [e,al ox,hj]; simp
    · have na : ∀ i, a ≠ .center i := fun i h => ox ⟨i,(ac i).mp h⟩
      have nb : ∀ j, b ≠ .center j := fun j h => oy ⟨j,(bc j).mp h⟩
      cases ha : a <;> cases hb : b <;> simp_all [wanted]

#print axioms recognizes
end FixedBudgetGain
