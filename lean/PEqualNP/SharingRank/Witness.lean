import Mathlib.Tactic

/-! A fooling set against any flat formula, with an explicit embedding at every budget. -/
namespace SharingRank.Witness
open Set
open scoped Classical

abbrev Tail (t : Nat) := Fin t → Bool × Bool
abbrev Word (t : Nat) := BitVec 6 × Tail t
abbrev Index (t : Nat) := Fin 8 ⊕ (Fin t × Bool)
def common (v : BitVec 6) := v.getLsbD 0 || v.getLsbD 1
def core (v : BitVec 6) := (v.getLsbD 2 || (v.getLsbD 3 && common v)) &&
  (v.getLsbD 4 || (v.getLsbD 5 && common v))

def zero (x y : Word t) : Prop := core (x.1 &&& y.1) = true ∧ ∀ i,
  ((x.2 i).1 && (y.2 i).1) = true ∨
    (((x.2 i).2 && (y.2 i).2) = true ∧ common (x.1 &&& y.1) = true)

def left : Fin 8 → BitVec 6 := ![61,57,59,27,62,58,47,53]
def right : Fin 8 → BitVec 6 := ![46,62,54,47,45,61,30,57]

private theorem seed : (∀ i, common (left i) = true ∧ common (right i) = true ∧
    core (left i) = true ∧ core (right i) = true ∧ core (left i &&& right i) = false) ∧
    ∀ i j, i ≠ j → core (left i &&& right j) = true ∨ core (left j &&& right i) = true := by
  decide +kernel

def whole : Tail t := fun _ => (true,true)
def mark (i : Fin t) (b : Bool) : Tail t := fun j => if i = j then (b,!b) else (true,true)
def anchor : Word t := (-1,whole)
def row : Index t → Word t
  | .inl i => (left i,whole)
  | .inr (i,b) => (-1,mark i b)
def col : Index t → Word t
  | .inl i => (right i,whole)
  | .inr (i,b) => (-1,mark i (!b))

@[simp] private theorem maskR : ∀ x : BitVec 6, (x &&& 63#6) = x := by decide +kernel
@[simp] private theorem maskL : ∀ x : BitVec 6, (63#6 &&& x) = x := by decide +kernel
@[simp] private theorem common_all : common 63#6 = true := by decide
@[simp] private theorem core_all : core 63#6 = true := by decide

theorem anchors (i : Index t) : zero (row i) anchor ∧ zero anchor (col i) := by
  cases i with
  | inl i => simp [zero,row,col,anchor,whole,(seed.1 i).1,(seed.1 i).2.1,
                     (seed.1 i).2.2.1,(seed.1 i).2.2.2.1]
  | inr v =>
    obtain ⟨i,b⟩ := v
    constructor <;> cases b <;> simp [zero,row,col,anchor,whole,mark] <;>
      intro j <;> by_cases h : i = j <;> simp [h]

theorem missing (i : Index t) : ¬ zero (row i) (col i) := by
  cases i with
  | inl i => simp [zero,row,col,(seed.1 i).2.2.2.2]
  | inr v =>
    obtain ⟨i,b⟩ := v
    intro h
    have impossible := h.2 i
    cases b <;> simp [row,col,mark] at impossible

theorem crossed (i j : Index t) (ne : i ≠ j) : zero (row i) (col j) ∨ zero (row j) (col i) := by
  cases i with
  | inl i =>
    cases j with
    | inl j => simpa [zero,row,col,whole] using seed.2 i j (by simpa using ne)
    | inr v =>
      obtain ⟨j,b⟩ := v
      left
      cases b <;> simp [zero,row,col,whole,mark,(seed.1 i).1,(seed.1 i).2.2.1] <;>
        intro l <;> by_cases h : j = l <;> simp [h]
  | inr u =>
    obtain ⟨i,b⟩ := u
    cases j with
    | inl j =>
      right
      cases b <;> simp [zero,row,col,whole,mark,(seed.1 j).1,(seed.1 j).2.2.1] <;>
        intro l <;> by_cases h : i = l <;> simp [h]
    | inr v =>
      obtain ⟨j,c⟩ := v
      left
      refine ⟨by simp [row,col],?_⟩
      intro l
      by_cases e : i = j
      · subst j
        have diff : b ≠ c := fun z => ne (by rw [z])
        cases b <;> cases c <;> by_cases h : i = l <;> simp_all [row,col,mark]
      · by_cases hi : i = l <;> by_cases hj : j = l <;> cases b <;> cases c <;>
          simp_all [row,col,mark,common_all]

/-- Two missed cells of the same orientation force both cross cells to be missed. -/
theorem flat_bound {X Y I : Type} [Fintype I] {k : Nat} (z : X → Y → Prop)
    (r : I → X) (c : I → Y) (u : X) (v : Y)
    (alive : ∀ i, z (r i) v ∧ z u (c i)) (miss : ∀ i, ¬ z (r i) (c i))
    (cross : ∀ i j, i ≠ j → z (r i) (c j) ∨ z (r j) (c i))
    (clipR : Set X) (clipC : Set Y) (a b : Fin k → Set X) (s t : Fin k → Set Y)
    (rep : ∀ x y, z x y ↔ x ∈ clipR ∧ y ∈ clipC ∧
      ∀ j, (x ∈ a j ∧ y ∈ s j) ∨ (x ∈ b j ∧ y ∈ t j)) : Fintype.card I ≤ 2*k := by
  classical
  have chooseGate (i : I) : ∃ j, ¬ ((r i ∈ a j ∧ c i ∈ s j) ∨ (r i ∈ b j ∧ c i ∈ t j)) := by
    by_contra! h
    exact miss i ((rep _ _).mpr ⟨((rep _ _).mp (alive i).1).1,((rep _ _).mp (alive i).2).2.1,h⟩)
  choose g bad using chooseGate
  let code (i : I) : Fin k × Bool := (g i, decide (r i ∈ a (g i)))
  have inj : Function.Injective code := by
    intro i j same
    have gate : g j = g i := (congrArg Prod.fst same).symm
    have side : (r i ∈ a (g i)) ↔ (r j ∈ a (g i)) := by
      have eq := congrArg Prod.snd same
      change decide (r i ∈ a (g i)) = decide (r j ∈ a (g j)) at eq
      simpa only [gate,decide_eq_decide] using eq
    by_contra ne
    have offI := bad i
    have offJ := bad j
    rw [gate] at offJ
    have ri := ((rep _ _).mp (alive i).1).2.2 (g i)
    have rj := ((rep _ _).mp (alive j).1).2.2 (g i)
    have ci := ((rep _ _).mp (alive i).2).2.2 (g i)
    have cj := ((rep _ _).mp (alive j).2).2.2 (g i)
    have each : ∀ h : I, r h ∈ a (g i) ∨ r h ∈ b (g i) := fun h =>
      (((rep _ _).mp (alive h).1).2.2 (g i)).elim (fun e => Or.inl e.1) (fun e => Or.inr e.1)
    have eachC : ∀ h : I, c h ∈ s (g i) ∨ c h ∈ t (g i) := fun h =>
      (((rep _ _).mp (alive h).2).2.2 (g i)).elim (fun e => Or.inl e.2) (fun e => Or.inr e.2)
    have pickI := each i
    have pickJ := each j
    have pickCI := eachC i
    have pickCJ := eachC j
    rcases cross i j ne with yes | yes <;>
      have hit := ((rep _ _).mp yes).2.2 (g i) <;>
      clear ri rj ci cj each eachC cross alive rep <;> tauto
  simpa [Nat.mul_comm] using Fintype.card_le_of_injective code inj

theorem no_flat {t : Nat} (clipR clipC : Set (Word t))
    (a b s u : Fin (t+3) → Set (Word t)) :
    ¬ (∀ x y, zero x y ↔ x ∈ clipR ∧ y ∈ clipC ∧
      ∀ j, (x ∈ a j ∧ y ∈ s j) ∨ (x ∈ b j ∧ y ∈ u j)) := by
  intro rep
  have h := flat_bound zero row col anchor anchor anchors missing crossed clipR clipC a b s u rep
  simp [Index,Fintype.card_sum,Fintype.card_prod] at h
  omega
end SharingRank.Witness
