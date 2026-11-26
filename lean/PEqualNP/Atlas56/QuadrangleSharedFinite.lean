import PEqualNP.Atlas56.QuadrangleSharedReduction

/-!
# Checked finite decision trees for the quadrangle obstruction

A tree splits only actual row/column membership bits. Its leaf checker is
parameterized here; the soundness theorem propagates checked geometric leaf
facts to every full assignment, including branches not enumerated by a solver.
-/

namespace QuadrangleSharedFinite

abbrev Variable := Fin 22
abbrev Assignment := Variable → Bool
abbrev State := Variable → Option Bool

def Matches (s : State) (v : Assignment) : Prop :=
  ∀ i b, s i = some b → v i = b

def empty : State := fun _ => none

def assign (s : State) (i : Variable) (b : Bool) : State :=
  Function.update s i (some b)

theorem matches_assign {s : State} {v : Assignment} (hs : Matches s v)
    (i : Variable) (b : Bool) (hi : v i = b) : Matches (assign s i b) v := by
  intro j c hj
  by_cases hji : j = i
  · subst j
    simp only [assign, Function.update_self, Option.some.injEq] at hj
    exact hi.trans hj
  · have hj' : s j = some c := by simpa [assign, hji] using hj
    exact hs j c hj'

theorem matches_empty (v : Assignment) : Matches empty v := by
  intro i b h
  cases h

inductive Tree (Tag : Type) where
  | leaf (tag : Tag)
  | split (i : Variable) (lo hi : Tree Tag)

def check {Tag : Type} (leafCheck : State → Tag → Bool) (s : State) : Tree Tag → Bool
  | .leaf tag => leafCheck s tag
  | .split i lo hi => check leafCheck (assign s i false) lo &&
      check leafCheck (assign s i true) hi

theorem check_split {Tag : Type} (leafCheck : State → Tag → Bool)
    (s : State) (i : Variable) (lo hi : Tree Tag)
    (hlo : check leafCheck (assign s i false) lo = true)
    (hhi : check leafCheck (assign s i true) hi = true) :
    check leafCheck s (.split i lo hi) = true :=
  Bool.and_eq_true_iff.mpr ⟨hlo, hhi⟩

/-- Verified geometric leaves and exhaustive binary branches imply the result
for every assignment compatible with the initial state. -/
theorem check_sound {Tag : Type} (leafCheck : State → Tag → Bool)
    (result : Assignment → Prop)
    (leafSound : ∀ s tag, leafCheck s tag = true →
      ∀ v, Matches s v → result v)
    (tree : Tree Tag) : ∀ s, check leafCheck s tree = true →
      ∀ v, Matches s v → result v := by
  induction tree with
  | leaf tag =>
    intro s h v hs
    exact leafSound s tag h v hs
  | split i lo hi ihlo ihhi =>
    intro s h v hs
    obtain ⟨hlo, hhi⟩ := Bool.and_eq_true_iff.mp h
    cases hvi : v i with
    | false => exact ihlo _ hlo v (matches_assign hs i false hvi)
    | true => exact ihhi _ hhi v (matches_assign hs i true hvi)

theorem check_empty_sound {Tag : Type} (leafCheck : State → Tag → Bool)
    (result : Assignment → Prop)
    (leafSound : ∀ s tag, leafCheck s tag = true →
      ∀ v, Matches s v → result v)
    (tree : Tree Tag) (h : check leafCheck empty tree = true) :
    ∀ v, result v :=
  fun v => check_sound leafCheck result leafSound tree empty h v (matches_empty v)

open Set TwoIntersections ThreeIntersectionsQuadrangle QuadranglePartialFooling
open QuadrangleSharedReduction

def lower (s : State) : Assignment := fun i => (s i).getD false
def upper (s : State) : Assignment := fun i => (s i).getD true

theorem lower_true {s : State} {v : Assignment} (hs : Matches s v)
    {i : Variable} (h : lower s i = true) : v i = true := by
  cases hsi : s i with
  | none => simp [lower, hsi] at h
  | some b =>
    have hb : b = true := by simpa [lower, hsi] using h
    exact (hs i b hsi).trans hb

theorem upper_true {s : State} {v : Assignment} (hs : Matches s v)
    {i : Variable} (h : v i = true) : upper s i = true := by
  cases hsi : s i with
  | none => simp [upper, hsi]
  | some b =>
    have hb : b = true := (hs i b hsi).symm.trans h
    simp [upper, hsi, hb]

def rowVar (side : Bool) (r : Fin 5) : Variable :=
  if side then Fin.natAdd 11 (Fin.castAdd 6 r) else Fin.castAdd 11 (Fin.castAdd 6 r)

def colVar (side : Bool) (c : Fin 6) : Variable :=
  if side then Fin.natAdd 11 (Fin.natAdd 5 c) else Fin.castAdd 11 (Fin.natAdd 5 c)

def rectBool (v : Assignment) (side : Bool) (p : Cell) : Bool :=
  v (rowVar side p.1) && v (colVar side p.2)

def rectSet (v : Assignment) (side : Bool) : Set Cell :=
  {p | rectBool v side p = true}

theorem rectSet_rectangle (v : Assignment) (side : Bool) : Rectangle (rectSet v side) := by
  refine ⟨{r | v (rowVar side r) = true}, {c | v (colVar side c) = true}, ?_⟩
  ext p
  simp [rectSet, rectBool]

theorem lower_rect {s : State} {v : Assignment} (hs : Matches s v) (side : Bool) :
    rectSet (lower s) side ⊆ rectSet v side := by
  intro p hp
  obtain ⟨hr, hc⟩ := Bool.and_eq_true_iff.mp hp
  exact Bool.and_eq_true_iff.mpr ⟨lower_true hs hr, lower_true hs hc⟩

theorem upper_rect {s : State} {v : Assignment} (hs : Matches s v) (side : Bool) :
    rectSet v side ⊆ rectSet (upper s) side := by
  intro p hp
  obtain ⟨hr, hc⟩ := Bool.and_eq_true_iff.mp hp
  exact Bool.and_eq_true_iff.mpr ⟨upper_true hs hr, upper_true hs hc⟩

def zeroBool (p : Cell) : Bool := !(mask p.1).testBit p.2.val

theorem zeroBool_true (p : Cell) : zeroBool p = true ↔ p ∈ zero := by
  simp [zeroBool, zero, graph]

/-- Two positive cells force a row/column crossing into a rectangle hull. -/
structure HullWitness where
  col : Fin 6
  row : Fin 5

def hullCheck (s : State) (side : Bool) (p : Cell) (w : HullWitness) : Bool :=
  zeroBool (p.1, w.col) && !rectBool (upper s) side (p.1, w.col) &&
  zeroBool (w.row, p.2) && !rectBool (upper s) side (w.row, p.2)

theorem hullCheck_sound {s : State} {side : Bool} {p : Cell} {w : HullWitness}
    (h : hullCheck s side p w = true) :
    p ∈ leftHull zero (rectSet (upper s) side) := by
  simp only [hullCheck, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h1, hn1⟩, h2⟩, hn2⟩ := h
  have hx : (p.1, w.col) ∈ zero \ rectSet (upper s) side :=
    ⟨(zeroBool_true _).mp h1, by simp only [rectSet, Set.mem_ofPred_eq, hn1]; decide⟩
  have hy : (w.row, p.2) ∈ zero \ rectSet (upper s) side :=
    ⟨(zeroBool_true _).mp h2, by simp only [rectSet, Set.mem_ofPred_eq, hn2]; decide⟩
  exact ⟨⟨(p.1, w.col), hx, rfl⟩, ⟨(w.row, p.2), hy, rfl⟩⟩

inductive ArmWitness where
  | left (f : HullWitness)
  | right (d : HullWitness)
  | both (d f : HullWitness)

def armCheck (s : State) (p : Cell) : ArmWitness → Bool
  | .left f => rectBool (lower s) false p && hullCheck s true p f
  | .right d => hullCheck s false p d && rectBool (lower s) true p
  | .both d f => hullCheck s false p d && hullCheck s true p f

def interval (s : State) : Set Cell :=
  intervalForbidden zero (rectSet (lower s) false) (rectSet (upper s) false)
    (rectSet (lower s) true) (rectSet (upper s) true)

theorem armCheck_sound {s : State} {p : Cell} {w : ArmWitness}
    (hz : p ∉ zero) (h : armCheck s p w = true) : p ∈ interval s := by
  refine ⟨hz, ?_⟩
  cases w with
  | left f =>
    obtain ⟨hc, hf⟩ := Bool.and_eq_true_iff.mp h
    exact Or.inl (Or.inl ⟨hc, hullCheck_sound hf⟩)
  | right d =>
    obtain ⟨hd, he⟩ := Bool.and_eq_true_iff.mp h
    exact Or.inl (Or.inr ⟨hullCheck_sound hd, he⟩)
  | both d f =>
    obtain ⟨hd, hf⟩ := Bool.and_eq_true_iff.mp h
    exact Or.inr ⟨hullCheck_sound hd, hullCheck_sound hf⟩

structure CrossWitness where
  reverse : Bool
  arm : ArmWitness

def crossCell (p q : Cell) (reverse : Bool) : Cell :=
  if reverse then (q.1, p.2) else (p.1, q.2)

def crossCheck (s : State) (p q : Cell) (w : CrossWitness) : Bool :=
  let x := crossCell p q w.reverse
  !zeroBool x && armCheck s x w.arm

theorem crossCheck_sound {s : State} {p q : Cell} {w : CrossWitness}
    (h : crossCheck s p q w = true) :
    (p.1, q.2) ∈ interval s ∨ (q.1, p.2) ∈ interval s := by
  obtain ⟨hz, ha⟩ := Bool.and_eq_true_iff.mp h
  have hn : crossCell p q w.reverse ∉ zero := by
    intro hmem
    have htrue := (zeroBool_true _).mpr hmem
    simp only [htrue, Bool.not_true] at hz
    contradiction
  have hi := armCheck_sound hn ha
  cases hr : w.reverse
  · exact Or.inl (by simpa [crossCell, hr] using hi)
  · exact Or.inr (by simpa [crossCell, hr] using hi)

def positiveCheck (s : State) (p : Cell) : Bool :=
  zeroBool p && !(rectBool (upper s) false p && rectBool (upper s) true p)

theorem positiveCheck_sound {s : State} {p : Cell}
    (h : positiveCheck s p = true) :
    p ∈ zero \ (rectSet (upper s) false ∩ rectSet (upper s) true) := by
  obtain ⟨hz, hn⟩ := Bool.and_eq_true_iff.mp h
  refine ⟨(zeroBool_true _).mp hz, ?_⟩
  rintro ⟨hc, he⟩
  have hboth := Bool.and_eq_true_iff.mpr ⟨hc, he⟩
  simp only [hboth, Bool.not_true] at hn
  contradiction

inductive Leaf where
  | bad (p : Cell)
  | fool (p q r : Cell) (pq pr qr : CrossWitness)

def leafCheck (s : State) : Leaf → Bool
  | .bad p => !zeroBool p && rectBool (lower s) false p && rectBool (lower s) true p
  | .fool p q r pq pr qr =>
      positiveCheck s p && positiveCheck s q && positiveCheck s r &&
      crossCheck s p q pq && crossCheck s p r pr && crossCheck s q r qr

def Result (v : Assignment) : Prop :=
  rectSet v false ∩ rectSet v true ⊆ zero →
    ∃ w : Fin 3 → Cell,
      PartialFooling (zero \ (rectSet v false ∩ rectSet v true))
        (forbidden zero (rectSet v false) (rectSet v true)) w

theorem leaf_sound (s : State) (tag : Leaf) (h : leafCheck s tag = true)
    (v : Assignment) (hv : Matches s v) : Result v := by
  intro hi
  cases tag with
  | bad p =>
    simp only [leafCheck, Bool.and_eq_true] at h
    obtain ⟨⟨hz, hc⟩, he⟩ := h
    have hp := hi ⟨lower_rect hv false hc, lower_rect hv true he⟩
    have ht := (zeroBool_true p).mpr hp
    simp only [ht, Bool.not_true] at hz
    contradiction
  | fool p q r pq pr qr =>
    simp only [leafCheck, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨hp, hq⟩, hr⟩, hpq⟩, hpr⟩, hqr⟩ := h
    let w : Fin 3 → Cell := ![p, q, r]
    have hw : PartialFooling
        (zero \ (rectSet (upper s) false ∩ rectSet (upper s) true)) (interval s) w := by
      refine ⟨?_, ?_⟩
      · intro i
        fin_cases i
        · exact positiveCheck_sound hp
        · exact positiveCheck_sound hq
        · exact positiveCheck_sound hr
      · intro i j hij
        have hpq' := crossCheck_sound hpq
        have hpr' := crossCheck_sound hpr
        have hqr' := crossCheck_sound hqr
        fin_cases i <;> fin_cases j <;> simp [w] at hij ⊢
        · exact hpq'
        · exact hpr'
        · exact hpq'.symm
        · exact hqr'
        · exact hpr'.symm
        · exact hqr'.symm
    exact ⟨w, interval_partial_fooling (lower_rect hv false) (upper_rect hv false)
      (lower_rect hv true) (upper_rect hv true) hw⟩

noncomputable def encode (cr er : Set (Fin 5)) (cc ec : Set (Fin 6)) : Assignment := by
  classical
  intro i
  exact Fin.addCases (m := 11) (n := 11) (motive := fun _ => Bool)
    (fun j => Fin.addCases (m := 5) (n := 6) (motive := fun _ => Bool)
      (fun r => decide (r ∈ cr)) (fun c => decide (c ∈ cc)) j)
    (fun j => Fin.addCases (m := 5) (n := 6) (motive := fun _ => Bool)
      (fun r => decide (r ∈ er)) (fun c => decide (c ∈ ec)) j) i

theorem encode_false (cr er : Set (Fin 5)) (cc ec : Set (Fin 6)) :
    rectSet (encode cr er cc ec) false = cr ×ˢ cc := by
  classical
  ext p
  simp [rectSet, rectBool, rowVar, colVar, encode]

theorem encode_true (cr er : Set (Fin 5)) (cc ec : Set (Fin 6)) :
    rectSet (encode cr er cc ec) true = er ×ˢ ec := by
  classical
  ext p
  simp [rectSet, rectBool, rowVar, colVar, encode, -Fin.natAdd_eq_addNat]

/-- A checked finite geometric tree supplies the obstruction for arbitrary
rectangles, including empty rows/columns and all possible overlaps. -/
theorem obstruction_of_checked_tree (tree : Tree Leaf)
    (h : check leafCheck empty tree = true) :
    ∀ c e : Set Cell, Rectangle c → Rectangle e → c ∩ e ⊆ zero →
      ∃ w : Fin 3 → Cell, PartialFooling (zero \ (c ∩ e)) (forbidden zero c e) w := by
  intro c e hc he hi
  obtain ⟨cr, cc, rfl⟩ := hc
  obtain ⟨er, ec, rfl⟩ := he
  have checked := check_empty_sound leafCheck Result leaf_sound tree h (encode cr er cc ec)
  unfold Result at checked
  rw [encode_false, encode_true] at checked
  exact checked hi

theorem no_shared_diamond_of_checked_tree (tree : Tree Leaf)
    (h : check leafCheck empty tree = true) :
    ¬ ∃ a b c d e f : Set Cell,
      Rectangle a ∧ Rectangle b ∧ Rectangle c ∧ Rectangle d ∧
      Rectangle e ∧ Rectangle f ∧
      zero = (c ∪ (d ∩ (a ∪ b))) ∩ (e ∪ (f ∩ (a ∪ b))) :=
  no_diamond_of_partial_fooling (obstruction_of_checked_tree tree h)

#print axioms check_sound
#print axioms check_empty_sound
#print axioms hullCheck_sound
#print axioms leaf_sound
#print axioms obstruction_of_checked_tree
#print axioms no_shared_diamond_of_checked_tree
end QuadrangleSharedFinite
