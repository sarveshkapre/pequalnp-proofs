import PEqualNP.Defs

/- Monotone formulas and routing to leaf occurrences. -/
namespace PEqualNP.Outside.FormulaGap_aux

open PEqualNP.MetaComplexity
abbrev F (n : Nat) := DMFormula n

def positive {n} (f : F n) : Prop :=
  DMFormula.rec (motive := fun _ => Prop) (fun _ b => b = true)
    (fun _ _ l r => l ∧ r) (fun _ _ l r => l ∧ r) f

-- Paths distinguish different occurrences of the same input.
def Tip {n} : F n → Type
  | .lit _ _ => Unit
  | .and l r | .or l r => Sum (Tip l) (Tip r)

def tag {n} : (f : F n) → Tip f → Fin n
  | .lit i _, _ => i
  | .and l _, .inl x | .or l _, .inl x => tag l x
  | .and _ r, .inr x | .or _ r, .inr x => tag r x

def reads {n} : F n → Fin n → Nat
  | .lit j _, i => if j = i then 1 else 0
  | .and l r, i | .or l r, i => reads l i + reads r i

theorem present {n} {f : F n} (t : Tip f) : 0 < reads f (tag f t) := by
  induction f with
  | lit => simp [reads, tag]
  | and l r il ir | or l r il ir =>
    cases t with
    | inl x => simpa only [tag, reads] using Nat.add_pos_left (il x) _
    | inr x => simpa only [tag, reads] using Nat.add_pos_right _ (ir x)

theorem uniqueTip {n} {f : F n} {i : Fin n} (h : reads f i ≤ 1)
    (x y : Tip f) (hx : tag f x = i) (hy : tag f y = i) : x = y := by
  induction f with
  | lit => cases x; cases y; rfl
  | and l r il ir | or l r il ir =>
    simp only [reads] at h
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (il (by omega) x y hx hy)
      | inr y =>
        have a := present x
        have b := present y
        change tag l x = i at hx
        change tag r y = i at hy
        rw [hx] at a
        rw [hy] at b
        omega
    | inr x =>
      cases y with
      | inl y =>
        have a := present x
        have b := present y
        change tag r x = i at hx
        change tag l y = i at hy
        rw [hx] at a
        rw [hy] at b
        omega
      | inr y => exact congrArg Sum.inr (ir (by omega) x y hx hy)

theorem sumReads {n} (f : F n) : (∑ i, reads f i) = f.leaves := by
  induction f with
  | lit j b => simp [reads, DMFormula.leaves]
  | and l r il ir | or l r il ir => simp [reads, DMFormula.leaves, Finset.sum_add_distrib, il, ir]

abbrev Input (n : Nat) := Fin n → Bool

-- At OR, the positive input chooses a true branch. At AND, the negative input chooses a false branch.
def route {n} : (f : F n) → Input n → Input n → Tip f
  | .lit _ _, _, _ => ()
  | .or l r, a, b => if l.eval a then .inl (route l a b) else .inr (route r a b)
  | .and l r, a, b => if l.eval b then .inr (route r a b) else .inl (route l a b)

theorem separates {n} {f : F n} (h : positive f) (a b : Input n)
    (ha : f.eval a = true) (hb : f.eval b = false) :
    a (tag f (route f a b)) = true ∧ b (tag f (route f a b)) = false := by
  induction f with
  | lit i s =>
    change s = true at h
    subst s
    exact ⟨ha,hb⟩
  | or l r il ir =>
    cases hl : l.eval a <;> simp [route, hl, tag]
    · exact ir h.2 (by simpa [DMFormula.eval,hl] using ha)
        (Bool.or_eq_false_iff.mp hb).2
    · exact il h.1 hl (Bool.or_eq_false_iff.mp hb).1
  | and l r il ir =>
    cases hl : l.eval b <;> simp [route, hl, tag]
    · exact il h.1 (Bool.and_eq_true_iff.mp ha).1 hl
    · exact ir h.2 (Bool.and_eq_true_iff.mp ha).2 (by simpa [DMFormula.eval,hl] using hb)

-- The pairs sent to any one occurrence form a rectangle.
theorem crossRoute {n} (f : F n) (a b c d : Input n)
    (h : route f a b = route f c d) : route f a d = route f a b := by
  induction f with
  | lit => rfl
  | or l r il ir =>
    cases h1 : l.eval a <;> cases h2 : l.eval c <;> simp [route, h1, h2] at h ⊢ <;>
      first | exact congrArg Sum.inl (il (Sum.inl.inj h)) | exact congrArg Sum.inr (ir (Sum.inr.inj h))
  | and l r il ir =>
    cases h1 : l.eval b <;> cases h2 : l.eval d <;> simp [route, h1, h2] at h ⊢ <;>
      first | exact congrArg Sum.inl (il (Sum.inl.inj h)) | exact congrArg Sum.inr (ir (Sum.inr.inj h))

end PEqualNP.Outside.FormulaGap_aux

/- Forced labels and incompatible rectangles. -/
namespace PEqualNP.Outside.FormulaGap_aux

open PEqualNP.MetaComplexity
variable {n : Nat} {X : Type} (x : X → Input n) (g : X → Bool)

-- Only wire i can distinguish this positive input from this negative input.
def Forced (i : Fin n) (a b : X) :=
  g a = true ∧ g b = false ∧ ∀ j, x a j = true → x b j = false → j = i

def Matches (f : F n) := ∀ a, f.eval (x a) = g a

theorem forcedTag {f : F n} (h : positive f) (ok : Matches x g f)
    {i : Fin n} {a b : X} (q : Forced x g i a b) :
    tag f (route f (x a) (x b)) = i := by
  obtain ⟨ha,hb⟩ := separates h (x a) (x b) ((ok a).trans q.1) ((ok b).trans q.2.1)
  exact q.2.2 _ ha hb

theorem forcedRead {f : F n} (h : positive f) (ok : Matches x g f)
    {i : Fin n} {a b : X} (q : Forced x g i a b) : 1 ≤ reads f i := by
  rw [← forcedTag x g h ok q]
  exact present _

-- If the same wire is the only possible label of both pairs and it appears
-- only once, their crossed pair must terminate at its unique occurrence.
theorem crossTag {f : F n} (h : positive f) (ok : Matches x g f)
    {i : Fin n} (hi : reads f i ≤ 1) {a b c d : X}
    (u : Forced x g i a b) (v : Forced x g i c d) :
    tag f (route f (x a) (x d)) = i := by
  have p := forcedTag x g h ok u
  have q := forcedTag x g h ok v
  rw [crossRoute f _ _ _ _ (uniqueTip hi _ _ p q)]
  exact p

theorem conflict {f : F n} (h : positive f) (ok : Matches x g f)
    {i j : Fin n} (ne : i ≠ j) {a b c d e z : X}
    (u : Forced x g i a b) (v : Forced x g i c d)
    (w : Forced x g j a e) (t : Forced x g j z d) :
    2 ≤ reads f i ∨ 2 ≤ reads f j := by
  by_contra! hin
  have eqi := crossTag x g h ok (by omega : reads f i ≤ 1) u v
  have eqj := crossTag x g h ok (by omega : reads f j ≤ 1) w t
  exact ne (eqi.symm.trans eqj)

end PEqualNP.Outside.FormulaGap_aux

/- A matching of three-corner patterns bounds formula size. -/
namespace PEqualNP.Outside.FormulaGap_aux

open PEqualNP.MetaComplexity
variable {R C : Nat}
abbrev Cell (R C : Nat) := Fin R × Fin C
def bits (a : Cell R C) : Input (R+C) := Fin.addCases (fun i => decide (i = a.1)) (fun j => decide (j = a.2))
def MixedTable (g : Cell R C → Bool) :=
  (∀ u, (∃ v, g (u,v) = true) ∧ (∃ v, g (u,v) = false)) ∧
  (∀ v, (∃ u, g (u,v) = true) ∧ (∃ u, g (u,v) = false))

theorem forceRow {g : Cell R C → Bool} {r s c} (h : g (r,c) = true) (t : g (s,c) = false) :
    Forced bits g (Fin.castAdd C r) (r,c) (s,c) := by
  refine ⟨h,t,?_⟩
  intro i
  refine Fin.addCases (fun u => ?_) (fun v => ?_) i
  · simp [bits]; tauto
  · simp [bits]; tauto

theorem forceCol {g : Cell R C → Bool} {r c d} (h : g (r,c) = true) (t : g (r,d) = false) :
    Forced bits g (Fin.natAdd R c) (r,c) (r,d) := by
  refine ⟨h,t,?_⟩
  intro i
  refine Fin.addCases (fun u => ?_) (fun v => ?_) i
  · simp [bits]; tauto
  · simp [bits]; tauto

theorem everyWire {g : Cell R C → Bool} {f : F (R+C)} (mix : MixedTable g)
    (hp : positive f) (ok : Matches bits g f) : ∀ i, 1 ≤ reads f i := by
  intro i
  refine Fin.addCases (fun r => ?_) (fun c => ?_) i
  · obtain ⟨c,h⟩ := (mix.1 r).1
    obtain ⟨s,t⟩ := (mix.2 c).2
    exact forcedRead bits g hp ok (forceRow h t)
  · obtain ⟨r,h⟩ := (mix.2 c).1
    obtain ⟨d,t⟩ := (mix.1 r).2
    exact forcedRead bits g hp ok (forceCol h t)

-- The two wires meeting at the middle of a three-corner path cannot both appear just once.
theorem repeatCorner {g : Cell R C → Bool} {f : F (R+C)} (mix : MixedTable g)
    (hp : positive f) (ok : Matches bits g f) {r s c d}
    (a : g (r,c) = true) (b : g (r,d) = true) (e : g (s,c) = true) (z : g (s,d) = false) :
    2 ≤ reads f (Fin.castAdd C r) ∨ 2 ≤ reads f (Fin.natAdd R c) := by
  obtain ⟨s',hs⟩ := (mix.2 c).2
  obtain ⟨d',hd⟩ := (mix.1 r).2
  have ne : Fin.castAdd C r ≠ Fin.natAdd R c := by
    intro h
    have h' := congrArg Fin.val h
    simp at h'
    omega
  exact conflict bits g hp ok ne (forceRow a hs) (forceRow b z) (forceCol a hd) (forceCol e z)

-- Charging one extra occurrence to each of a set of distinct repeated wires.
theorem countRepeats {n} (f : F n) (need : ∀ i, 1 ≤ reads f i)
    (s : Finset (Fin n)) (h : ∀ i ∈ s, 2 ≤ reads f i) : n + s.card ≤ f.leaves := by
  have localBound (i : Fin n) : 1 + (if i ∈ s then 1 else 0) ≤ reads f i := by
    by_cases hi : i ∈ s
    · simpa [hi] using h i hi
    · simpa [hi] using need i
  have total := Finset.sum_le_sum (s := Finset.univ) (fun i _ => localBound i)
  simpa [Finset.sum_add_distrib, sumReads, Finset.sum_boole] using total

def Corner (g : Cell R C → Bool) (r s : Fin R) (c d : Fin C) :=
  g (r,c) = true ∧ g (r,d) = true ∧ g (s,c) = true ∧ g (s,d) = false

private theorem row_ne_col (r : Fin R) (c : Fin C) : Fin.castAdd C r ≠ Fin.natAdd R c := by
  intro e
  have h := congrArg Fin.val e
  simp at h
  omega

-- Each of k corners with different central rows and columns charges a different leaf.
theorem matchingBound {g : Cell R C → Bool} {f : F (R+C)} (mix : MixedTable g)
    (hp : positive f) (ok : Matches bits g f) {k : Nat}
    (r s : Fin k → Fin R) (c d : Fin k → Fin C)
    (hr : Function.Injective r) (hc : Function.Injective c)
    (corners : ∀ j, Corner g (r j) (s j) (c j) (d j)) : R + C + k ≤ f.leaves := by
  classical
  let pick (j : Fin k) : Fin (R+C) := if 2 ≤ reads f (Fin.castAdd C (r j))
    then Fin.castAdd C (r j) else Fin.natAdd R (c j)
  have hinj : Function.Injective pick := by
    intro a b eq
    dsimp only [pick] at eq
    split at eq <;> split at eq
    · exact hr (Fin.castAdd_injective _ _ eq)
    · exact False.elim (row_ne_col _ _ eq)
    · exact False.elim (row_ne_col _ _ eq.symm)
    · exact hc (Fin.natAdd_injective _ _ eq)
  have large (j : Fin k) : 2 ≤ reads f (pick j) := by
    obtain ⟨a,b,e,z⟩ := corners j
    have h := repeatCorner mix hp ok a b e z
    dsimp only [pick]
    split
    · assumption
    · omega
  have bound := countRepeats f (everyWire mix hp ok) (Finset.univ.image pick) (by
    intro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    exact large j)
  simpa [Finset.card_image_of_injective _ hinj] using bound

end PEqualNP.Outside.FormulaGap_aux

/- Exact monotone formula costs for the five desk masks. -/
namespace PEqualNP.Outside.FormulaGap_aux

open PEqualNP.MetaComplexity PEqualNP.Represents

def table (m : Nat) (a : Cell 4 5) := m.testBit (5*a.1.val+a.2.val)

def DeskMatches (m : Nat) (f : F 9) := ∀ (r : Fin 4) (c : Fin 5),
  f.eval (fun i => (oneEach r c).getD i.val false) = m.testBit (5*r.val+c.val)

theorem exactInputs : ∀ (r : Fin 4) (c : Fin 5) (i : Fin 9),
    bits (r,c) i = (oneEach r c).getD i.val false := by decide

theorem matchesIff {m f} : DeskMatches m f ↔ Matches bits (table m) f := by
  have eqInput (r : Fin 4) (c : Fin 5) :
      (fun i : Fin 9 => (oneEach r c).getD i.val false) = bits (r,c) :=
    funext (fun i => (exactInputs r c i).symm)
  constructor
  · intro h a
    obtain ⟨r,c⟩ := a
    rw [← eqInput r c]
    exact h r c
  · intro h r c
    rw [eqInput r c]
    exact h (r,c)

def ExactFormula (m : Nat) :=
  (∀ f, positive f → DeskMatches m f → 11 ≤ f.leaves) ∧
  (∃ f, positive f ∧ DeskMatches m f ∧ f.leaves = 11)

def wire (i : Fin 9) : F 9 := .lit i true

private def tree34262 : F 9 := (.or (.or (.and (wire 0) (.or (wire 8) (.or (wire 5) (wire 6)))) (.and (wire 1) (.or (wire 7) (.or (wire 5) (wire 6))))) (.and (wire 4) (.or (wire 2) (wire 3))))

theorem exact34262 : ExactFormula 34262 := by
  constructor
  · intro f hp ok
    apply matchingBound (g := table 34262) (k := 2)
      (by unfold MixedTable; decide) hp (matchesIff.mp ok)
      ![0, 1] ![1, 0] ![1, 2] ![4, 3]
    · unfold Function.Injective; decide
    · unfold Function.Injective; decide
    · intro j; fin_cases j <;> unfold Corner <;> decide
  · exact ⟨tree34262, by simp [tree34262, wire, positive], by unfold DeskMatches; decide, rfl⟩

private def tree39902 : F 9 := (.or (.or (.and (.or (wire 0) (wire 1)) (.or (.or (wire 5) (wire 6)) (.or (wire 7) (wire 8)))) (.and (wire 2) (.or (wire 5) (wire 6)))) (.and (wire 3) (wire 4)))

theorem exact39902 : ExactFormula 39902 := by
  constructor
  · intro f hp ok
    apply matchingBound (g := table 39902) (k := 2)
      (by unfold MixedTable; decide) hp (matchesIff.mp ok)
      ![0, 1] ![2, 2] ![1, 2] ![3, 3]
    · unfold Function.Injective; decide
    · unfold Function.Injective; decide
    · intro j; fin_cases j <;> unfold Corner <;> decide
  · exact ⟨tree39902, by simp [tree39902, wire, positive], by unfold DeskMatches; decide, rfl⟩

private def tree47574 : F 9 := (.or (.or (.and (wire 0) (.or (wire 8) (.or (wire 5) (wire 6)))) (.and (.or (wire 1) (wire 2)) (.or (wire 7) (.or (wire 5) (wire 6))))) (.and (wire 3) (wire 4)))

theorem exact47574 : ExactFormula 47574 := by
  constructor
  · intro f hp ok
    apply matchingBound (g := table 47574) (k := 2)
      (by unfold MixedTable; decide) hp (matchesIff.mp ok)
      ![0, 1] ![1, 0] ![1, 2] ![4, 3]
    · unfold Function.Injective; decide
    · unfold Function.Injective; decide
    · intro j; fin_cases j <;> unfold Corner <;> decide
  · exact ⟨tree47574, by simp [tree47574, wire, positive], by unfold DeskMatches; decide, rfl⟩

private def tree48094 : F 9 := (.or (.or (.and (.or (wire 0) (.or (wire 1) (wire 2))) (.or (wire 5) (.or (wire 6) (wire 7)))) (.and (.or (wire 0) (wire 1)) (wire 8))) (.and (wire 3) (wire 4)))

theorem exact48094 : ExactFormula 48094 := by
  constructor
  · intro f hp ok
    apply matchingBound (g := table 48094) (k := 2)
      (by unfold MixedTable; decide) hp (matchesIff.mp ok)
      ![0, 1] ![2, 2] ![1, 2] ![4, 4]
    · unfold Function.Injective; decide
    · unfold Function.Injective; decide
    · intro j; fin_cases j <;> unfold Corner <;> decide
  · exact ⟨tree48094, by simp [tree48094, wire, positive], by unfold DeskMatches; decide, rfl⟩

private def tree105720 : F 9 := (.or (.or (.and (wire 0) (.or (wire 7) (wire 8))) (.and (.or (wire 1) (wire 2)) (.or (wire 6) (.or (wire 4) (wire 5))))) (.and (wire 3) (.or (wire 4) (wire 5))))

theorem exact105720 : ExactFormula 105720 := by
  constructor
  · intro f hp ok
    apply matchingBound (g := table 105720) (k := 2)
      (by unfold MixedTable; decide) hp (matchesIff.mp ok)
      ![1, 2] ![3, 3] ![0, 1] ![2, 2]
    · unfold Function.Injective; decide
    · unfold Function.Injective; decide
    · intro j; fin_cases j <;> unfold Corner <;> decide
  · exact ⟨tree105720, by simp [tree105720, wire, positive], by unfold DeskMatches; decide, rfl⟩

theorem fiveCases : ∀ m ∈ ([34262,39902,47574,48094,105720] : List Nat), ExactFormula m := by
  intro m hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  exacts [exact34262,exact39902,exact47574,exact48094,exact105720]

end PEqualNP.Outside.FormulaGap_aux

/- The square family and matching formulas. -/
namespace PEqualNP.Outside.FormulaGap_aux

open PEqualNP.MetaComplexity

-- There are k ordinary indices, one special index k, and one isolated index k+1.
def square (k : Nat) (a : Cell (k+2) (k+2)) : Bool :=
  decide ((a.1.val ≤ k ∧ a.2.val ≤ k ∧ (a.1.val < k ∨ a.2.val < k)) ∨
          (a.1.val = k+1 ∧ a.2.val = k+1))

def iso (k : Nat) : Fin (k+2) := ⟨k+1,by omega⟩
def special (k : Nat) : Fin (k+2) := ⟨k,by omega⟩
def ordinary {k : Nat} (i : Fin k) : Fin (k+2) := ⟨i.val,by omega⟩

theorem squareMixed {k : Nat} (hk : 0 < k) : MixedTable (square k) := by
  let z : Fin (k+2) := ⟨0,by omega⟩
  constructor
  · intro r
    by_cases h : r.val = k+1
    · exact ⟨⟨iso k,by simp [square,iso,h]⟩,⟨z,by simp [square,z,h]⟩⟩
    · have hr : r.val ≤ k := by omega
      exact ⟨⟨z,by simp [square,z,hr,hk]⟩,⟨iso k,by simp [square,iso,h]⟩⟩
  · intro c
    by_cases h : c.val = k+1
    · exact ⟨⟨iso k,by simp [square,iso,h]⟩,⟨z,by simp [square,z,h]⟩⟩
    · have hc : c.val ≤ k := by omega
      exact ⟨⟨z,by simp [square,z,hc,hk]⟩,⟨iso k,by simp [square,iso,h]⟩⟩

theorem squareLower {k : Nat} (hk : 0 < k) (f : F ((k+2)+(k+2))) (hp : positive f)
    (ok : Matches bits (square k) f) : 3*k+4 ≤ f.leaves := by
  have hi : Function.Injective (@ordinary k) := fun a b h => Fin.ext (congrArg (fun i : Fin (k+2) => i.val) h)
  have h := matchingBound (squareMixed hk) hp ok ordinary (fun _ => special k)
    ordinary (fun _ => special k) hi hi (by
      intro j
      simp [Corner,square,ordinary,special,j.isLt,Nat.le_of_lt j.isLt])
  omega

-- A disjunction of wires 0 through t in a chosen enumeration.
def group {n} (wire : Nat → Fin n) : Nat → F n
  | 0 => .lit (wire 0) true
  | t+1 => .or (group wire t) (.lit (wire (t+1)) true)

theorem groupPositive {n} (w : Nat → Fin n) (t : Nat) : positive (group w t) := by
  induction t with
  | zero => rfl
  | succ t ih => exact ⟨ih,rfl⟩

theorem groupLeaves {n} (w : Nat → Fin n) (t : Nat) : (group w t).leaves = t+1 := by
  induction t with
  | zero => rfl
  | succ t ih => simp [group, DMFormula.leaves, ih]

theorem groupEval {n} (w : Nat → Fin n) (t : Nat) (x : Input n) :
    (group w t).eval x = true ↔ ∃ i ≤ t, x (w i) = true := by
  induction t with
  | zero => simp [group,DMFormula.eval]
  | succ t ih =>
    simp only [group,DMFormula.eval,Bool.or_eq_true,ih,ite_true]
    constructor
    · rintro (⟨i,hi,v⟩|v)
      · exact ⟨i,by omega,v⟩
      · exact ⟨t+1,by omega,v⟩
    · rintro ⟨i,hi,v⟩
      by_cases h : i ≤ t
      · exact Or.inl ⟨i,h,v⟩
      · have e : i = t+1 := by omega
        exact Or.inr (e ▸ v)

def clipped (k i : Nat) : Fin (k+2) := ⟨min i k,by omega⟩

theorem rowGroup {k t : Nat} (ht : t ≤ k) (a : Cell (k+2) (k+2)) :
    (group (fun i => Fin.castAdd (k+2) (clipped k i)) t).eval (bits a) = decide (a.1.val ≤ t) := by
  apply Bool.eq_iff_iff.mpr
  rw [groupEval]
  simp only [bits, Fin.addCases_left, decide_eq_true_eq]
  constructor
  · rintro ⟨i,hi,e⟩
    have h := congrArg Fin.val e
    simp [clipped, Nat.min_eq_left (show i ≤ k by omega)] at h
    omega
  · intro h
    exact ⟨_,h,Fin.ext (Nat.min_eq_left (by omega))⟩

theorem colGroup {k t : Nat} (ht : t ≤ k) (a : Cell (k+2) (k+2)) :
    (group (fun i => Fin.natAdd (k+2) (clipped k i)) t).eval (bits a) = decide (a.2.val ≤ t) := by
  apply Bool.eq_iff_iff.mpr
  rw [groupEval]
  simp only [bits, Fin.addCases_right, decide_eq_true_eq]
  constructor
  · rintro ⟨i,hi,e⟩
    have h := congrArg Fin.val e
    simp [clipped, Nat.min_eq_left (show i ≤ k by omega)] at h
    omega
  · intro h
    exact ⟨_,h,Fin.ext (Nat.min_eq_left (by omega))⟩

-- The formula duplicates the ordinary column group.
def squareTree (k : Nat) : F ((k+2)+(k+2)) :=
  let R := fun i => Fin.castAdd (k+2) i
  let C := fun i => Fin.natAdd (k+2) i
  let rows := group (fun i => R (clipped k i)) (k-1)
  let cols := group (fun i => C (clipped k i)) (k-1)
  .or (.or (.and rows (.or cols (.lit (C (special k)) true)))
           (.and (.lit (R (special k)) true) cols))
      (.and (.lit (R (iso k)) true) (.lit (C (iso k)) true))

theorem squareEvaluates {k : Nat} (hk : 0 < k) : Matches bits (square k) (squareTree k) := by
  intro a
  simp only [squareTree,DMFormula.eval, rowGroup (Nat.sub_le k 1) a,
    colGroup (Nat.sub_le k 1) a,ite_true]
  apply Bool.eq_iff_iff.mpr
  simp only [bits, Fin.addCases_left, Fin.addCases_right]
  simp [special,iso,square,Fin.ext_iff]
  omega

theorem squareUpper {k : Nat} (hk : 0 < k) :
    ∃ f : F ((k+2)+(k+2)), positive f ∧ Matches bits (square k) f ∧ f.leaves = 3*k+4 := by
  refine ⟨squareTree k,?_,?_,?_⟩
  · exact ⟨⟨⟨groupPositive _ _, ⟨groupPositive _ _,rfl⟩⟩, ⟨rfl,groupPositive _ _⟩⟩, ⟨rfl,rfl⟩⟩
  · exact squareEvaluates hk
  · simp [squareTree,DMFormula.leaves,groupLeaves]
    omega

end PEqualNP.Outside.FormulaGap_aux

/- Compiling shared Boolean signals to project circuits. -/
namespace PEqualNP.Outside.FormulaGap_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

abbrev Sig (X : Type) := X → Bool
def bin {X} (b : Bool) (l r : Sig X) : Sig X :=
  fun x => if b then l x && r x else l x || r x

-- A growing list of wire meanings. Every step uses two earlier wires.
inductive Extend {X} (s : List (Sig X)) : Nat → List (Sig X) → Prop where
  | start : Extend s 0 s
  | gate {k w a b} (old : Extend s k w) (op : Bool) (ha : a ∈ w) (hb : b ∈ w) :
      Extend s (k+1) (w ++ [bin op a b])

theorem kept {X} {s w : List (Sig X)} {k} (p : Extend s k w) : ∀ a ∈ s, a ∈ w := by
  induction p with
  | start => exact fun _ h => h
  | gate _ _ _ _ ih => exact fun a h => List.mem_append_left _ (ih a h)

theorem compose {X} {s w v : List (Sig X)} {k l} (a : Extend s k w) (b : Extend w l v) :
    Extend s (k+l) v := by
  induction b with
  | start => exact a
  | gate _ op h g ih => exact .gate ih op h g

def allows (g : Gate) := g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

def tick (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem compile {X} {s w : List (Sig X)} {k} (p : Extend s k w) :
    ∃ gs : List Gate, gs.length = k ∧ (∀ g ∈ gs, allows g) ∧
      ∀ x, gs.foldl tick (s.map (fun f => f x)) = w.map (fun f => f x) := by
  induction p with
  | start => exact ⟨[],rfl,by simp,fun _ => rfl⟩
  | @gate k w a b old op ha hb ih =>
    obtain ⟨gs,len,allowed,ok⟩ := ih
    obtain ⟨i,hi,ei⟩ := List.mem_iff_getElem.mp ha
    obtain ⟨j,hj,ej⟩ := List.mem_iff_getElem.mp hb
    let g : Gate := ⟨if op then .and else .or,[i,j]⟩
    refine ⟨gs++[g],by simp [len],?_,?_⟩
    · intro q hq
      rcases List.mem_append.mp hq with h|h
      · exact allowed _ h
      · have : q = g := List.mem_singleton.mp h
        subst q
        cases op <;> simp [g,allows]
    · intro x
      simp only [List.foldl_append,List.foldl_cons,List.foldl_nil,ok]
      have readAt (u : Nat) (hu : u < w.length) :
        (w.map (fun f => f x)).getD u false = w[u] x := by
        rw [List.getD_eq_getElem _ _ (by simpa using hu)]; simp
      cases op <;> simp [tick,g,GateOp.eval,bin,readAt i hi,readAt j hj,ei,ej,
        -List.getD_eq_getElem?_getD]

def inputs (R C : Nat) : List (Sig (Cell R C)) :=
  (List.ofFn fun i : Fin R => fun a : Cell R C => decide (i = a.1)) ++
  (List.ofFn fun i : Fin C => fun a : Cell R C => decide (i = a.2))

theorem rawRow {R C} (i : Fin R) :
    (fun a : Cell R C => decide (i = a.1)) ∈ inputs R C := by
  apply List.mem_append_left
  exact List.mem_ofFn.mpr ⟨i,rfl⟩

theorem rawCol {R C} (i : Fin C) :
    (fun a : Cell R C => decide (i = a.2)) ∈ inputs R C := by
  apply List.mem_append_right
  exact List.mem_ofFn.mpr ⟨i,rfl⟩

theorem circuitFrom {R C k} {w : List (Sig (Cell R C))} (g : Cell R C → Bool)
    (p : Extend (inputs R C) k w) (out : g ∈ w) :
    RepSizeAtMost (fun u v => g (u,v)) k := by
  obtain ⟨gs,len,allowed,ok⟩ := compile p
  obtain ⟨i,hi,ei⟩ := List.mem_iff_getElem.mp out
  refine ⟨⟨gs,i⟩,allowed,len.le,?_⟩
  intro u v
  have init : (inputs R C).map (fun f => f (u,v)) = oneEach u v := by
    simp [inputs,oneEach,List.map_ofFn,Function.comp_def]
  have hw := ok (u,v)
  rw [init] at hw
  change (gs.foldl tick (oneEach u v)).getD i false = _
  rw [hw, List.getD_eq_getElem _ _ (by simpa using hi)]
  simp [ei]

end PEqualNP.Outside.FormulaGap_aux

/- A circuit for each member of the square family. -/
namespace PEqualNP.Outside.FormulaGap_aux

open PEqualNP.MetaComplexity PEqualNP.Represents

def sem {R C} (f : F (R+C)) : Sig (Cell R C) := fun a => f.eval (bits a)

theorem appendGroup {R C} (wire : Nat → Fin (R+C)) (t : Nat) (w : List (Sig (Cell R C)))
    (avail : ∀ j ≤ t, sem (.lit (wire j) true) ∈ w) :
    ∃ v, Extend w t v ∧ sem (group wire t) ∈ v := by
  induction t with
  | zero => exact ⟨w,.start,avail 0 (by omega)⟩
  | succ t ih =>
    obtain ⟨v,h,haveGroup⟩ := ih (fun j hj => avail j (by omega))
    have last := kept h _ (avail (t+1) (by omega))
    exact ⟨_, .gate h false haveGroup last, List.mem_append_right _ (List.mem_singleton_self _)⟩

theorem rowLit {R C} (r : Fin R) : sem (.lit (Fin.castAdd C r) true) ∈ inputs R C := by
  have eq : sem (R:=R) (C:=C) (.lit (Fin.castAdd C r) true) = (fun a : Cell R C => decide (r = a.1)) := by
    funext a
    simp only [sem,DMFormula.eval,ite_true,bits,Fin.addCases_left]
  rw [eq]
  exact rawRow r

theorem colLit {R C} (c : Fin C) : sem (.lit (Fin.natAdd R c) true) ∈ inputs R C := by
  have eq : sem (R:=R) (C:=C) (.lit (Fin.natAdd R c) true) = (fun a : Cell R C => decide (c = a.2)) := by
    funext a
    simp only [sem,DMFormula.eval,ite_true,bits,Fin.addCases_right]
  rw [eq]
  exact rawCol c

-- The two ordinary groups are built once. The rest uses six gates and reads the column group twice.
theorem squareCircuit {k : Nat} (hk : 0 < k) :
    RepSizeAtMost (fun u v => square k (u,v)) (2*k+4) := by
  let n := k+2
  let R (i : Fin n) := Fin.castAdd n i
  let C (i : Fin n) := Fin.natAdd n i
  let u := group (fun j => R (clipped k j)) (k-1)
  let v := group (fun j => C (clipped k j)) (k-1)
  let ss := inputs n n
  obtain ⟨s1,h1,hu⟩ := appendGroup (fun j => R (clipped k j)) (k-1) ss
    (fun j _ => rowLit _)
  obtain ⟨s2,h2,hv⟩ := appendGroup (fun j => C (clipped k j)) (k-1) s1
    (fun j _ => kept h1 _ (colLit _))
  have H := compose h1 h2
  change sem u ∈ s1 at hu
  change sem v ∈ s2 at hv
  let rs : F (n+n) := .lit (R (special k)) true
  let cs : F (n+n) := .lit (C (special k)) true
  let ri : F (n+n) := .lit (R (iso k)) true
  let ci : F (n+n) := .lit (C (iso k)) true
  have hrs : sem rs ∈ s2 := kept H _ (rowLit _)
  have hcs : sem cs ∈ s2 := kept H _ (colLit _)
  have hri : sem ri ∈ s2 := kept H _ (rowLit _)
  have hci : sem ci ∈ s2 := kept H _ (colLit _)
  have hU := kept h2 _ hu
  let a := bin false (sem v) (sem cs)
  let b := bin true (sem u) a
  let c := bin true (sem rs) (sem v)
  let d := bin false b c
  let e := bin true (sem ri) (sem ci)
  have H1 : Extend ss _ (s2++[a]) := .gate H false hv hcs
  have H2 : Extend ss _ ((s2++[a])++[b]) := .gate H1 true (by simp [hU]) (by simp)
  have H3 : Extend ss _ (((s2++[a])++[b])++[c]) := .gate H2 true (by simp [hrs]) (by simp [hv])
  have H4 : Extend ss _ ((((s2++[a])++[b])++[c])++[d]) := .gate H3 false (by simp) (by simp)
  have H5 : Extend ss _ (((((s2++[a])++[b])++[c])++[d])++[e]) :=
    .gate H4 true (by simp [hri]) (by simp [hci])
  have H6 := Extend.gate H5 false (a:=d) (b:=e) (by simp) (by simp)
  have out : square k = bin false d e := funext (fun x => (squareEvaluates hk x).symm)
  have eqn : (k-1)+(k-1)+1+1+1+1+1+1 = 2*k+4 := by omega
  rw [← eqn]
  exact circuitFrom (square k) H6 (by rw [out]; exact List.mem_append_right _ (List.mem_singleton_self _))

end PEqualNP.Outside.FormulaGap_aux

/- The tight binary-gate lemma reused from the earlier family proof. -/
namespace PEqualNP.Outside.FormulaGap_aux

namespace Tight
variable {α : Type} [DecidableEq α] (gate : Bool → α → α → α)

inductive Can (t : α) : Nat → Finset α → Prop where
  | done {k s} : t ∈ s → Can t k s
  | step {k s a b} (op : Bool) : a ∈ s → b ∈ s →
      Can t k (insert (gate op a b) s) → Can t (k+1) s

inductive Tree : Finset α → α → Prop where
  | leaf (x : α) : Tree {x} x
  | node {p q x y} (op : Bool) : Tree p x → Tree q y → Disjoint p q →
      Tree (p ∪ q) (gate op x y)

theorem enlarge {t k s} (h : Can gate t k s) : ∀ {q}, s ⊆ q → Can gate t k q := by
  induction h with
  | done ht => exact fun hsub => .done (hsub ht)
  | step op ha hb _ ih =>
    intro q hsub
    exact .step op (hsub ha) (hsub hb) (ih (Finset.insert_subset_insert _ hsub))

theorem budget {t k s} (h : Can gate t k s) : ∀ {m}, k ≤ m → Can gate t m s := by
  induction h with
  | done ht => exact fun _ => .done ht
  | step op ha hb _ ih =>
    intro m hm
    cases m with
    | zero => omega
    | succ m => exact .step op ha hb (ih (by omega))

-- Substitute disjoint input trees for the leaves of a read-once tree.
theorem substTree {q t} (h : Tree gate q t) (f : α → Finset α)
    (hr : ∀ x∈q, Tree gate (f x) x)
    (hd : ∀ x∈q, ∀ y∈q, x ≠ y → Disjoint (f x) (f y)) :
    Tree gate (q.biUnion f) t := by
  induction h with
  | leaf x => simpa using hr x (by simp)
  | @node p q x y op hp hq dis ip iq =>
    rw [Finset.union_biUnion]
    refine Tree.node op (ip (fun i hi => hr i (by simp [hi]))
      (fun i hi j hj => hd i (by simp [hi]) j (by simp [hj])))
      (iq (fun i hi => hr i (by simp [hi]))
      (fun i hi j hj => hd i (by simp [hi]) j (by simp [hj]))) ?_
    rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨i,hi,hiz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨j,hj,hjz⟩ := Finset.mem_biUnion.mp hz'
    have ne : i ≠ j := by rintro rfl; exact Finset.disjoint_left.mp dis hi hj
    exact Finset.disjoint_left.mp (hd i (by simp [hi]) j (by simp [hj]) ne) hiz hjz

-- Attaining the maximum number of necessary inputs forces a read-once tree.
theorem tight {t k s} (h : Can gate t k s) :
    ∃ q : Finset α, q ⊆ s ∧ q.card ≤ k+1 ∧ Can gate t k q ∧
       (q.card = k+1 → Tree gate q t) := by
  induction h with
  | done ht => exact ⟨{_}, by simpa, by simp, .done (by simp), fun _ => .leaf _⟩
  | @step k s a b op ha hb h ih =>
    obtain ⟨q,hsub,hcard,hq,htree⟩ := ih
    let w := gate op a b
    by_cases hw : w ∈ q
    · let v := insert a (insert b (q.erase w))
      have he : q.erase w ⊆ s := by
        intro x hx
        exact (Finset.mem_insert.mp (hsub (Finset.mem_erase.mp hx).2)).resolve_left
          (Finset.mem_erase.mp hx).1
      have h1 := Finset.card_insert_le a (insert b (q.erase w))
      have h2 := Finset.card_insert_le b (q.erase w)
      have h3 := Finset.card_erase_add_one hw
      refine ⟨v, Finset.insert_subset ha (Finset.insert_subset hb he), by dsimp [v]; omega, ?_, ?_⟩
      · apply Can.step (a:=a) (b:=b) op (by simp [v]) (by simp [v])
        apply enlarge gate hq
        intro x hx
        by_cases ex : x = w
        · exact Finset.mem_insert.mpr (.inl ex)
        · exact Finset.mem_insert_of_mem (by simp [v,hx,ex])
      · intro eq
        change (insert a (insert b (q.erase w))).card = k+1+1 at eq
        have old := htree (by omega)
        have af : a ∉ insert b (q.erase w) := by
          intro hmem
          rw [Finset.insert_eq_of_mem hmem] at eq; omega
        have bf : b ∉ q.erase w := by
          intro hmem
          rw [Finset.insert_eq_of_mem hmem] at eq h1; omega
        have ab : a ≠ b := by rintro rfl; exact af (by simp)
        let f (x : α) : Finset α := if x = w then {a,b} else {x}
        have used (x) (hx : x ∈ q) (hn : x ≠ w) : x ≠ a ∧ x ≠ b := by
          have hxe := Finset.mem_erase.mpr ⟨hn,hx⟩
          exact ⟨by rintro rfl; exact af (Finset.mem_insert_of_mem hxe),
            by rintro rfl; exact bf hxe⟩
        have rep : ∀ x∈q, Tree gate (f x) x := by
          intro x hx
          by_cases e : x = w
          · subst x
            simpa [f] using Tree.node (gate:=gate) op (.leaf a) (.leaf b) (by simpa using ab)
          · simpa [f,e] using Tree.leaf (gate:=gate) x
        have dis : ∀ x∈q, ∀ y∈q, x ≠ y → Disjoint (f x) (f y) := by
          intro x hx y hy ne
          by_cases ex : x = w <;> by_cases ey : y = w
          · exact (ne (ex.trans ey.symm)).elim
          · obtain ⟨na,nb⟩ := used y hy ey
            simp [f,ex,ey,na,nb]
          · obtain ⟨na,nb⟩ := used x hx ex
            simp [f,ex,ey,na,nb]
          · simp [f,ex,ey,ne]
        have same : q.biUnion f = v := by
          ext x
          simp only [Finset.mem_biUnion, f, v, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro ⟨j,hj,hx⟩
            by_cases e : j = w
            · simp [e] at hx
              exact hx.elim Or.inl (fun eb => Or.inr (Or.inl eb))
            · simp [e] at hx
              exact Or.inr (Or.inr ⟨hx.symm ▸ e, hx.symm ▸ hj⟩)
          · rintro (rfl|rfl|⟨ne,hx⟩)
            · exact ⟨w,hw,by simp⟩
            · exact ⟨w,hw,by simp⟩
            · exact ⟨x,hx,by simp [ne]⟩
        exact same ▸ substTree gate old f rep dis
    · refine ⟨q, ?_, by omega, budget gate hq (by omega), by omega⟩
      intro x hx
      exact (Finset.mem_insert.mp (hsub hx)).resolve_left (by intro ex; apply hw; simpa [w, ← ex] using hx)

end Tight

end PEqualNP.Outside.FormulaGap_aux

/- At the minimum wiring budget every essential input occurs once. -/
namespace PEqualNP.Outside.FormulaGap_aux

open Tight PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds PEqualNP.Represents
noncomputable section
open scoped Classical
variable {X : Type} [Fintype X]

def zeroS : Sig X := fun _ => false
def oneS : Sig X := fun _ => true
def valueAt (x : X) (s : Sig X) := s x

def word (w : List (Sig X)) (g : Gate) : Sig X :=
  let a := w.getD (g.inputs.getD 0 0) zeroS
  let b := w.getD (g.inputs.getD 1 0) zeroS
  let isAnd := match g.op with | .and => true | _ => false
  match g.inputs with
  | [] => if isAnd then oneS else zeroS
  | [_] => a
  | _ :: _ :: _ => bin isAnd a b

omit [Fintype X] in
theorem evalWord (i : X) (w : List (Sig X)) (g : Gate) (h : allows g) :
   valueAt i (word w g) = g.op.eval (g.inputs.map (fun j => (w.map (valueAt i)).getD j false)) := by
  obtain ⟨op,inp⟩ := g
  rcases h with ⟨hop,hlen⟩
  change op = .and ∨ op = .or at hop
  change inp.length ≤ 2 at hlen
  have rd (j : Nat) : (w.map (valueAt i)).getD j false = valueAt i (w.getD j zeroS) :=
    List.getD_map w (zeroS : Sig X) (n := j) (valueAt i)
  simp_rw [rd]
  rcases inp with _|⟨x,_|⟨y,_|⟨z,zs⟩⟩⟩ <;> simp at hlen
  all_goals rcases hop with rfl|rfl <;> simp [word, bin, GateOp.eval, valueAt,zeroS,oneS]


omit [Fintype X] in
theorem proj (gs : List Gate) (w : List (Sig X)) (i : X) (h : ∀ g∈gs, allows g) :
 (gs.foldl (fun v g => v ++ [word v g]) w).map (valueAt i) =
 gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun j => v.getD j false)]) (w.map (valueAt i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    simp [evalWord i w g (h g (by simp))]

omit [Fintype X] in
theorem read_mem (w : List (Sig X)) (s : Finset (Sig X)) (incl : ∀ x∈w, x∈s) (zero : zeroS∈s) (j : Nat) :
   w.getD j zeroS ∈ s := by
  by_cases h : j < w.length
  · rw [List.getD_eq_getElem _ _ h]; exact incl _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]; exact zero

theorem circuitCan (gs : List Gate) (w : List (Sig X)) (s : Finset (Sig X)) (o : Nat)
    (z : zeroS∈s) (u : oneS∈s) (h : ∀ x∈w, x∈s) :
    Can bin ((gs.foldl (fun v g => v ++ [word v g]) w).getD o zeroS) gs.length s := by
  induction gs generalizing w s with
  | nil => exact Can.done (read_mem w s h z o)
  | cons g gs ih =>
    let v := word w g
    have rest := ih (w ++ [v]) (insert v s) (Finset.mem_insert_of_mem z)
       (Finset.mem_insert_of_mem u) (by
        intro x hx; rcases List.mem_append.mp hx with h1|h2
        · exact Finset.mem_insert_of_mem (h x h1)
        · simp only [List.mem_singleton] at h2; exact Finset.mem_insert.mpr (.inl h2))
    change Can bin _ (gs.length+1) s
    by_cases hv : v ∈ s
    · have : insert v s = s := Finset.insert_eq_of_mem hv
      rw [this] at rest
      exact budget bin rest (by omega)
    · rcases g with ⟨op,inp⟩
      rcases inp with _|⟨a,_|⟨b,tail⟩⟩
      · apply False.elim; apply hv; cases op <;> first | exact u | exact z
      · exact False.elim (hv (by simpa [v,word] using read_mem w s h z a))
      · exact .step (match op with | .and => true | _ => false)
          (read_mem w s h z a) (read_mem w s h z b) rest



def rawWire {R C : Nat} (i : Fin (R+C)) : Sig (Cell R C) := fun a => bits a i
def pool {R C : Nat} : Finset (Sig (Cell R C)) :=
  insert zeroS (insert oneS (Finset.univ.image (@rawWire R C)))

theorem entries {R C} : ∀ a ∈ inputs R C, a ∈ @pool R C := by
  intro a ha
  apply Finset.mem_insert_of_mem
  apply Finset.mem_insert_of_mem
  rcases List.mem_append.mp ha with h|h
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
    exact Finset.mem_image.mpr ⟨Fin.castAdd C i,by simp,by ext; simp [rawWire,bits]⟩
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
    exact Finset.mem_image.mpr ⟨Fin.natAdd R i,by simp,by ext; simp [rawWire,bits]⟩

theorem circuitMeans {R C k} {g : Cell R C → Bool}
    (h : RepSizeAtMost (fun r c => g (r,c)) k) : Can bin g k pool := by
  obtain ⟨c,hc,hs,ht⟩ := h
  let w := c.gates.foldl (fun v t => v++[word v t]) (inputs R C)
  have can := circuitCan c.gates (inputs R C) pool c.output (by simp [pool]) (by simp [pool]) entries
  have equal : w.getD c.output zeroS = g := by
    funext a
    obtain ⟨u,v⟩ := a
    have map := List.getD_map w zeroS (n:=c.output) (valueAt (u,v))
    have init : (inputs R C).map (valueAt (u,v)) = oneEach u v := by
      simp [inputs,valueAt,oneEach,List.map_ofFn,Function.comp_def]
    have pr := proj c.gates (inputs R C) (u,v) hc
    change w.map _ = _ at pr
    rw [init] at pr
    change (w.getD c.output zeroS) (u,v) = _
    exact map.symm.trans ((congrArg (fun l : List Bool => l.getD c.output false) pr).trans (ht u v))
  exact equal ▸ budget bin can hs

theorem separated {w : Finset (Sig X)} {m : Nat} {g : Sig X} (h : Can bin g m w)
    (a b : X) (ha : g a = true) (hb : g b = false) : ∃ f ∈ w, f a = true ∧ f b = false := by
  induction h with
  | done h => exact ⟨_, h, ha, hb⟩
  | @step k s l r op hl hr rest ih =>
    obtain ⟨f,hf,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hf with e|old
    · subst f
      cases op <;> simp [bin] at hp hn
      · rcases hp with h|h
        · exact ⟨l,hl,h,hn.1⟩
        · exact ⟨r,hr,h,hn.2⟩
      · by_cases h : l b = true
        · exact ⟨r,hr,hp.2,hn h⟩
        · exact ⟨l,hl,hp.1,by simpa using h⟩
    · exact ⟨_,old,hp,hn⟩

theorem forcedWitness {R C} {g : Cell R C → Bool} (mix : MixedTable g) (i : Fin (R+C)) :
    ∃ a b, Forced bits g i a b ∧ bits a i = true ∧ bits b i = false := by
  refine Fin.addCases (fun r => ?_) (fun c => ?_) i
  · obtain ⟨c,h⟩ := (mix.1 r).1
    obtain ⟨s,t⟩ := (mix.2 c).2
    have ne : r ≠ s := by rintro rfl; rw [h] at t; contradiction
    exact ⟨(r,c),(s,c),forceRow h t,by simp [bits],by simp [bits,ne]⟩
  · obtain ⟨r,h⟩ := (mix.2 c).1
    obtain ⟨d,t⟩ := (mix.1 r).2
    have ne : c ≠ d := by rintro rfl; rw [h] at t; contradiction
    exact ⟨(r,c),(r,d),forceCol h t,by simp [bits],by simp [bits,ne]⟩

theorem rawInj {R C} {g : Cell R C → Bool} (mix : MixedTable g) : Function.Injective (@rawWire R C) := by
  intro i j eq
  obtain ⟨a,b,force,ha,hb⟩ := forcedWitness mix i
  exact (force.2.2 j ((congrFun eq a).symm.trans ha) ((congrFun eq b).symm.trans hb)).symm

theorem needsRaw {R C m} {g : Cell R C → Bool} {q} (mix : MixedTable g)
    (sub : q ⊆ pool) (h : Can bin g m q) : Finset.univ.image (@rawWire R C) ⊆ q := by
  intro v hv
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨a,b,f,_,_⟩ := forcedWitness mix i
  obtain ⟨l,hl,ha,hb⟩ := separated h a b f.1 f.2.1
  have hp := sub hl
  simp only [pool, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hp
  rcases hp with rfl | rfl | ⟨j,e⟩
  · contradiction
  · contradiction
  · subst l
    have eq := f.2.2 j ha hb
    exact eq ▸ hl

theorem treeFormula {R C} {q g} (tree : Tree bin q g) (sub : q ⊆ Finset.univ.image (@rawWire R C)) :
    ∃ f, positive f ∧ Matches bits g f ∧ f.leaves = q.card := by
  induction tree with
  | leaf x =>
    obtain ⟨j,_,e⟩ := Finset.mem_image.mp (sub (Finset.mem_singleton_self x))
    exact ⟨.lit j true,rfl,fun a => (congrFun e a),by simp [DMFormula.leaves]⟩
  | @node p q x y op a b dis il ir =>
    obtain ⟨l,pl,ml,cl⟩ := il (Finset.Subset.trans Finset.subset_union_left sub)
    obtain ⟨r,pr,mr,cr⟩ := ir (Finset.Subset.trans Finset.subset_union_right sub)
    cases op
    · exact ⟨.or l r,⟨pl,pr⟩,fun a => by simp [DMFormula.eval,bin,ml a,mr a],
        by simp [DMFormula.leaves,cl,cr,Finset.card_union_of_disjoint dis]⟩
    · exact ⟨.and l r,⟨pl,pr⟩,fun a => by simp [DMFormula.eval,bin,ml a,mr a],
        by simp [DMFormula.leaves,cl,cr,Finset.card_union_of_disjoint dis]⟩

theorem noSmallCircuit {R C k} {g : Cell R C → Bool} (mix : MixedTable g)
    (lb : ∀ f, positive f → Matches bits g f → R+C < f.leaves) (hk : k < R+C) :
    ¬ RepSizeAtMost (fun r c => g (r,c)) k := by
  intro h
  obtain ⟨q,sub,hq,hcan,tree⟩ := tight _ (circuitMeans h)
  have incl := needsRaw mix sub hcan
  have card := Finset.card_le_card incl
  have nr : (Finset.univ.image (@rawWire R C)).card = R+C := by
    simp [Finset.card_image_of_injective _ (rawInj mix)]
  rw [nr] at card
  have eq := Finset.eq_of_subset_of_card_le incl (by omega)
  obtain ⟨f,p,m,t⟩ := treeFormula (tree (by omega)) (by rw [eq])
  have := lb f p m
  omega

end
end PEqualNP.Outside.FormulaGap_aux

/- Exact circuit and formula results on the project inputs. -/
namespace PEqualNP.Outside.FormulaGap_aux

open PEqualNP.Represents PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def makeGate (p : Bool × Nat × Nat) : Gate := ⟨if p.1 then .and else .or, [p.2.1,p.2.2]⟩
def circuit (gates : List (Bool × Nat × Nat)) (out : Nat) : Circuit := ⟨gates.map makeGate, out⟩

theorem goodCircuit (gs : List (Bool × Nat × Nat)) (out : Nat) : Monotone2 (circuit gs out) := by
  intro g hg
  obtain ⟨⟨op,a,b⟩,_,rfl⟩ := List.mem_map.mp hg
  cases op <;> simp [makeGate]

theorem upper34262 : RepSizeAtMost (fun r c => table 34262 (r,c)) 9 :=
  ⟨circuit [(false,5,6), (false,8,9), (true,0,10), (false,7,9), (true,1,12), (false,11,13), (false,2,3), (true,4,15), (false,14,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem upper39902 : RepSizeAtMost (fun r c => table 39902 (r,c)) 9 :=
  ⟨circuit [(false,0,1), (false,5,6), (false,7,8), (false,10,11), (true,9,12), (true,2,10), (false,13,14), (true,3,4), (false,15,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem upper47574 : RepSizeAtMost (fun r c => table 47574 (r,c)) 9 :=
  ⟨circuit [(false,5,6), (false,8,9), (true,0,10), (false,1,2), (false,7,9), (true,12,13), (false,11,14), (true,3,4), (false,15,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem upper48094 : RepSizeAtMost (fun r c => table 48094 (r,c)) 9 :=
  ⟨circuit [(false,0,1), (false,6,7), (false,5,10), (false,8,11), (true,9,12), (true,2,11), (false,13,14), (true,3,4), (false,15,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem upper105720 : RepSizeAtMost (fun r c => table 105720 (r,c)) 9 :=
  ⟨circuit [(false,7,8), (true,0,9), (false,1,2), (false,4,5), (false,6,12), (true,11,13), (false,10,14), (true,3,12), (false,15,16)] 17,
    goodCircuit _ _, by decide, by decide⟩


def ExactDesk (m : Nat) :=
  (¬ RepSizeAtMost (fun r c => table m (r,c)) 8) ∧
  RepSizeAtMost (fun r c => table m (r,c)) 9 ∧ ExactFormula m

theorem desks : ∀ m ∈ ([34262,39902,47574,48094,105720] : List Nat), ExactDesk m := by
  intro m hm
  have hf := fiveCases m hm
  have mix : MixedTable (table m) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl <;> unfold MixedTable <;> decide
  refine ⟨noSmallCircuit mix (fun f p ok => ?_) (by decide), ?_, hf⟩
  · have := hf.1 f p (matchesIff.mpr ok)
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl
    exacts [upper34262,upper39902,upper47574,upper48094,upper105720]

def ExactSquare (k : Nat) :=
  (¬ RepSizeAtMost (fun r c => square k (r,c)) (2*k+3)) ∧
  RepSizeAtMost (fun r c => square k (r,c)) (2*k+4) ∧
  (∀ f, positive f → Matches bits (square k) f → 3*k+4 ≤ f.leaves) ∧
  ∃ f, positive f ∧ Matches bits (square k) f ∧ f.leaves = 3*k+4

theorem exactSquare (k : Nat) (hk : 0 < k) : ExactSquare k := by
  refine ⟨noSmallCircuit (squareMixed hk) (fun f p ok => ?_) (by omega),
    squareCircuit hk, squareLower hk, squareUpper hk⟩
  have := squareLower hk f p ok
  omega

end PEqualNP.Outside.FormulaGap_aux

theorem PEqualNP.Outside.FormulaGap :
  let Pos := fun {n : Nat} (f : PEqualNP.MetaComplexity.DMFormula n) =>
    PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => Prop) (fun _ b => b = true)
      (fun _ _ l r => l ∧ r) (fun _ _ l r => l ∧ r) f
  (∀ k : Nat, 0 < k →
    let G := fun (r c : Fin (k+2)) =>
      decide ((r.val ≤ k ∧ c.val ≤ k ∧ (r.val < k ∨ c.val < k)) ∨ (r.val = k+1 ∧ c.val = k+1))
    let Fits := fun (f : PEqualNP.MetaComplexity.DMFormula ((k+2)+(k+2))) =>
      ∀ a : Fin (k+2) × Fin (k+2),
        f.eval (Fin.addCases (fun i => decide (i = a.1)) (fun j => decide (j = a.2))) = G a.1 a.2
    (¬ PEqualNP.Represents.RepSizeAtMost G (2*k+3)) ∧ PEqualNP.Represents.RepSizeAtMost G (2*k+4) ∧
    (∀ f, Pos f → Fits f → 3*k+4 ≤ f.leaves) ∧ ∃ f, Pos f ∧ Fits f ∧ f.leaves = 3*k+4) ∧
  (∀ m ∈ ([34262,39902,47574,48094,105720] : List Nat),
    let G := fun (r : Fin 4) (c : Fin 5) => m.testBit (5*r.val+c.val)
    let Fits := fun (f : PEqualNP.MetaComplexity.DMFormula 9) =>
      ∀ (r : Fin 4) (c : Fin 5), f.eval (fun i => (PEqualNP.Represents.oneEach r c).getD i.val false) = G r c
    (¬ PEqualNP.Represents.RepSizeAtMost G 8) ∧ PEqualNP.Represents.RepSizeAtMost G 9 ∧
    (∀ f, Pos f → Fits f → 11 ≤ f.leaves) ∧ ∃ f, Pos f ∧ Fits f ∧ f.leaves = 11) :=
  ⟨PEqualNP.Outside.FormulaGap_aux.exactSquare, PEqualNP.Outside.FormulaGap_aux.desks⟩
