import PEqualNP.Defs

namespace PEqualNP.Outside.TightFamily_aux

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

open Tight PEqualNP.CircuitLowerBounds PEqualNP.Represents PEqualNP.MetaComplexity
abbrev W := BitVec 29
abbrev Pool := Finset W
def combine (op : Bool) (a b : W) : W := if op then a &&& b else a ||| b
def raw : List W := [1048607, 2098144, 4226048, 9404416, 16811041, 33622082, 67244164, 134488328, 268976656]
def start : Pool := insert 0 (insert (-1) raw.toFinset)
def word (w : List W) (g : Gate) : W :=
  let a := w.getD (g.inputs.getD 0 0) 0
  let b := w.getD (g.inputs.getD 1 0) 0
  let isAnd := match g.op with | .and => true | _ => false
  match g.inputs with
  | [] => if isAnd then -1 else 0
  | [_] => a
  | _ :: _ :: _ => combine isAnd a b

def atBit (i : Fin 29) (x : W) := x.getLsbD i
def allowed (g : Gate) := g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem evalWord (i : Fin 29) (w : List W) (g : Gate) (h : allowed g) :
   atBit i (word w g) = g.op.eval (g.inputs.map (fun j => (w.map (atBit i)).getD j false)) := by
  obtain ⟨op,inp⟩ := g
  rcases h with ⟨hop,hlen⟩
  change op = .and ∨ op = .or at hop
  change inp.length ≤ 2 at hlen
  have rd (j : Nat) : (w.map (atBit i)).getD j false = atBit i (w.getD j 0) :=
    by simpa [atBit] using (List.getD_map w (0 : W) (n := j) (atBit i))
  have ones : ∀ i : Fin 29, atBit i (-1) = true := by decide
  simp_rw [rd]
  rcases inp with _|⟨x,_|⟨y,_|⟨z,zs⟩⟩⟩ <;> simp at hlen
  all_goals rcases hop with rfl|rfl <;> simp [word, combine, GateOp.eval, atBit]
  exact ones i

theorem proj (gs : List Gate) (w : List W) (i : Fin 29) (h : ∀ g∈gs, allowed g) :
 (gs.foldl (fun v g => v ++ [word v g]) w).map (atBit i) =
 gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun j => v.getD j false)]) (w.map (atBit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    simp [evalWord i w g (h g (by simp))]

theorem read_mem (w : List W) (s : Pool) (incl : ∀ x∈w, x∈s) (zero : 0∈s) (j : Nat) :
   w.getD j 0 ∈ s := by
  by_cases h : j < w.length
  · rw [List.getD_eq_getElem _ _ h]; exact incl _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]; exact zero

theorem circuitCan (gs : List Gate) (w : List W) (s : Pool) (o : Nat)
    (z : 0∈s) (u : (-1:W)∈s) (h : ∀ x∈w, x∈s) :
    Can combine ((gs.foldl (fun v g => v ++ [word v g]) w).getD o 0) gs.length s := by
  induction gs generalizing w s with
  | nil => exact Can.done (read_mem w s h z o)
  | cons g gs ih =>
    let v := word w g
    have rest := ih (w ++ [v]) (insert v s) (Finset.mem_insert_of_mem z)
       (Finset.mem_insert_of_mem u) (by
        intro x hx; rcases List.mem_append.mp hx with h1|h2
        · exact Finset.mem_insert_of_mem (h x h1)
        · simp only [List.mem_singleton] at h2; exact Finset.mem_insert.mpr (.inl h2))
    change Can combine _ (gs.length+1) s
    by_cases hv : v ∈ s
    · have : insert v s = s := Finset.insert_eq_of_mem hv
      rw [this] at rest
      exact budget combine rest (by omega)
    · rcases g with ⟨op,inp⟩
      rcases inp with _|⟨a,_|⟨b,tail⟩⟩
      · apply False.elim; apply hv; cases op <;> first | exact u | exact z
      · exact False.elim (hv (by simpa [v,word] using read_mem w s h z a))
      · exact .step (match op with | .and => true | _ => false)
          (read_mem w s h z a) (read_mem w s h z b) rest


def plane (m : Nat) (u : Fin 4) (v : Fin 5) := m.testBit (5*u.val+v.val)

theorem coordinates : ∀ i : Fin 20, raw.map (atBit (⟨i.val, by omega⟩ : Fin 29)) =
      oneEach (Fin.ofNat 4 (i.val/5)) (Fin.ofNat 5 (i.val%5)) := by decide
theorem index : ∀ i : Fin 20,
      5*(Fin.ofNat 4 (i.val/5)).val + (Fin.ofNat 5 (i.val%5)).val = i.val := by decide

theorem representCan {m} (h : RepSizeAtMost (plane m) 8) :
    ∃ t : W, Can combine t 8 start ∧ ∀ i : Fin 20, t.getLsbD i = m.testBit i := by
  obtain ⟨c,hc,hs,ht⟩ := h
  let q := c.gates.foldl (fun v g => v ++ [word v g]) raw
  refine ⟨q.getD c.output 0, budget combine (circuitCan c.gates raw start c.output
    (by simp [start]) (by simp [start]) (by intro x hx; simp [start,hx])) hs, ?_⟩
  intro i
  let p : Fin 29 := ⟨i.val, by omega⟩
  change atBit p (q.getD c.output 0) = _
  rw [← List.getD_map q 0 (atBit p), show atBit p 0 = false by simp [atBit]]
  rw [show q.map (atBit p) = _ from proj c.gates raw p hc, coordinates i]
  exact (ht _ _).trans (congrArg m.testBit (index i))

def ordered (s : Pool) (p n : Nat) := ∀ x ∈ s, x.getLsbD p = true → x.getLsbD n = true

local instance (s : Pool) (p n : Nat) : Decidable (ordered s p n) := by unfold ordered; exact Finset.decidableDforallFinset

theorem preserve {t k s} (h : Can combine t k s) {p n} :
    ordered s p n → t.getLsbD p = true → t.getLsbD n = true := by
  induction h with
  | done ht => exact fun ho => ho _ ht
  | @step k s a b op ha hb _ ih =>
    intro ho; apply ih
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl|old
    · have h1 := ho a ha; have h2 := ho b hb
      cases op <;> simp [combine, BitVec.getLsbD_and, BitVec.getLsbD_or] <;> grind
    · exact ho x old

def Necessary (m : Nat) := ∀ a∈raw.toFinset, ∃ p n : Fin 20,
  m.testBit p = true ∧ m.testBit n = false ∧ ordered (start.erase a) p n

theorem obtainTree {m} (necessary : Necessary m) (h : RepSizeAtMost (plane m) 8) :
    ∃ t : W, Tree combine raw.toFinset t ∧ Can combine t 8 start ∧
       ∀ i : Fin 20, t.getLsbD i = m.testBit i := by
  obtain ⟨t,can,matchCells⟩ := representCan h
  obtain ⟨q,hs,hcard,hq,ht⟩ := tight combine can
  have sub : raw.toFinset ⊆ q := by
    intro a ha
    by_contra absent
    obtain ⟨p,n,hp,hn,ho⟩ := necessary a ha
    have ret : ordered q p n := by
      intro x hx; apply ho x (Finset.mem_erase.mpr ⟨by rintro rfl; exact absent hx,hs hx⟩)
    have bad := preserve hq ret ((matchCells p).trans hp)
    rw [matchCells n, hn] at bad
    contradiction
  have cardRaw : raw.toFinset.card = 9 := by decide
  have eq := Finset.eq_of_subset_of_card_le sub (by omega)
  have cq : q.card = 9 := eq ▸ cardRaw
  exact ⟨t,eq.symm ▸ ht cq,can,matchCells⟩

open Tight
abbrev Tags := BitVec 4
abbrev Bits := BitVec 8

def pack4 (f : Fin 4 → Bool) : BitVec 4 :=
  BitVec.ofBoolListLE [f 0, f 1, f 2, f 3]

theorem getPack4 (f : Fin 4 → Bool) (i : Fin 4) :
    (pack4 f).getLsbD i = f i := by
  unfold pack4; rw [BitVec.getLsbD_ofBoolListLE]; fin_cases i <;> rfl

def pack8 (f : Fin 8 → Bool) : BitVec 8 :=
  BitVec.ofBoolListLE [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7]

theorem getPack8 (f : Fin 8 → Bool) (i : Fin 8) :
    (pack8 f).getLsbD i = f i := by
  unfold pack8; rw [BitVec.getLsbD_ofBoolListLE]; fin_cases i <;> rfl

structure View where
  pick : Fin 4 → W
  probe : Fin 8 → Nat

def tags (v : View) (q : Pool) : Tags := pack4 fun i => decide (v.pick i ∈ q)
def bits (v : View) (x : W) : Bits := pack8 fun i => x.getLsbD (v.probe i)

theorem tags_union (v : View) (p q : Pool) : tags v (p ∪ q) = tags v p ||| tags v q := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  let j : Fin 4 := ⟨i,hi⟩
  change (tags v (p ∪ q)).getLsbD j = (tags v p ||| tags v q).getLsbD j
  simp only [tags, BitVec.getLsbD_or, getPack4, Finset.mem_union]
  by_cases hp : v.pick j ∈ p <;> by_cases hq : v.pick j ∈ q <;> simp [hp,hq]

theorem tags_disjoint (v : View) {p q : Pool} (hd : Disjoint p q) :
    tags v p &&& tags v q = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  let j : Fin 4 := ⟨i,hi⟩
  change (tags v p &&& tags v q).getLsbD j = _
  have ex : v.pick j ∈ p → v.pick j ∉ q := fun hp => Finset.disjoint_left.mp hd hp
  simp only [tags, BitVec.getLsbD_and, getPack4]
  by_cases h : v.pick j ∈ p <;> simp_all

theorem bits_gate (v : View) (op : Bool) (x y : W) :
    bits v (combine op x y) = if op then bits v x &&& bits v y else bits v x ||| bits v y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  let j : Fin 8 := ⟨i,hi⟩
  change (bits v (combine op x y)).getLsbD j = (if op then bits v x &&& bits v y else bits v x ||| bits v y).getLsbD j
  cases op <;> simp only [combine, Bool.false_eq_true, ite_false, ite_true, bits, BitVec.getLsbD_and, BitVec.getLsbD_or, getPack8]

-- Each entry lists the possible eight test answers for a given set of marked leaves.
def permitted (s : Tags) : Finset Bits :=
  ([{0},
    {0,49},
    {0,194},
    {0,49,194,243},
    {0,84},
    {0,16,49,84,117},
    {0,64,84,194,214},
    {0,16,49,64,80,84,113,117,194,210,214,243,247},
    {0,168},
    {0,32,49,168,185},
    {0,128,168,194,234},
    {0,32,49,128,160,168,177,185,194,226,234,243,251},
    {0,84,168,252},
    {0,16,32,48,49,84,116,117,168,184,185,252,253},
    {0,64,84,128,168,192,194,212,214,232,234,252,254},
    {0,16,32,48,49,64,80,84,96,113,116,117,128,144,160,168,177,184,185,192,194,210,212,214,226,232,234,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255}] : List (Finset Bits)).getD s.toNat ∅

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem closed : ∀ a b : Tags, a &&& b = 0 →
    ∀ x ∈ permitted a, ∀ y ∈ permitted b,
    x &&& y ∈ permitted (a ||| b) ∧ x ||| y ∈ permitted (a ||| b) := by decide +kernel

theorem missing : ∀ a : Tags, (112 : Bits) ∉ permitted a := by decide

def Leaves (v : View) := ∀ a∈raw.toFinset, bits v a ∈ permitted (tags v {a})

theorem treeView {v} (startOK : Leaves v) {p t} (h : Tree combine p t)
    (hs : p ⊆ raw.toFinset) : bits v t ∈ permitted (tags v p) := by
  induction h with
  | leaf x => exact startOK x (hs (by simp))
  | @node p q x y op hp hq hd ip iq =>
    have hxy := closed _ _ (tags_disjoint v hd) _
      (ip (Finset.Subset.trans Finset.subset_union_left hs)) _
      (iq (Finset.Subset.trans Finset.subset_union_right hs))
    rw [tags_union, bits_gate]
    cases op <;> first | exact hxy.1 | exact hxy.2

def Expected (m : Nat) (v : View) := ∀ i : Fin 8,
    (v.probe i < 20 ∧ m.testBit (v.probe i) = (112 : Bits).getLsbD i) ∨
    ((112 : Bits).getLsbD i = false ∧ ∃ n : Fin 20, m.testBit n = false ∧ ordered start (v.probe i) n)

theorem obstruction {m v} (hn : Necessary m) (hl : Leaves v) (he : Expected m v) :
    ¬ PEqualNP.Represents.RepSizeAtMost (plane m) 8 := by
  intro h
  obtain ⟨t,tree,can,matchCells⟩ := obtainTree hn h
  have hv := treeView hl tree (Finset.Subset.refl _)
  have eq : bits v t = (112 : Bits) := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    let j : Fin 8 := ⟨i,hi⟩
    change (bits v t).getLsbD j = (112 : Bits).getLsbD j
    rw [bits, getPack8]
    rcases he j with ⟨hb,hm⟩|⟨hz,n,hn,orderedSignals⟩
    · exact (matchCells ⟨_,hb⟩).trans hm
    · rw [hz]
      apply Bool.eq_false_iff.mpr; intro bad
      have no := preserve can orderedSignals bad
      rw [matchCells n,hn] at no
      contradiction
  exact missing _ (eq ▸ hv)

def cell (r : Fin 4) (c : Fin 5) : Fin 20 := ⟨5*r.val+c.val, by omega⟩
def rowWire (r : Fin 4) := raw.getD r.val 0
def colWire (c : Fin 5) := raw.getD (4+c.val) 0
def edge (m : Nat) (r : Fin 4) (c : Fin 5) := m.testBit (cell r c).val

def Mixed (m : Nat) :=
  (∀ r, ∃ c, edge m r c = true) ∧ (∀ r, ∃ c, edge m r c = false) ∧
  (∀ c, ∃ r, edge m r c = true) ∧ (∀ c, ∃ r, edge m r c = false)

def viewAt (r s : Fin 4) (c d : Fin 5) : View where
  pick i := [rowWire r,rowWire s,colWire c,colWire d].getD i.val 0
  probe i := [20+r.val,20+s.val,24+c.val,24+d.val,
    (cell r c).val,(cell r d).val,(cell s c).val,(cell s d).val].getD i.val 0

theorem rawCases : ∀ a∈raw.toFinset, (∃ r, a = rowWire r) ∨ (∃ c, a = colWire c) := by
  let : Decidable (∀ a∈raw.toFinset, (∃ r, a = rowWire r) ∨ (∃ c, a = colWire c)) :=
    Finset.decidableDforallFinset
  decide
theorem omitRow : ∀ r s c, r ≠ s → ordered (start.erase (rowWire r)) (cell r c) (cell s c) := by decide
theorem omitCol : ∀ c d r, c ≠ d → ordered (start.erase (colWire c)) (cell r c) (cell r d) := by decide
theorem rowSingleton : ∀ r c, ordered start (20+r.val) (cell r c) := by decide
theorem colSingleton : ∀ c r, ordered start (24+c.val) (cell r c) := by decide

theorem necessaryOfMixed {m} (hm : Mixed m) : Necessary m := by
  rcases hm with ⟨rowOne,rowZero,colOne,colZero⟩
  intro a ha
  rcases rawCases a ha with ⟨r,rfl⟩|⟨c,rfl⟩
  · obtain ⟨c,yes⟩ := rowOne r
    obtain ⟨s,no⟩ := colZero c
    have ne : r ≠ s := by rintro rfl; rw [yes] at no; contradiction
    exact ⟨cell r c,cell s c,yes,no,omitRow r s c ne⟩
  · obtain ⟨r,yes⟩ := colOne c
    obtain ⟨d,no⟩ := rowZero r
    have ne : c ≠ d := by rintro rfl; rw [yes] at no; contradiction
    exact ⟨cell r c,cell r d,yes,no,omitCol c d r ne⟩

def leavesDecision (v : View) : Decidable (Leaves v) :=
  Finset.decidableDforallFinset

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem leavesAt : ∀ (r s : Fin 4) (c d : Fin 5), r ≠ s → c ≠ d → Leaves (viewAt r s c d) := by
  have verified : ∀ (r s : Fin 4) (c d : Fin 5), r ≠ s → c ≠ d →
     @decide _ (leavesDecision (viewAt r s c d)) = true := by decide +kernel
  intro r s c d hr hc
  exact @of_decide_eq_true _ (leavesDecision (viewAt r s c d)) (verified r s c d hr hc)

-- A three-corner block in a matrix with both values in every row and column
-- excludes every circuit of size at most eight, with arbitrary sharing.
theorem mixedCorners {m : Nat} (hm : Mixed m) {r s : Fin 4} {c d : Fin 5}
    (a : edge m r c = true) (b : edge m r d = true)
    (e : edge m s c = true) (f : edge m s d = false) :
    ¬ PEqualNP.Represents.RepSizeAtMost (plane m) 8 := by
  have rs : r ≠ s := by rintro rfl; rw [b] at f; contradiction
  have cd : c ≠ d := by rintro rfl; rw [e] at f; contradiction
  apply obstruction (necessaryOfMixed hm) (leavesAt r s c d rs cd)
  have rz (u : Fin 4) : ∃ n : Fin 20, m.testBit n = false ∧ ordered start (20+u.val) n := by
    obtain ⟨v,h⟩ := hm.2.1 u
    exact ⟨cell u v,h,rowSingleton u v⟩
  have cz (v : Fin 5) : ∃ n : Fin 20, m.testBit n = false ∧ ordered start (24+v.val) n := by
    obtain ⟨u,h⟩ := hm.2.2.2 v
    exact ⟨cell u v,h,colSingleton v u⟩
  intro i
  fin_cases i
  · exact Or.inr ⟨rfl,rz r⟩
  · exact Or.inr ⟨rfl,rz s⟩
  · exact Or.inr ⟨rfl,cz c⟩
  · exact Or.inr ⟨rfl,cz d⟩
  · exact Or.inl ⟨(cell r c).isLt,a⟩
  · exact Or.inl ⟨(cell r d).isLt,b⟩
  · exact Or.inl ⟨(cell s c).isLt,e⟩
  · exact Or.inl ⟨(cell s d).isLt,f⟩

open PEqualNP.Represents PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def makeGate (p : Bool × Nat × Nat) : Gate := ⟨if p.1 then .and else .or, [p.2.1,p.2.2]⟩
def circuit (gates : List (Bool × Nat × Nat)) (out : Nat) : Circuit := ⟨gates.map makeGate, out⟩

theorem goodCircuit (gs : List (Bool × Nat × Nat)) (out : Nat) : Monotone2 (circuit gs out) := by
  intro g hg
  obtain ⟨⟨op,a,b⟩,_,rfl⟩ := List.mem_map.mp hg
  cases op <;> simp [makeGate]

theorem lower33885 : ¬ RepSizeAtMost (plane 33885) 8 :=
  mixedCorners (r := 0) (s := 2) (c := 0) (d := 2)
    (by unfold Mixed; decide) (by decide) (by decide) (by decide) (by decide)

theorem upper33885 : RepSizeAtMost (plane 33885) 9 :=
  ⟨circuit [(false,7,8), (false,6,9), (false,4,10), (true,0,11), (true,1,5), (false,12,13), (false,2,3), (true,4,15), (false,14,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem lower33886 : ¬ RepSizeAtMost (plane 33886) 8 :=
  mixedCorners (r := 0) (s := 1) (c := 1) (d := 2)
    (by unfold Mixed; decide) (by decide) (by decide) (by decide) (by decide)

theorem upper33886 : RepSizeAtMost (plane 33886) 9 :=
  ⟨circuit [(false,7,8), (false,6,9), (false,5,10), (true,0,11), (true,1,5), (false,12,13), (false,2,3), (true,4,15), (false,14,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem lower33916 : ¬ RepSizeAtMost (plane 33916) 8 :=
  mixedCorners (r := 1) (s := 2) (c := 0) (d := 1)
    (by unfold Mixed; decide) (by decide) (by decide) (by decide) (by decide)

theorem upper33916 : RepSizeAtMost (plane 33916) 9 :=
  ⟨circuit [(false,7,8), (false,6,9), (true,0,10), (false,4,5), (true,1,12), (false,11,13), (false,2,3), (true,4,15), (false,14,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem lower34009 : ¬ RepSizeAtMost (plane 34009) 8 :=
  mixedCorners (r := 0) (s := 2) (c := 0) (d := 3)
    (by unfold Mixed; decide) (by decide) (by decide) (by decide) (by decide)

theorem upper34009 : RepSizeAtMost (plane 34009) 9 :=
  ⟨circuit [(false,7,8), (false,4,9), (true,0,10), (false,5,6), (true,1,12), (false,11,13), (false,2,3), (true,4,15), (false,14,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem lower34010 : ¬ RepSizeAtMost (plane 34010) 8 :=
  mixedCorners (r := 0) (s := 1) (c := 1) (d := 3)
    (by unfold Mixed; decide) (by decide) (by decide) (by decide) (by decide)

theorem upper34010 : RepSizeAtMost (plane 34010) 9 :=
  ⟨circuit [(false,7,8), (false,5,9), (true,0,10), (false,5,6), (true,1,12), (false,11,13), (false,2,3), (true,4,15), (false,14,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem lower34014 : ¬ RepSizeAtMost (plane 34014) 8 :=
  mixedCorners (r := 0) (s := 1) (c := 1) (d := 3)
    (by unfold Mixed; decide) (by decide) (by decide) (by decide) (by decide)

theorem upper34014 : RepSizeAtMost (plane 34014) 9 :=
  ⟨circuit [(false,5,6), (false,7,8), (false,9,10), (true,0,11), (true,1,9), (false,12,13), (false,2,3), (true,4,15), (false,14,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem lower34262 : ¬ RepSizeAtMost (plane 34262) 8 :=
  mixedCorners (r := 0) (s := 1) (c := 1) (d := 4)
    (by unfold Mixed; decide) (by decide) (by decide) (by decide) (by decide)

theorem upper34262 : RepSizeAtMost (plane 34262) 9 :=
  ⟨circuit [(false,5,6), (false,8,9), (true,0,10), (false,7,9), (true,1,12), (false,11,13), (false,2,3), (true,4,15), (false,14,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem lower34270 : ¬ RepSizeAtMost (plane 34270) 8 :=
  mixedCorners (r := 0) (s := 1) (c := 1) (d := 4)
    (by unfold Mixed; decide) (by decide) (by decide) (by decide) (by decide)

theorem upper34270 : RepSizeAtMost (plane 34270) 9 :=
  ⟨circuit [(false,6,7), (false,5,9), (false,8,10), (true,0,11), (true,1,10), (false,12,13), (false,2,3), (true,4,15), (false,14,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem lower34940 : ¬ RepSizeAtMost (plane 34940) 8 :=
  mixedCorners (r := 1) (s := 2) (c := 1) (d := 0)
    (by unfold Mixed; decide) (by decide) (by decide) (by decide) (by decide)

theorem upper34940 : RepSizeAtMost (plane 34940) 9 :=
  ⟨circuit [(false,1,3), (true,4,9), (false,1,2), (true,5,11), (false,10,12), (false,7,8), (false,6,14), (true,0,15), (false,13,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem lower34969 : ¬ RepSizeAtMost (plane 34969) 8 :=
  mixedCorners (r := 0) (s := 3) (c := 0) (d := 3)
    (by unfold Mixed; decide) (by decide) (by decide) (by decide) (by decide)

theorem upper34969 : RepSizeAtMost (plane 34969) 9 :=
  ⟨circuit [(false,7,8), (false,4,9), (true,0,10), (true,1,6), (false,11,12), (true,2,5), (false,13,14), (true,3,4), (false,15,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem lower35000 : ¬ RepSizeAtMost (plane 35000) 8 :=
  mixedCorners (r := 1) (s := 3) (c := 0) (d := 2)
    (by unfold Mixed; decide) (by decide) (by decide) (by decide) (by decide)

theorem upper35000 : RepSizeAtMost (plane 35000) 9 :=
  ⟨circuit [(false,7,8), (true,0,9), (false,4,6), (true,1,11), (false,10,12), (true,2,5), (false,13,14), (true,3,4), (false,15,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem lower35220 : ¬ RepSizeAtMost (plane 35220) 8 :=
  mixedCorners (r := 0) (s := 1) (c := 2) (d := 4)
    (by unfold Mixed; decide) (by decide) (by decide) (by decide) (by decide)

theorem upper35220 : RepSizeAtMost (plane 35220) 9 :=
  ⟨circuit [(false,6,8), (true,0,9), (false,6,7), (true,1,11), (false,10,12), (true,2,5), (false,13,14), (true,3,4), (false,15,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem lower35228 : ¬ RepSizeAtMost (plane 35228) 8 :=
  mixedCorners (r := 0) (s := 1) (c := 2) (d := 4)
    (by unfold Mixed; decide) (by decide) (by decide) (by decide) (by decide)

theorem upper35228 : RepSizeAtMost (plane 35228) 9 :=
  ⟨circuit [(false,6,7), (false,8,9), (true,0,10), (true,1,9), (false,11,12), (true,2,5), (false,13,14), (true,3,4), (false,15,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem lower35741 : ¬ RepSizeAtMost (plane 35741) 8 :=
  mixedCorners (r := 0) (s := 1) (c := 2) (d := 0)
    (by unfold Mixed; decide) (by decide) (by decide) (by decide) (by decide)

theorem upper35741 : RepSizeAtMost (plane 35741) 9 :=
  ⟨circuit [(false,0,3), (true,4,9), (true,2,5), (false,10,11), (false,7,8), (false,6,13), (false,0,1), (true,14,15), (false,12,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem lower35773 : ¬ RepSizeAtMost (plane 35773) 8 :=
  mixedCorners (r := 0) (s := 3) (c := 0) (d := 2)
    (by unfold Mixed; decide) (by decide) (by decide) (by decide) (by decide)

theorem upper35773 : RepSizeAtMost (plane 35773) 9 :=
  ⟨circuit [(false,0,1), (false,7,8), (false,6,10), (false,4,11), (true,9,12), (true,2,5), (false,13,14), (true,3,4), (false,15,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem lower35964 : ¬ RepSizeAtMost (plane 35964) 8 :=
  mixedCorners (r := 1) (s := 3) (c := 0) (d := 1)
    (by unfold Mixed; decide) (by decide) (by decide) (by decide) (by decide)

theorem upper35964 : RepSizeAtMost (plane 35964) 9 :=
  ⟨circuit [(false,7,8), (false,6,9), (true,0,10), (false,1,2), (false,4,5), (true,12,13), (false,11,14), (true,3,4), (false,15,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem lower36764 : ¬ RepSizeAtMost (plane 36764) 8 :=
  mixedCorners (r := 2) (s := 3) (c := 0) (d := 1)
    (by unfold Mixed; decide) (by decide) (by decide) (by decide) (by decide)

theorem upper36764 : RepSizeAtMost (plane 36764) 9 :=
  ⟨circuit [(false,0,1), (false,7,8), (false,6,10), (true,9,11), (false,4,5), (true,2,13), (false,12,14), (true,3,4), (false,15,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem lower39129 : ¬ RepSizeAtMost (plane 39129) 8 :=
  mixedCorners (r := 0) (s := 3) (c := 0) (d := 3)
    (by unfold Mixed; decide) (by decide) (by decide) (by decide) (by decide)

theorem upper39129 : RepSizeAtMost (plane 39129) 9 :=
  ⟨circuit [(false,7,8), (false,4,9), (true,0,10), (false,1,2), (false,5,6), (true,12,13), (false,11,14), (true,3,4), (false,15,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem lower39130 : ¬ RepSizeAtMost (plane 39130) 8 :=
  mixedCorners (r := 0) (s := 1) (c := 1) (d := 3)
    (by unfold Mixed; decide) (by decide) (by decide) (by decide) (by decide)

theorem upper39130 : RepSizeAtMost (plane 39130) 9 :=
  ⟨circuit [(false,7,8), (false,5,9), (true,0,10), (false,1,2), (false,5,6), (true,12,13), (false,11,14), (true,3,4), (false,15,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem lower39134 : ¬ RepSizeAtMost (plane 39134) 8 :=
  mixedCorners (r := 0) (s := 1) (c := 1) (d := 3)
    (by unfold Mixed; decide) (by decide) (by decide) (by decide) (by decide)

theorem upper39134 : RepSizeAtMost (plane 39134) 9 :=
  ⟨circuit [(false,5,6), (false,7,8), (false,9,10), (true,0,11), (false,1,2), (true,9,13), (false,12,14), (true,3,4), (false,15,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem lower39160 : ¬ RepSizeAtMost (plane 39160) 8 :=
  mixedCorners (r := 1) (s := 2) (c := 1) (d := 0)
    (by unfold Mixed; decide) (by decide) (by decide) (by decide) (by decide)

theorem upper39160 : RepSizeAtMost (plane 39160) 9 :=
  ⟨circuit [(false,1,3), (true,4,9), (false,5,6), (false,1,2), (true,11,12), (false,10,13), (false,7,8), (true,0,15), (false,14,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem lower39710 : ¬ RepSizeAtMost (plane 39710) 8 :=
  mixedCorners (r := 0) (s := 1) (c := 3) (d := 1)
    (by unfold Mixed; decide) (by decide) (by decide) (by decide) (by decide)

theorem upper39710 : RepSizeAtMost (plane 39710) 9 :=
  ⟨circuit [(true,3,4), (false,5,6), (false,0,2), (true,10,11), (false,9,12), (false,7,8), (false,0,1), (true,14,15), (false,13,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem lower39737 : ¬ RepSizeAtMost (plane 39737) 8 :=
  mixedCorners (r := 0) (s := 3) (c := 0) (d := 3)
    (by unfold Mixed; decide) (by decide) (by decide) (by decide) (by decide)

theorem upper39737 : RepSizeAtMost (plane 39737) 9 :=
  ⟨circuit [(false,0,1), (false,7,8), (false,4,10), (true,9,11), (false,5,6), (true,2,13), (false,12,14), (true,3,4), (false,15,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem lower39770 : ¬ RepSizeAtMost (plane 39770) 8 :=
  mixedCorners (r := 0) (s := 2) (c := 1) (d := 3)
    (by unfold Mixed; decide) (by decide) (by decide) (by decide) (by decide)

theorem upper39770 : RepSizeAtMost (plane 39770) 9 :=
  ⟨circuit [(false,0,1), (false,7,8), (false,5,10), (true,9,11), (false,5,6), (true,2,13), (false,12,14), (true,3,4), (false,15,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem lower39902 : ¬ RepSizeAtMost (plane 39902) 8 :=
  mixedCorners (r := 0) (s := 2) (c := 1) (d := 3)
    (by unfold Mixed; decide) (by decide) (by decide) (by decide) (by decide)

theorem upper39902 : RepSizeAtMost (plane 39902) 9 :=
  ⟨circuit [(false,0,1), (false,5,6), (false,7,8), (false,10,11), (true,9,12), (true,2,10), (false,13,14), (true,3,4), (false,15,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem lower47574 : ¬ RepSizeAtMost (plane 47574) 8 :=
  mixedCorners (r := 0) (s := 1) (c := 1) (d := 4)
    (by unfold Mixed; decide) (by decide) (by decide) (by decide) (by decide)

theorem upper47574 : RepSizeAtMost (plane 47574) 9 :=
  ⟨circuit [(false,5,6), (false,8,9), (true,0,10), (false,1,2), (false,7,9), (true,12,13), (false,11,14), (true,3,4), (false,15,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem lower47582 : ¬ RepSizeAtMost (plane 47582) 8 :=
  mixedCorners (r := 0) (s := 1) (c := 1) (d := 4)
    (by unfold Mixed; decide) (by decide) (by decide) (by decide) (by decide)

theorem upper47582 : RepSizeAtMost (plane 47582) 9 :=
  ⟨circuit [(false,6,7), (false,5,9), (false,8,10), (true,0,11), (false,1,2), (true,10,13), (false,12,14), (true,3,4), (false,15,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem lower48094 : ¬ RepSizeAtMost (plane 48094) 8 :=
  mixedCorners (r := 0) (s := 2) (c := 1) (d := 4)
    (by unfold Mixed; decide) (by decide) (by decide) (by decide) (by decide)

theorem upper48094 : RepSizeAtMost (plane 48094) 9 :=
  ⟨circuit [(false,0,1), (false,6,7), (false,5,10), (false,8,11), (true,9,12), (true,2,11), (false,13,14), (true,3,4), (false,15,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem lower101560 : ¬ RepSizeAtMost (plane 101560) 8 :=
  mixedCorners (r := 1) (s := 2) (c := 0) (d := 2)
    (by unfold Mixed; decide) (by decide) (by decide) (by decide) (by decide)

theorem upper101560 : RepSizeAtMost (plane 101560) 9 :=
  ⟨circuit [(false,7,8), (true,0,9), (false,4,6), (true,1,11), (false,10,12), (false,2,3), (false,4,5), (true,14,15), (false,13,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem lower101624 : ¬ RepSizeAtMost (plane 101624) 8 :=
  mixedCorners (r := 1) (s := 2) (c := 0) (d := 2)
    (by unfold Mixed; decide) (by decide) (by decide) (by decide) (by decide)

theorem upper101624 : RepSizeAtMost (plane 101624) 9 :=
  ⟨circuit [(false,7,8), (true,0,9), (false,4,5), (false,6,11), (true,1,12), (false,10,13), (false,2,3), (true,11,15), (false,14,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem lower101780 : ¬ RepSizeAtMost (plane 101780) 8 :=
  mixedCorners (r := 0) (s := 1) (c := 2) (d := 4)
    (by unfold Mixed; decide) (by decide) (by decide) (by decide) (by decide)

theorem upper101780 : RepSizeAtMost (plane 101780) 9 :=
  ⟨circuit [(false,6,8), (true,0,9), (false,6,7), (true,1,11), (false,10,12), (false,2,3), (false,4,5), (true,14,15), (false,13,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem lower101788 : ¬ RepSizeAtMost (plane 101788) 8 :=
  mixedCorners (r := 0) (s := 1) (c := 2) (d := 4)
    (by unfold Mixed; decide) (by decide) (by decide) (by decide) (by decide)

theorem upper101788 : RepSizeAtMost (plane 101788) 9 :=
  ⟨circuit [(false,6,7), (false,8,9), (true,0,10), (true,1,9), (false,11,12), (false,2,3), (false,4,5), (true,14,15), (false,13,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

theorem lower105720 : ¬ RepSizeAtMost (plane 105720) 8 :=
  mixedCorners (r := 1) (s := 3) (c := 0) (d := 2)
    (by unfold Mixed; decide) (by decide) (by decide) (by decide) (by decide)

theorem upper105720 : RepSizeAtMost (plane 105720) 9 :=
  ⟨circuit [(false,7,8), (true,0,9), (false,1,2), (false,4,5), (false,6,12), (true,11,13), (false,10,14), (true,3,12), (false,15,16)] 17,
    goodCircuit _ _, by decide, by decide⟩

def masks : List Nat := [33885, 33886, 33916, 34009, 34010, 34014, 34262, 34270, 34940, 34969, 35000, 35220, 35228, 35741, 35773, 35964, 36764, 39129, 39130, 39134, 39160, 39710, 39737, 39770, 39902, 47574, 47582, 48094, 101560, 101624, 101780, 101788, 105720]

theorem exactList : ∀ m ∈ masks, (¬ RepSizeAtMost (plane m) 8) ∧ RepSizeAtMost (plane m) 9 := by
  intro m hm
  simp only [masks, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨lower33885,upper33885⟩
  · exact ⟨lower33886,upper33886⟩
  · exact ⟨lower33916,upper33916⟩
  · exact ⟨lower34009,upper34009⟩
  · exact ⟨lower34010,upper34010⟩
  · exact ⟨lower34014,upper34014⟩
  · exact ⟨lower34262,upper34262⟩
  · exact ⟨lower34270,upper34270⟩
  · exact ⟨lower34940,upper34940⟩
  · exact ⟨lower34969,upper34969⟩
  · exact ⟨lower35000,upper35000⟩
  · exact ⟨lower35220,upper35220⟩
  · exact ⟨lower35228,upper35228⟩
  · exact ⟨lower35741,upper35741⟩
  · exact ⟨lower35773,upper35773⟩
  · exact ⟨lower35964,upper35964⟩
  · exact ⟨lower36764,upper36764⟩
  · exact ⟨lower39129,upper39129⟩
  · exact ⟨lower39130,upper39130⟩
  · exact ⟨lower39134,upper39134⟩
  · exact ⟨lower39160,upper39160⟩
  · exact ⟨lower39710,upper39710⟩
  · exact ⟨lower39737,upper39737⟩
  · exact ⟨lower39770,upper39770⟩
  · exact ⟨lower39902,upper39902⟩
  · exact ⟨lower47574,upper47574⟩
  · exact ⟨lower47582,upper47582⟩
  · exact ⟨lower48094,upper48094⟩
  · exact ⟨lower101560,upper101560⟩
  · exact ⟨lower101624,upper101624⟩
  · exact ⟨lower101780,upper101780⟩
  · exact ⟨lower101788,upper101788⟩
  · exact ⟨lower105720,upper105720⟩

end PEqualNP.Outside.TightFamily_aux

theorem PEqualNP.Outside.TightFamily :
  (∀ (m : Nat) (r s : Fin 4) (c d : Fin 5),
    ((∀ (u : Fin 4), ∃ (v : Fin 5), m.testBit (5 * u.val + v.val) = true) ∧
     (∀ (u : Fin 4), ∃ (v : Fin 5), m.testBit (5 * u.val + v.val) = false) ∧
     (∀ (v : Fin 5), ∃ (u : Fin 4), m.testBit (5 * u.val + v.val) = true) ∧
     (∀ (v : Fin 5), ∃ (u : Fin 4), m.testBit (5 * u.val + v.val) = false)) →
    m.testBit (5 * r.val + c.val) = true → m.testBit (5 * r.val + d.val) = true →
    m.testBit (5 * s.val + c.val) = true → m.testBit (5 * s.val + d.val) = false →
    ¬ PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => m.testBit (5 * u.val + v.val)) 8) ∧
  (∀ m ∈ ([33885, 33886, 33916, 34009, 34010, 34014, 34262, 34270, 34940, 34969, 35000, 35220, 35228, 35741, 35773, 35964, 36764, 39129, 39130, 39134, 39160, 39710, 39737, 39770, 39902, 47574, 47582, 48094, 101560, 101624, 101780, 101788, 105720] : List Nat),
    (¬ PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => m.testBit (5 * u.val + v.val)) 8) ∧ PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => m.testBit (5 * u.val + v.val)) 9) := by
  constructor
  · intro m r s c d mixed a b e f
    exact PEqualNP.Outside.TightFamily_aux.mixedCorners (r := r) (s := s) (c := c) (d := d) mixed a b e f
  · exact PEqualNP.Outside.TightFamily_aux.exactList
