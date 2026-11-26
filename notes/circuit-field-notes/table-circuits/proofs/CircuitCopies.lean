import PEqualNP.Outside.FormulaGap

namespace PEqualNP.Outside.CircuitCopies_aux

open PEqualNP.Outside.FormulaGap_aux PEqualNP.Outside.FormulaGap_aux.Tight
open PEqualNP.Represents

noncomputable section
open scoped Classical

abbrev Covered {X : Type} (w : List (Sig X)) (f : Sig X) :=
  f ∈ w ∨ f = zeroS ∨ f = oneS

private theorem const_left {X : Type} (op : Bool) (a b : Sig X)
    (h : a = zeroS ∨ a = oneS) :
    bin op a b = zeroS ∨ bin op a b = oneS ∨ bin op a b = b := by
  rcases h with h|h <;> rw [h] <;> cases op
  · right; right; funext x; simp [bin,zeroS]
  · left; funext x; simp [bin,zeroS]
  · right; left; funext x; simp [bin,oneS]
  · right; right; funext x; simp [bin,oneS]

private theorem const_right {X : Type} (op : Bool) (a b : Sig X)
    (h : b = zeroS ∨ b = oneS) :
    bin op a b = zeroS ∨ bin op a b = oneS ∨ bin op a b = a := by
  rcases h with h|h <;> rw [h] <;> cases op
  · right; right; funext x; simp [bin,zeroS]
  · left; funext x; simp [bin,zeroS]
  · right; left; funext x; simp [bin,oneS]
  · right; right; funext x; simp [bin,oneS]

-- Constants in the semantic basis are free. Eliminate them before emitting real gates.
private theorem realize {X : Type} [Fintype X] {g : Sig X} {k s}
    (h : Can bin g k s) : ∀ {w : List (Sig X)}, (∀ a ∈ s, Covered w a) →
      ∃ j ≤ k, ∃ v, Extend w j v ∧ Covered v g := by
  induction h with
  | done h => exact fun cover => ⟨0,Nat.zero_le _,_,.start,cover _ h⟩
  | @step k s a b op ha hb _ ih =>
    intro w cover
    by_cases seen : Covered w (bin op a b)
    · obtain ⟨j,hj,v,ext,out⟩ := ih (w := w) (by
        intro f hf
        rcases Finset.mem_insert.mp hf with rfl|hf
        · exact seen
        · exact cover f hf)
      exact ⟨j,by omega,v,ext,out⟩
    · have actual {x y : Sig X} (hx : Covered w x) (hy : Covered w y)
          (hc : x = zeroS ∨ x = oneS →
            bin op a b = zeroS ∨ bin op a b = oneS ∨ bin op a b = y) : x ∈ w := by
        rcases hx with h|h
        · exact h
        · rcases hc h with eq|eq|eq
          · exact False.elim (seen (.inr (.inl eq)))
          · exact False.elim (seen (.inr (.inr eq)))
          · exact False.elim (seen (eq ▸ hy))
      have p : Extend w 1 (w ++ [bin op a b]) := .gate .start op
        (actual (cover _ ha) (cover _ hb) (const_left op a b))
        (actual (cover _ hb) (cover _ ha) (const_right op a b))
      obtain ⟨j,hj,v,ext,out⟩ := ih (w := w ++ [bin op a b]) (by
        intro f hf
        rcases Finset.mem_insert.mp hf with rfl|hf
        · exact .inl (by simp)
        · rcases cover f hf with old|constant
          · exact .inl (List.mem_append_left _ old)
          · exact .inr constant)
      exact ⟨1+j,by omega,v,compose p ext,out⟩

abbrev rowS {R C} (r : Fin R) : Sig (Cell R C) := fun p => decide (r = p.1)
abbrev colS {R C} (c : Fin C) : Sig (Cell R C) := fun p => decide (c = p.2)

private theorem basis {R C} {f : Sig (Cell R C)} (hf : f ∈ pool) :
    f = zeroS ∨ f = oneS ∨ (∃ r, f = rowS r) ∨ (∃ c, f = colS c) := by
  simp only [pool,Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and] at hf
  rcases hf with h|h|⟨i,rfl⟩
  · exact .inl h
  · exact .inr (.inl h)
  · apply Or.inr; apply Or.inr
    refine Fin.addCases (fun r => ?_) (fun c => ?_) i
    · exact .inl ⟨r, by ext p; simp [rawWire,bits,rowS]⟩
    · exact .inr ⟨c, by ext p; simp [rawWire,bits,colS]⟩

private theorem represented {R C k} {g : Sig (Cell R C)}
    (h : Can bin g k pool) (p q : Cell R C) (hp : g p = true) (hq : g q = false) :
    RepSizeAtMost (fun r c => g (r,c)) k := by
  obtain ⟨j,hj,w,ext,out⟩ := realize h (w := inputs R C) (by
    intro f hf
    rcases basis hf with e|e|⟨r,rfl⟩|⟨c,rfl⟩
    · exact .inr (.inl e)
    · exact .inr (.inr e)
    · exact .inl (rawRow r)
    · exact .inl (rawCol c))
  rcases out with out|e|e
  · obtain ⟨circ,ops,size,ev⟩ := circuitFrom g ext out
    exact ⟨circ,ops,size.trans hj,ev⟩
  · rw [e] at hp; contradiction
  · rw [e] at hq; contradiction

def pull {X Y : Type} (e : Y → X) (f : Sig X) : Sig Y := fun y => f (e y)

private theorem mapCan {X Y : Type} [Fintype X] [Fintype Y]
    {g : Sig X} {k s} (h : Can bin g k s) (e : Y → X) :
    ∀ {t : Finset (Sig Y)}, (∀ f ∈ s, pull e f ∈ t) → Can bin (pull e g) k t := by
  induction h with
  | done hf => exact fun inc => .done (inc _ hf)
  | @step k s a b op ha hb _ ih =>
    intro t inc
    apply Can.step op (inc _ ha) (inc _ hb)
    apply ih
    intro f hf
    rcases Finset.mem_insert.mp hf with rfl|hf
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (inc _ hf)

-- Locate the first gate reading a signal that distinguishes p from q. Under
-- restriction that signal vanishes and the gate becomes either zero or a wire.
private theorem saveGate {X Y : Type} [Fintype X] [Fintype Y] {g : Sig X}
    {k s} (h : Can bin g k s) (v : Sig X) (p q : X)
    (hp : g p = true) (hq : g q = false) (gn : g ≠ v)
    (e : Y → X) (hv : pull e v = zeroS) :
    ∀ {t : Finset (Sig Y)}, zeroS ∈ t → (∀ f ∈ s, pull e f ∈ t) →
    (∀ f ∈ s, f ≠ v → f p = true → f q = true) →
    ∃ j < k, Can bin (pull e g) j t := by
  induction h with
  | done ht => intro t _ _ ord; have := ord _ ht gn hp; simp_all
  | @step k s a b op ha hb rest ih =>
    intro t zero inc ord
    by_cases uses : a = v ∨ b = v
    · have collapsed : pull e (bin op a b) ∈ t := by
        change bin op (pull e a) (pull e b) ∈ t
        rcases uses with use|use
        · rw [use,hv]
          cases op
          · have he : bin false zeroS (pull e b) = pull e b := by funext y; simp [bin,zeroS]
            rw [he]; exact inc b hb
          · exact zero
        · rw [use,hv]
          cases op
          · have he : bin false (pull e a) zeroS = pull e a := by funext y; simp [bin,zeroS]
            rw [he]; exact inc a ha
          · have he : bin true (pull e a) zeroS = zeroS := by funext y; simp [bin,zeroS]
            rw [he]; exact zero
      refine ⟨k,by omega,mapCan rest e ?_⟩
      intro f hf
      rcases Finset.mem_insert.mp hf with rfl|hf
      · exact collapsed
      · exact inc _ hf
    · obtain ⟨an,bn⟩ := not_or.mp uses
      obtain ⟨j,hj,short⟩ := ih (t := insert (bin op (pull e a) (pull e b)) t)
        (Finset.mem_insert_of_mem zero) (by
          intro f hf; rcases Finset.mem_insert.mp hf with rfl|hf
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (inc _ hf)) (by
          intro f hf ne ht
          rcases Finset.mem_insert.mp hf with rfl|hf
          · have A := ord a ha an; have B := ord b hb bn
            cases op <;> simp [bin] at ht ⊢ <;> tauto
          · exact ord f hf ne ht)
      exact ⟨j+1,by omega,.step op (inc _ ha) (inc _ hb) short⟩

def copyIndex {R : Nat} (u : Fin R) (i : Fin (R+1)) : Fin R := Fin.lastCases u id i

private theorem rowPool {R C} (r : Fin R) : @rowS R C r ∈ pool := entries _ (rawRow r)
private theorem colPool {R C} (c : Fin C) : @colS R C c ∈ pool := entries _ (rawCol c)

theorem rowCost {R C} (g : Sig (Cell R C)) (u s : Fin R) (c : Fin C)
    (hp : g (u,c) = true) (hq : g (s,c) = false) (k : Nat) :
    RepSizeAtMost (fun r j => g (copyIndex u r,j)) k ↔
    ∃ j < k, RepSizeAtMost (fun r j => g (r,j)) j := by
  let project : Cell (R+1) C → Cell R C := fun p => (copyIndex u p.1,p.2)
  let embed : Cell R C → Cell (R+1) C := fun p => (p.1.castSucc,p.2)
  let dup := pull project g
  let v : Sig (Cell (R+1) C) := rowS (Fin.last R)
  have original (r : Fin R) : copyIndex u r.castSucc = r := by simp [copyIndex]
  have last : copyIndex u (Fin.last R) = u := by simp [copyIndex]
  have condense : pull embed dup = g := by funext p; simp [pull,embed,dup,project,original]
  have away (i : Fin R) : Fin.last R ≠ i.castSucc := (Fin.castSucc_ne_last i).symm
  have hz : pull embed v = zeroS := by funext p; simp [v,rowS,embed,pull,zeroS,away]
  have good : dup (Fin.last R,c) = true := by simpa [dup,pull,project,last] using hp
  have bad : dup (s.castSucc,c) = false := by simpa [dup,pull,project,original] using hq
  constructor
  · intro large
    have sem : Can bin dup k pool := circuitMeans large
    have distinct : dup ≠ v := by
      intro eq
      have a := congrFun eq (u.castSucc,c)
      simp [dup,pull,project,original,hp,v,rowS,away] at a
    obtain ⟨j,less,small⟩ := saveGate sem v (Fin.last R,c) (s.castSucc,c) good bad distinct embed hz
      (t := pool) (by simp [pool]) (by
        intro f hf
        rcases basis hf with rfl|rfl|⟨r,rfl⟩|⟨d,rfl⟩
        · change zeroS ∈ pool; simp [pool]
        · change oneS ∈ pool; simp [pool]
        · refine Fin.lastCases ?_ (fun i => ?_) r
          · change pull embed v ∈ pool; rw [hz]; simp [pool]
          · have eq : pull embed (rowS i.castSucc) = rowS i := by funext p; simp [pull,embed,rowS]
            rw [eq]; exact rowPool _
        · exact colPool d) (by
        intro f hf ne htrue
        rcases basis hf with rfl|rfl|⟨r,rfl⟩|⟨d,rfl⟩
        · contradiction
        · rfl
        · have he : r = Fin.last R := of_decide_eq_true htrue
          exact False.elim (ne (he ▸ rfl))
        · exact htrue)
    rw [condense] at small
    exact ⟨j,less,represented small _ _ hp hq⟩
  · rintro ⟨j,less,small⟩
    let join := bin false (@rowS (R+1) C u.castSucc) v
    have sem : Can bin dup j (insert join pool) := by
      apply mapCan (circuitMeans small) project
      intro f hf
      rcases basis hf with rfl|rfl|⟨i,rfl⟩|⟨d,rfl⟩
      · apply Finset.mem_insert_of_mem; change zeroS ∈ pool; simp [pool]
      · apply Finset.mem_insert_of_mem; change oneS ∈ pool; simp [pool]
      · by_cases he : i = u
        · subst i
          have eq : pull project (rowS u) = join := by
            funext p
            obtain ⟨r,d⟩ := p
            refine Fin.lastCases ?_ (fun i => ?_) r <;> simp [pull,project,rowS,join,v,bin,original,last,away]
          exact eq ▸ Finset.mem_insert_self _ _
        · have eq : pull project (rowS i) = rowS i.castSucc := by
            funext p
            obtain ⟨r,d⟩ := p
            refine Fin.lastCases ?_ (fun j => ?_) r <;> simp [pull,project,rowS,original,last,he]
          exact Finset.mem_insert_of_mem (eq ▸ rowPool _)
      · exact Finset.mem_insert_of_mem (colPool d)
    have full : Can bin dup (j+1) pool := .step false (rowPool _) (rowPool _) sem
    exact represented (budget bin full (by omega : j+1 ≤ k)) _ _ good bad

-- Relabel the two shores. This transports shared gates without expanding them into a formula.
theorem swapCost {R C} (g : Sig (Cell R C)) (p q : Cell R C)
    (hp : g p = true) (hq : g q = false) {k}
    (h : RepSizeAtMost (fun r c => g (r,c)) k) : RepSizeAtMost (fun c r => g (r,c)) k := by
  let swap : Cell C R → Cell R C := Prod.swap
  have sem : Can bin (pull swap g) k pool := by
    apply mapCan (circuitMeans h) swap
    intro f hf
    rcases basis hf with rfl|rfl|⟨r,rfl⟩|⟨c,rfl⟩
    · change zeroS ∈ pool; simp [pool]
    · change oneS ∈ pool; simp [pool]
    · exact colPool r
    · exact rowPool c
  exact represented sem p.swap q.swap hp hq

theorem columnCost {R C} (g : Sig (Cell R C)) (u s : Fin C) (r : Fin R)
    (hp : g (r,u) = true) (hq : g (r,s) = false) (k : Nat) :
    RepSizeAtMost (fun i c => g (i,copyIndex u c)) k ↔
    ∃ j < k, RepSizeAtMost (fun i c => g (i,c)) j := by
  let colG : Sig (Cell R (C+1)) := fun p => g (p.1,copyIndex u p.2)
  have h1 : colG (r,u.castSucc) = true := by simpa [colG,copyIndex] using hp
  have h0 : colG (r,s.castSucc) = false := by simpa [colG,copyIndex] using hq
  have eq := rowCost (fun p : Cell C R => g p.swap) u s r hp hq k
  constructor
  · intro h
    obtain ⟨j,lt,rep⟩ := eq.mp (swapCost colG _ _ h1 h0 h)
    exact ⟨j,lt,swapCost (fun p : Cell C R => g p.swap) (u,r) (s,r) hp hq rep⟩
  · rintro ⟨j,lt,rep⟩
    have large := eq.mpr ⟨j,lt,swapCost g _ _ hp hq rep⟩
    exact swapCost (fun p : Cell (C+1) R => colG p.swap) (u.castSucc,r) (s.castSucc,r) h1 h0 large

abbrev Cost {R C} (g : Sig (Cell R C)) (k : Nat) := RepSizeAtMost (fun r c => g (r,c)) k

private theorem renameOne {R M C} (f : Fin M ≃ Fin R) (g : Sig (Cell R C))
    (p q : Cell R C) (hp : g p = true) (hq : g q = false) {k} (h : Cost g k) :
    Cost (fun x : Cell M C => g (f x.1,x.2)) k := by
  let e : Cell M C → Cell R C := fun x => (f x.1,x.2)
  have sem : Can bin (pull e g) k pool := by
    apply mapCan (circuitMeans h) e
    intro a ha
    rcases basis ha with rfl|rfl|⟨i,rfl⟩|⟨c,rfl⟩
    · change zeroS ∈ pool; simp [pool]
    · change oneS ∈ pool; simp [pool]
    · have eq : pull e (rowS i) = rowS (f.symm i) := by
        funext x; simp [pull,e,rowS,Equiv.symm_apply_eq]
      rw [eq]; exact rowPool _
    · exact colPool c
  apply represented sem (f.symm p.1,p.2) (f.symm q.1,q.2)
  · simpa [e,pull] using hp
  · simpa [e,pull] using hq

private theorem renameRows {R M C} (f : Fin M ≃ Fin R) (g : Sig (Cell R C))
    (p q : Cell R C) (hp : g p = true) (hq : g q = false) (k) :
    Cost (fun x : Cell M C => g (f x.1,x.2)) k ↔ Cost g k := by
  refine ⟨?_,renameOne f g p q hp hq⟩
  intro h
  let d : Sig (Cell M C) := fun x => g (f x.1,x.2)
  have a : d (f.symm p.1,p.2) = true := by simpa [d] using hp
  have b : d (f.symm q.1,q.2) = false := by simpa [d] using hq
  simpa [d] using renameOne f.symm d _ _ a b h

-- Move one of two equal labels to the end, then delete it without losing a label.
private theorem peel {R M : Nat} (p : Fin (M+1) → Fin R) (sur : Function.Surjective p)
    (lt : R < M+1) : ∃ (e : Fin (M+1) ≃ Fin (M+1)) (q : Fin M → Fin R) (u : Fin M),
      Function.Surjective q ∧ ∀ x, p (e x) = q (copyIndex u x) := by
  obtain ⟨a,b,ne,same⟩ := Fintype.exists_ne_map_eq_of_card_lt p (by simpa using lt)
  let e := Equiv.swap (Fin.last M) a
  have ea : e (Fin.last M) = a := Equiv.swap_apply_left _ _
  have nb : e.symm b ≠ Fin.last M := by
    intro h
    have hb := congrArg e h
    rw [Equiv.apply_symm_apply,ea] at hb
    exact ne hb.symm
  obtain ⟨u,hu⟩ := Fin.exists_castSucc_eq.mpr nb
  have eb : e u.castSucc = b := by rw [hu,Equiv.apply_symm_apply]
  let q := fun x : Fin M => p (e x.castSucc)
  have eq : ∀ x, p (e x) = q (copyIndex u x) := by
    refine Fin.lastCases ?_ (fun i => ?_)
    · simpa [q,copyIndex,ea,eb] using same
    · simp [q,copyIndex]
  refine ⟨e,q,u,?_,eq⟩
  intro i
  obtain ⟨x,hx⟩ := sur i
  exact ⟨copyIndex u (e.symm x),by rw [← eq,Equiv.apply_symm_apply,hx]⟩

abbrev RowWitness {R C} (g : Sig (Cell R C)) :=
  ∀ u, ∃ s c, g (u,c) = true ∧ g (s,c) = false

private theorem peelBudget {i m k R : Nat} (h : i + (m+1) ≤ k+R) (lt : R < m+1) :
    k-1 < k ∧ i+m ≤ (k-1)+R := by omega

private theorem manyRows {R C} (g : Sig (Cell R C)) (u0 : Fin R) (witness : RowWitness g)
    (M : Nat) (p : Fin M → Fin R) (sur : Function.Surjective p) (k : Nat) :
    Cost (fun x : Cell M C => g (p x.1,x.2)) k ↔ ∃ j, Cost g j ∧ j + M ≤ k + R := by
  obtain ⟨s0,c0,yes0,no0⟩ := witness u0
  induction M generalizing k with
  | zero =>
    obtain ⟨x,_⟩ := sur u0
    exact Fin.elim0 x
  | succ m ih =>
    have card : R ≤ m+1 := by simpa using Fintype.card_le_of_surjective p sur
    by_cases eq : m+1 = R
    · let f : Fin (m+1) ≃ Fin R := Equiv.ofBijective p
        ((Fintype.bijective_iff_surjective_and_card p).2 ⟨sur,by simpa using eq⟩)
      rw [show Cost (fun x : Cell (m+1) C => g (p x.1,x.2)) k ↔ Cost g k from
        renameRows f g _ _ yes0 no0 k]
      constructor
      · exact fun h => ⟨k,h,by omega⟩
      · rintro ⟨j,⟨circ,ops,size,ev⟩,le⟩
        exact ⟨circ,ops,by omega,ev⟩
    · obtain ⟨e,q,u,qs,factor⟩ := peel p sur (by omega)
      let old : Sig (Cell m C) := fun x => g (q x.1,x.2)
      let big : Sig (Cell (m+1) C) := fun x => g (p x.1,x.2)
      obtain ⟨s,c,hp,hq⟩ := witness (q u)
      obtain ⟨t,ht⟩ := qs s
      have no : old (t,c) = false := by simpa [old,ht] using hq
      have row := rowCost old u t c hp no k
      obtain ⟨a,ha⟩ := sur u0
      obtain ⟨b,hb⟩ := sur s0
      have y : big (a,c0) = true := by simpa [big,ha] using yes0
      have n : big (b,c0) = false := by simpa [big,hb] using no0
      have perm := renameRows e big _ _ y n k
      have step : Cost big k ↔ ∃ j < k, Cost old j := by
        rw [← perm]
        simpa only [Cost,big,old,factor] using row
      rw [step]
      constructor
      · rintro ⟨j,lt,h⟩
        obtain ⟨i,base,le⟩ := (ih q qs j).mp h
        exact ⟨i,base,by omega⟩
      · rintro ⟨i,base,le⟩
        have bounds := peelBudget le (Nat.lt_of_le_of_ne card (Ne.symm eq))
        exact ⟨k-1,bounds.1,(ih q qs _).mpr ⟨i,base,bounds.2⟩⟩

theorem copies {R C M N} (g : Sig (Cell R C)) (u : Fin R) (c : Fin C)
    (rows : RowWitness g) (cols : RowWitness (fun x : Cell C R => g x.swap))
    (p : Fin M → Fin R) (q : Fin N → Fin C)
    (ps : Function.Surjective p) (qs : Function.Surjective q) (k : Nat) :
    Cost (fun x : Cell M N => g (p x.1,q x.2)) k ↔
      ∃ j, Cost g j ∧ j + (M-R) + (N-C) ≤ k := by
  have rle : R ≤ M := by simpa using Fintype.card_le_of_surjective p ps
  have cle : C ≤ N := by simpa using Fintype.card_le_of_surjective q qs
  let d : Sig (Cell R N) := fun x => g (x.1,q x.2)
  let t : Sig (Cell C R) := fun x => g x.swap
  have dw : RowWitness d := by
    intro a
    obtain ⟨b,v,h1,h0⟩ := rows a
    obtain ⟨j,hj⟩ := qs v
    exact ⟨b,j,by simpa [d,hj] using h1,by simpa [d,hj] using h0⟩
  have row := manyRows d u dw M p ps k
  have col := manyRows t c cols N q qs
  obtain ⟨s,v,h1,h0⟩ := rows u
  obtain ⟨z,hz⟩ := qs v
  have a : d (u,z) = true := by simpa [d,hz] using h1
  have b : d (s,z) = false := by simpa [d,hz] using h0
  have colEq (l : Nat) : Cost d l ↔ ∃ j, Cost g j ∧ j + N ≤ l+C := by
    constructor
    · intro h
      obtain ⟨j,bh,le⟩ := (col l).mp (swapCost d _ _ a b h)
      exact ⟨j,swapCost t (v,u) (v,s) h1 h0 bh,le⟩
    · rintro ⟨j,bh,le⟩
      have ch := (col l).mpr ⟨j,swapCost g _ _ h1 h0 bh,le⟩
      exact swapCost (fun x : Cell N R => d x.swap) (z,u) (z,s) a b ch
  rw [row]
  constructor
  · rintro ⟨l,dh,le⟩
    obtain ⟨j,bh,cl⟩ := (colEq l).mp dh
    exact ⟨j,bh,by omega⟩
  · rintro ⟨j,bh,le⟩
    exact ⟨j+(N-C),(colEq _).mpr ⟨j,bh,by omega⟩,by omega⟩

end
end PEqualNP.Outside.CircuitCopies_aux

/-- On one-row/one-column inputs, arbitrary nonempty groups of copies cost one
    additional binary AND/OR gate per new input when every input has a distinguishing pair. -/
theorem PEqualNP.Outside.CircuitCopies :
  ∀ (R C M N : Nat) (G : Fin R → Fin C → Bool),
    0 < R → 0 < C →
    (∀ r, ∃ s c, G r c = true ∧ G s c = false) →
    (∀ c, ∃ d r, G r c = true ∧ G r d = false) →
    ∀ (p : Fin M → Fin R) (q : Fin N → Fin C),
      Function.Surjective p → Function.Surjective q → ∀ k : Nat,
      PEqualNP.Represents.RepSizeAtMost (fun r c => G (p r) (q c)) k ↔
        ∃ j, PEqualNP.Represents.RepSizeAtMost G j ∧ j + (M-R) + (N-C) ≤ k := by
  intro R C M N G rpos cpos rows cols p q ps qs k
  exact PEqualNP.Outside.CircuitCopies_aux.copies (fun x => G x.1 x.2)
    ⟨0,rpos⟩ ⟨0,cpos⟩ rows cols p q ps qs k
