import PEqualNP.Outside.FormulaGap
import PEqualNP.Outside.TwinReduction

namespace PEqualNP.Outside.TwinCorner_aux
open PEqualNP.MetaComplexity
open TwinReduction_aux
abbrev G := PEqualNP.Outside.FormulaGap_aux.square 1
abbrev enc := @PEqualNP.Outside.FormulaGap_aux.bits 3 3
abbrev F6 := DMFormula 6

def lit (i : Fin 6) : F6 := .lit i true
def useCol : F6 := .or (.or (.and (lit 0) (.or (lit 3) (lit 4))) (.and (lit 1) (lit 3))) (.and (lit 2) (lit 5))
def useRow : F6 := .or (.or (.and (.or (lit 0) (lit 1)) (lit 3)) (.and (lit 0) (lit 4))) (.and (lit 2) (lit 5))

theorem colData : pos useCol ∧ (∀ a, useCol.eval (enc a) = G a) ∧
    ∀ i, reads useCol i = 1 + (if i = 3 then 1 else 0) := by
  refine ⟨?_, by decide, by decide⟩
  simp [pos,useCol,lit]
theorem rowData : pos useRow ∧ (∀ a, useRow.eval (enc a) = G a) ∧
    ∀ i, reads useRow i = 1 + (if i = 0 then 1 else 0) := by
  refine ⟨?_, by decide, by decide⟩
  simp [pos,useRow,lit]

theorem sameReads {n : Nat} (f : DMFormula n) (i : Fin n) :
    reads f i = FormulaGap_aux.reads f i := by
  induction f with
  | lit => rfl
  | and l r hl hr | or l r hl hr => exact congrArg₂ Nat.add hl hr

theorem need (f : F6) (hf : pos f) (ok : ∀ a, f.eval (enc a) = G a) :
    (∀ i, 1 ≤ reads f i) ∧ (2 ≤ reads f 0 ∨ 2 ≤ reads f 3) := by
  have baseOk : FormulaGap_aux.Matches FormulaGap_aux.bits G f := fun a => ok a
  have basePos : FormulaGap_aux.positive f := by
    clear baseOk ok
    induction f with
    | lit => exact hf
    | and _ _ hl hr | or _ _ hl hr => exact ⟨hl hf.1, hr hf.2⟩
  have mix : FormulaGap_aux.MixedTable G := FormulaGap_aux.squareMixed (k:=1) (by decide)
  have corner := FormulaGap_aux.repeatCorner mix (f:=f) basePos baseOk (r:=0) (s:=1) (c:=0) (d:=1)
    (by decide) (by decide) (by decide) (by decide)
  simp only [sameReads]
  exact ⟨FormulaGap_aux.everyWire mix basePos baseOk,corner⟩

variable {m : Nat} (p : Fin m → Fin 6)
def count (i : Fin 6) := (Finset.univ.filter (fun j => p j = i)).card
theorem bill (i : Fin 6) : (∑ j, (1 + if p j = i then 1 else 0 : Nat)) = m + count p i := by
  simp [count,Finset.sum_add_distrib,Finset.sum_boole]

theorem baseBudget (k : Nat) :
    (∃ f : F6, pos f ∧ (∀ a, f.eval (enc a) = G a) ∧ (∑ j, reads f (p j)) ≤ k) ↔
        m + min (count p 0) (count p 3) ≤ k := by
  constructor
  · rintro ⟨f,hf,ok,limit⟩
    obtain ⟨all,twice⟩ := need f hf ok
    have charge (i : Fin 6) (hi : 2 ≤ reads f i) : m + count p i ≤ k := by
      rw [← bill]
      apply le_trans (Finset.sum_le_sum ?_) limit
      intro j _
      by_cases e : p j = i
      · simpa [e] using hi
      · simpa [e] using all (p j)
    rcases twice with h | h
    · exact (Nat.add_le_add_left (min_le_left _ _) _).trans (charge 0 h)
    · exact (Nat.add_le_add_left (min_le_right _ _) _).trans (charge 3 h)
  · intro cap
    rcases le_total (count p 0) (count p 3) with h|h
    · refine ⟨useRow,rowData.1,rowData.2.1,?_⟩
      simpa only [rowData.2.2,bill,min_eq_left h] using cap
    · refine ⟨useCol,colData.1,colData.2.1,?_⟩
      simpa only [colData.2.2,bill,min_eq_right h] using cap

def FitsCorner (g : DMFormula m) := ∀ s, (∀ i, p (s i) = i) →
    ∀ a, g.eval (liftInput p s (enc a)) = G a

theorem cornerBudget (onto : Function.Surjective p) (k : Nat) :
    (∃ g : DMFormula m, pos g ∧ FitsCorner p g ∧ g.leaves ≤ k) ↔
        m + min (count p 0) (count p 3) ≤ k := by
  let X := fun x : Fin 6 → Bool => ∃ a, enc a = x
  let H := useCol.eval
  have live : ∃ x, X x ∧ H x = true := ⟨enc (0,0),⟨(0,0),rfl⟩,by decide⟩
  have base (f : F6) : Fits X H f ↔ ∀ a, f.eval (enc a) = G a := by
    constructor
    · intro h a; exact (h _ ⟨a,rfl⟩).trans (colData.2.1 a)
    · intro h x hx; obtain ⟨a,rfl⟩ := hx; exact (h a).trans (colData.2.1 a).symm
  have copies (g : DMFormula m) : FitsCopies p X H g ↔ FitsCorner p g := by
    constructor
    · intro h s hs a; exact (h s hs _ ⟨a,rfl⟩).trans (colData.2.1 a)
    · intro h s hs x hx; obtain ⟨a,rfl⟩ := hx; exact (h s hs a).trans (colData.2.1 a).symm
  have equiv := exactBudget p onto live k
  simp only [base,copies] at equiv
  exact equiv.symm.trans (baseBudget p k)

end PEqualNP.Outside.TwinCorner_aux

namespace PEqualNP.Outside.TwinCircuit_aux
open FormulaGap_aux PEqualNP.Represents PEqualNP.MetaComplexity

def classCard {d} (p : Fin d → Fin 3) (i : Fin 3) := (Finset.univ.filter (fun j => p j = i)).card

theorem classSum {d} (p : Fin d → Fin 3) :
    classCard p 0 + classCard p 1 + classCard p 2 = d := by
  have part := Finset.sum_fiberwise (Finset.univ : Finset (Fin d)) p (fun _ => (1 : Nat))
  simpa [Fin.sum_univ_three,classCard,Nat.add_assoc] using part

theorem combine {X Y : Type} (signal : X → Y → Bool) (w : List (Sig Y)) (j : X) (js : List X)
    (avail : ∀ i ∈ j :: js, signal i ∈ w) :
    ∃ v s, Extend w js.length v ∧ s ∈ v ∧ ∀ y, s y = true ↔ ∃ i ∈ j :: js, signal i y = true := by
  induction js with
  | nil => exact ⟨w,signal j,.start,avail _ (by simp),by simp⟩
  | cons k ks ih =>
    obtain ⟨v,s,ex,hs,ok⟩ := ih (fun i hi => avail i (by simp_all [List.mem_cons]; tauto))
    have hk := kept ex _ (avail k (by simp))
    refine ⟨_,bin false (signal k) s,.gate ex false hk hs, List.mem_append_right _ (by simp),?_⟩
    intro y; simp [bin,ok,or_left_comm]

theorem poolClass {d} {Y : Type} (p : Fin d → Fin 3) (onto : Function.Surjective p)
    (get : Y → Fin d) (i : Fin 3) (w : List (Sig Y))
    (avail : ∀ j : Fin d, (fun y : Y => decide (j = get y)) ∈ w) :
    ∃ t v, Extend w t v ∧ t+1 = classCard p i ∧ (fun y => decide (p (get y) = i)) ∈ v := by
  let list := (Finset.univ.filter (fun j => p j = i)).toList
  have mem (j) : j ∈ list ↔ p j = i := by simp [list]
  have len : list.length = classCard p i := by simp [list,classCard]
  obtain ⟨j0,h0⟩ := onto i
  cases eq : list with
  | nil => simpa [eq] using (mem _).mpr h0
  | cons j js =>
    obtain ⟨v,s,ex,hs,ok⟩ := combine (fun k y => decide (k = get y)) w j js (fun k _ => avail k)
    refine ⟨js.length,v,ex,by simpa [eq] using len,?_⟩
    have same : s = (fun y => decide (p (get y) = i)) := by
      funext y
      apply Bool.eq_iff_iff.mpr
      rw [ok,← eq]
      simp [mem]
    rwa [← same]

variable {R C : Nat} (pr : Fin R → Fin 3) (pc : Fin C → Fin 3)
abbrev graph (r : Fin R) (c : Fin C) := TwinCorner_aux.G (pr r,pc c)
def row (i : Fin 3) : Sig (Cell R C) := fun a => decide (pr a.1 = i)
def col (i : Fin 3) : Sig (Cell R C) := fun a => decide (pc a.2 = i)

theorem upper (hr : Function.Surjective pr) (hc : Function.Surjective pc) :
    RepSizeAtMost (graph pr pc) (R+C) := by
  let w := inputs R C
  have rstep (i : Fin 3) {n v} (e : Extend w n v) :
      ∃ t v', Extend v t v' ∧ t+1 = classCard pr i ∧ row (C:=C) pr i ∈ v' :=
    poolClass pr hr Prod.fst i v (fun j => kept e _ (rawRow j))
  have cstep (i : Fin 3) {n v} (e : Extend w n v) :
      ∃ t v', Extend v t v' ∧ t+1 = classCard pc i ∧ col (R:=R) pc i ∈ v' :=
    poolClass pc hc Prod.snd i v (fun j => kept e _ (rawCol j))
  obtain ⟨t0,v0,e0,n0,a0⟩ := rstep 0 Extend.start
  obtain ⟨t1,v1,e1,n1,a1⟩ := rstep 1 e0
  obtain ⟨t2,v2,e2,n2,a2⟩ := rstep 2 (compose e0 e1)
  obtain ⟨t3,v3,e3,n3,a3⟩ := cstep 0 (compose (compose e0 e1) e2)
  obtain ⟨t4,v4,e4,n4,a4⟩ := cstep 1 (compose (compose (compose e0 e1) e2) e3)
  obtain ⟨t5,v5,e5,n5,a5⟩ := cstep 2 (compose (compose (compose (compose e0 e1) e2) e3) e4)
  have h0 := kept (compose (compose (compose (compose e1 e2) e3) e4) e5) _ a0
  have h1 := kept (compose (compose (compose e2 e3) e4) e5) _ a1
  have h2 := kept (compose (compose e3 e4) e5) _ a2
  have h3 := kept (compose e4 e5) _ a3
  have h4 := kept e5 _ a4
  have base := compose (compose (compose (compose (compose e0 e1) e2) e3) e4) e5
  let wide := bin false (col (R:=R) pc 0) (col pc 1)
  let top := bin true (row pr 0) wide
  let mid := bin true (row pr 1) (col pc 0)
  let block := bin false top mid
  let island := bin true (row pr 2) (col pc 2)
  have g1 : Extend w _ (v5++[wide]) := .gate base false h3 h4
  have g2 : Extend w _ ((v5++[wide])++[top]) := .gate g1 true (by simp [h0]) (by simp)
  have g3 : Extend w _ (((v5++[wide])++[top])++[mid]) := .gate g2 true (by simp [h1]) (by simp [h3])
  have g4 : Extend w _ ((((v5++[wide])++[top])++[mid])++[block]) := .gate g3 false (by simp) (by simp)
  have g5 : Extend w _ (((((v5++[wide])++[top])++[mid])++[block])++[island]) :=
    .gate g4 true (by simp [h2]) (by simp [a5])
  have g6 := Extend.gate g5 false (a:=block) (b:=island) (by simp) (by simp)
  have out : (fun a => graph pr pc a.1 a.2) = bin false block island := by
    funext a
    change TwinCorner_aux.G (pr a.1,pc a.2) = _
    simp only [block,top,mid,wide,island,bin,row,col,ite_true]
    generalize pr a.1 = u; generalize pc a.2 = v
    fin_cases u <;> fin_cases v <;> decide
  have sumR := classSum pr
  have sumC := classSum pc
  have len : t0+t1+t2+t3+t4+t5+1+1+1+1+1+1 = R+C := by omega
  rw [← len]
  exact circuitFrom (fun a => graph pr pc a.1 a.2) g6 (by rw [out]; exact List.mem_append_right _ (by simp))

theorem lower (hr : Function.Surjective pr) (hc : Function.Surjective pc) (k : Nat) (hk : k < R+C) :
    ¬ RepSizeAtMost (graph pr pc) k := by
  let g := fun a : Cell R C => graph pr pc a.1 a.2
  have seed := squareMixed (k:=1) (by decide)
  have transport {A B : Type} (f : A → B) (sur : Function.Surjective f) (P : B → Prop) :
      (∃ b, P b) → ∃ a, P (f a) := by rintro ⟨b,hb⟩; obtain ⟨a,rfl⟩ := sur b; exact ⟨a,hb⟩
  have mix : MixedTable g :=
    ⟨fun r => ⟨transport pc hc _ (seed.1 (pr r)).1, transport pc hc _ (seed.1 (pr r)).2⟩,
     fun c => ⟨transport pr hr _ (seed.2 (pc c)).1, transport pr hr _ (seed.2 (pc c)).2⟩⟩
  obtain ⟨r0,hr0⟩ := hr 0; obtain ⟨r1,hr1⟩ := hr 1
  obtain ⟨c0,hc0⟩ := hc 0; obtain ⟨c1,hc1⟩ := hc 1
  apply noSmallCircuit (g:=g) mix _ hk
  intro f hp ok
  have h := matchingBound (k:=1) mix hp ok (fun _ => r0) (fun _ => r1) (fun _ => c0) (fun _ => c1)
    (fun _ _ _ => Subsingleton.elim _ _) (fun _ _ _ => Subsingleton.elim _ _) (by
      intro i; simp only [Corner,g,graph,hr0,hc0,hr1,hc1]; decide)
  omega

end PEqualNP.Outside.TwinCircuit_aux

namespace PEqualNP.Outside.TwinCircuit_aux
open FormulaGap_aux PEqualNP.MetaComplexity TwinReduction_aux

variable {R C : Nat} (pr : Fin R → Fin 3) (pc : Fin C → Fin 3)
def wires : Fin (R+C) → Fin 6 :=
  Fin.addCases (fun r => Fin.castAdd 3 (pr r)) (fun c => Fin.natAdd 3 (pc c))

theorem wireR (r : Fin R) : wires pr pc (Fin.castAdd C r) = Fin.castAdd 3 (pr r) := Fin.addCases_left _
theorem wireC (c : Fin C) : wires pr pc (Fin.natAdd R c) = Fin.natAdd 3 (pc c) := Fin.addCases_right _

theorem apart {a b} (i : Fin a) (j : Fin b) : Fin.castAdd b i ≠ Fin.natAdd a j := by
  intro h; have eq := congrArg Fin.val h; simp at eq; omega

theorem wiresOnto (hr : Function.Surjective pr) (hc : Function.Surjective pc) : Function.Surjective (wires pr pc) := by
  intro i
  refine Fin.addCases (m:=3) (n:=3) (fun r => ?_) (fun c => ?_) i
  · obtain ⟨r',e⟩ := hr r; exact ⟨Fin.castAdd C r',by rw [wireR,e]⟩
  · obtain ⟨c',e⟩ := hc c; exact ⟨Fin.natAdd R c',by rw [wireC,e]⟩

theorem rowPreimage (j : Fin (R+C)) (u : Fin 3) :
    wires pr pc j = Fin.castAdd 3 u → ∃ r, j = Fin.castAdd C r ∧ pr r = u := by
  refine Fin.addCases (fun r => ?_) (fun c => ?_) j
  · intro h; exact ⟨r,rfl,Fin.castAdd_injective _ _ ((wireR pr pc r).symm.trans h)⟩
  · intro h; exact False.elim (apart u (pc c) (h.symm.trans (wireC pr pc c)))

theorem colPreimage (j : Fin (R+C)) (v : Fin 3) :
    wires pr pc j = Fin.natAdd 3 v → ∃ c, j = Fin.natAdd R c ∧ pc c = v := by
  refine Fin.addCases (fun r => ?_) (fun c => ?_) j
  · intro h; exact False.elim (apart (pr r) v ((wireR pr pc r).symm.trans h))
  · intro h; exact ⟨c,rfl,Fin.natAdd_injective _ _ ((wireC pr pc c).symm.trans h)⟩

theorem bits_pair {r : Fin R} {c : Fin C} (j : Fin (R+C)) :
    bits (r,c) j = true ↔ j = Fin.castAdd C r ∨ j = Fin.natAdd R c := by
  refine Fin.addCases (fun r' => ?_) (fun c' => ?_) j
  · simp [bits,apart]
  · simp [bits,Ne.symm (apart r c')]

-- Every choice of representatives activates precisely one row and one column.
theorem lift_pair {s : Fin 6 → Fin (R+C)} (hs : ∀ i, wires pr pc (s i) = i)
    (a : Cell 3 3) (j : Fin (R+C)) :
    liftInput (wires pr pc) s (bits a) j = true ↔
        j = s (Fin.castAdd 3 a.1) ∨ j = s (Fin.natAdd 3 a.2) := by
  cases a with
  | mk u v =>
    constructor
    · intro hit
      by_cases kept : s (wires pr pc j) = j
      · have e := (bits_pair _).mp (by simpa [liftInput,kept] using hit : bits (u,v) (wires pr pc j) = true)
        rcases e with h|h
        · exact Or.inl (kept.symm.trans (congrArg s h))
        · exact Or.inr (kept.symm.trans (congrArg s h))
      · simp [liftInput,kept] at hit
    · rintro (rfl|rfl) <;> simp only [liftInput,hs,ite_true] <;> apply (bits_pair _).mpr
      · exact Or.inl rfl
      · exact Or.inr rfl

theorem fits_equiv (hr : Function.Surjective pr) (hc : Function.Surjective pc) (f : DMFormula (R+C)) :
    TwinCorner_aux.FitsCorner (wires pr pc) f ↔ ∀ r c, f.eval (bits (r,c)) = graph pr pc r c := by
  constructor
  · intro ok r c
    let u := Fin.castAdd 3 (pr r)
    let v := Fin.natAdd 3 (pc c)
    have uv : u ≠ v := apart _ _
    let base := (wiresOnto pr pc hr hc).hasRightInverse.choose
    have hb : Function.RightInverse base (wires pr pc) := (wiresOnto pr pc hr hc).hasRightInverse.choose_spec
    let s := fun i => if i = u then Fin.castAdd C r else if i = v then Fin.natAdd R c else base i
    have hs (i) : wires pr pc (s i) = i := by
      by_cases hu : i = u
      · subst i; simp [s,u,wireR]
      · by_cases hv : i = v
        · subst i; change wires pr pc (if v = u then _ else if v = v then _ else _) = v
          simp only [hu,ite_false,ite_true,eq_self]; exact wireC pr pc c
        · simp [s,hu,hv,hb i]
    have eq : liftInput (wires pr pc) s (bits (pr r,pc c)) = bits (r,c) := by
      funext j; apply Bool.eq_iff_iff.mpr
      rw [lift_pair _ _ hs,bits_pair]
      change (j = s u ∨ j = s v) ↔ _
      simp [s,uv.symm]
    simpa only [eq] using ok s hs (pr r,pc c)
  · intro ok s hs a
    obtain ⟨r,er,prr⟩ := rowPreimage pr pc _ a.1 (hs _)
    obtain ⟨c,ec,pcc⟩ := colPreimage pr pc _ a.2 (hs _)
    have eq : liftInput (wires pr pc) s (bits a) = bits (r,c) := by
      funext j; apply Bool.eq_iff_iff.mpr; rw [lift_pair _ _ hs,bits_pair,er,ec]
    simpa only [eq,graph,prr,pcc] using (ok r c : f.eval (bits (r,c)) = TwinCorner_aux.G (pr r,pc c))

theorem countsR : TwinCorner_aux.count (wires pr pc) 0 = classCard pr 0 := by
  change TwinCorner_aux.count (wires pr pc) (Fin.castAdd 3 0) = _
  simp only [TwinCorner_aux.count, classCard, Finset.card_filter]
  rw [Fin.sum_univ_add (a:=R) (b:=C)]
  simp only [wireR,wireC]
  calc
    _ = (∑ j, if pr j = 0 then 1 else 0) + (∑ _ : Fin C, 0) := by
      apply congrArg₂ Nat.add <;> apply Finset.sum_congr rfl
      · intro i _; generalize pr i = u; fin_cases u <;> decide
      · intro i _; generalize pc i = u; fin_cases u <;> decide
    _ = _ := by simp

theorem countsC : TwinCorner_aux.count (wires pr pc) 3 = classCard pc 0 := by
  change TwinCorner_aux.count (wires pr pc) (Fin.natAdd 3 (0 : Fin 3)) = _
  simp only [TwinCorner_aux.count, classCard, Finset.card_filter]
  rw [Fin.sum_univ_add (a:=R) (b:=C)]
  simp only [wireR,wireC]
  calc
    _ = (∑ _ : Fin R, 0) + (∑ j, if pc j = 0 then 1 else 0) := by
      apply congrArg₂ Nat.add <;> apply Finset.sum_congr rfl
      · intro i _; generalize pr i = u; fin_cases u <;> decide
      · intro i _; generalize pc i = u; fin_cases u <;> decide
    _ = _ := by simp

theorem formula (hr : Function.Surjective pr) (hc : Function.Surjective pc) (k : Nat) :
    (∃ f : DMFormula (R+C), pos f ∧ (∀ r c, f.eval (bits (r,c)) = graph pr pc r c) ∧ f.leaves ≤ k) ↔
      R+C+min (classCard pr 0) (classCard pc 0) ≤ k := by
  simpa only [fits_equiv pr pc hr hc,countsR,countsC] using
    TwinCorner_aux.cornerBudget (wires pr pc) (wiresOnto pr pc hr hc) k
end PEqualNP.Outside.TwinCircuit_aux

theorem PEqualNP.Outside.TwinTable :
  let Pos := fun {d : Nat} (f : PEqualNP.MetaComplexity.DMFormula d) =>
    PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => Prop) (fun _ b => b = true)
      (fun _ _ l r => l ∧ r) (fun _ _ l r => l ∧ r) f
  ∀ (R C : Nat) (pr : Fin R → Fin 3) (pc : Fin C → Fin 3),
    Function.Surjective pr → Function.Surjective pc →
    let G := fun (r : Fin R) (c : Fin C) =>
      decide (((pr r).val ≤ 1 ∧ (pc c).val ≤ 1 ∧ ((pr r).val < 1 ∨ (pc c).val < 1)) ∨
              ((pr r).val = 2 ∧ (pc c).val = 2))
    PEqualNP.Represents.RepSizeAtMost G (R+C) ∧
    (∀ k : Nat, k < R+C → ¬ PEqualNP.Represents.RepSizeAtMost G k) ∧
    ∀ k : Nat,
      (∃ f : PEqualNP.MetaComplexity.DMFormula (R+C), Pos f ∧
        (∀ r c, f.eval (Fin.addCases (fun i => decide (i = r)) (fun j => decide (j = c))) = G r c) ∧
        f.leaves ≤ k) ↔
      R+C+min (Finset.univ.filter (fun r => pr r = 0)).card (Finset.univ.filter (fun c => pc c = 0)).card ≤ k := by
  dsimp only
  intro R C pr pc hr hc
  exact ⟨TwinCircuit_aux.upper pr pc hr hc, TwinCircuit_aux.lower pr pc hr hc,
    TwinCircuit_aux.formula pr pc hr hc⟩
