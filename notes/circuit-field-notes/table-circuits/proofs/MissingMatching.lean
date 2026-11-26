import PEqualNP.MetaComplexity.Helpers.RepReads
import PEqualNP.Outside.FormulaGap

namespace PEqualNP.Outside.MissingMatching_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.RepReads PEqualNP.Represents PEqualNP.Outside.FormulaGap_aux

-- Trace through a chosen NOT. Only its first operand matters, even when it lists two.
private theorem passesNot (g : Gate) (op : g.op = .not) (n : Nat) (S : Finset Nat) :
    ∃ T : Finset Nat, T.card ≤ S.card ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
        (∀ i ∈ T, x.getD i false = y.getD i false) →
        ∀ i ∈ S, (wiresFrom [g] x).getD i false = (wiresFrom [g] y).getD i false := by
  let parent := (g.inputs.take 1).toFinset
  let T := if n ∈ S then S.erase n ∪ parent else S
  refine ⟨T,?_,?_⟩
  · by_cases hn : n ∈ S
    · have a := Finset.card_union_le (S.erase n) parent
      have b := Finset.card_erase_of_mem hn
      have c : parent.card ≤ 1 := (List.toFinset_card_le _).trans (by simp)
      have := Finset.card_pos.mpr ⟨n,hn⟩
      simp only [T,hn,↓reduceIte]
      omega
    · simp [T,hn]
  · intro x y hx hy agree i hi
    change (x ++ [_]).getD i false = (y ++ [_]).getD i false
    rw [getD_snoc,getD_snoc,hx,hy]
    by_cases eq : i = n
    · subst i
      simp only [op,GateOp.eval]
      cases h : g.inputs with
      | nil => rfl
      | cons a rest =>
        have ha : a ∈ T := by simp [T,hi,parent,h]
        simpa using agree a ha
    · simp only [eq,↓reduceIte]
      apply agree i
      by_cases hn : n ∈ S <;> simp [T,hn,hi,eq]

private theorem supportOfNot {D : Circuit} (fan : FanInTwo D)
    (has : ∃ g ∈ D.gates, g.op = .not) (n : Nat) :
    ∃ S : Finset Nat, S.card ≤ D.size ∧ ∀ x y : List Bool, x.length = n → y.length = n →
      (∀ i ∈ S, x.getD i false = y.getD i false) → D.eval x = D.eval y := by
  obtain ⟨g,hg,op⟩ := has
  obtain ⟨pre,post,split⟩ := List.append_of_mem hg
  have ap : ∀ h ∈ pre, h.inputs.length ≤ 2 := fun h hh => (fan h (split ▸ List.mem_append_left _ hh)).2
  have az : ∀ h ∈ post, h.inputs.length ≤ 2 := fun h hh =>
    (fan h (split ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hh))).2
  obtain ⟨Z,cz,hz⟩ := needed (n+pre.length+1) post az {D.output}
  obtain ⟨T,ct,ht⟩ := passesNot g op (n+pre.length) Z
  obtain ⟨S,cs,hs⟩ := needed n pre ap T
  refine ⟨S,?_,?_⟩
  · simp only [Finset.card_singleton] at cz
    simp [Circuit.size,split]; omega
  · intro x y hx hy agree
    change (wiresFrom D.gates x).getD D.output false = (wiresFrom D.gates y).getD D.output false
    rw [split,show pre ++ g :: post = (pre ++ [g]) ++ post by simp]
    simp only [wiresFrom_append]
    apply hz _ _ (by simp [length_wiresFrom,hx]) (by simp [length_wiresFrom,hy]) _ _ (by simp)
    exact ht _ _ (by simp [length_wiresFrom,hx]) (by simp [length_wiresFrom,hy]) (hs x y hx hy agree)

def table {R C : Nat} (s : Nat) (u : Fin R) (v : Fin C) := !decide (u.val = v.val ∧ u.val < s)

-- Of s+1 representatives on either shore at most one can be unread.
private theorem distinguish {R C s : Nat} (hr : s < R) (hc : s < C)
    {D : Circuit} (rep : Represents (@table R C s) D) {S : Finset Nat}
    (support : ∀ x y : List Bool, x.length = R+C → y.length = R+C →
      (∀ i ∈ S, x.getD i false = y.getD i false) → D.eval x = D.eval y) : 2*s ≤ S.card := by
  have readSame (u x : Fin R) (v y : Fin C)
      (a : u=x ∨ (u.val ∉ S ∧ x.val ∉ S)) (b : v=y ∨ (R+v.val ∉ S ∧ R+y.val ∉ S)) :
      table s u v = table s x y := by
    rw [← rep u v,← rep x y]
    apply support _ _ (by simp [oneEach]) (by simp [oneEach])
    intro i hi
    simp only [oneEach_eq,inp_getD,Finset.mem_insert,Finset.mem_singleton,decide_eq_decide]
    rcases a with rfl|⟨a1,a2⟩ <;> rcases b with rfl|⟨b1,b2⟩ <;> grind
  let rows := Finset.range (s+1)
  let cols := Finset.Ico R (R+s+1)
  have mr : (rows \ S).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    simp only [rows,Finset.mem_sdiff,Finset.mem_range] at ha hb
    by_contra ne
    wlog lt : a < b generalizing a b
    · exact this b a hb ha (Ne.symm ne) (by omega)
    have same := readSame ⟨a,by omega⟩ ⟨b,by omega⟩ ⟨a,by omega⟩ ⟨a,by omega⟩
      (.inr ⟨ha.2,hb.2⟩) (.inl rfl)
    simp [table,show a < s by omega,Ne.symm ne] at same
  have mc : (cols \ S).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    simp only [cols,Finset.mem_sdiff,Finset.mem_Ico] at ha hb
    by_contra ne
    wlog lt : a < b generalizing a b
    · exact this b a hb ha (Ne.symm ne) (by omega)
    let i : Fin R := ⟨a-R,by omega⟩
    let j : Fin C := ⟨a-R,by omega⟩
    let l : Fin C := ⟨b-R,by omega⟩
    have ij : R+j.val = a := by dsimp [j]; omega
    have il : R+l.val = b := by dsimp [l]; omega
    have same := readSame i i j l (.inl rfl) (.inr ⟨ij ▸ ha.2,il ▸ hb.2⟩)
    simp [table,i,j,l,show a-R < s by omega,show a-R ≠ b-R by omega] at same
  have cr := Finset.card_sdiff_add_card_inter rows S
  have cc := Finset.card_sdiff_add_card_inter cols S
  have dis : Disjoint (rows ∩ S) (cols ∩ S) := by
    apply Finset.disjoint_left.mpr
    intro i h j
    have a := (Finset.mem_inter.mp h).1
    have b := (Finset.mem_inter.mp j).1
    simp [rows,cols] at a b
    omega
  have sub : (rows ∩ S) ∪ (cols ∩ S) ⊆ S := Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
  have bound := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint dis] at bound
  have a : rows.card = s+1 := Finset.card_range _
  have b : cols.card = s+1 := by simp [cols]; omega
  omega

private theorem hasLower {R C s k : Nat} (hs : 2 ≤ s) (hr : s < R) (hc : s < C)
    {D : Circuit} (fan : FanInTwo D) (size : D.size ≤ k) (rep : Represents (@table R C s) D) : 2*s ≤ k := by
  by_cases has : ∃ g ∈ D.gates, g.op = .not
  · obtain ⟨S,le,support⟩ := supportOfNot fan has (R+C)
    exact (distinguish hr hc rep support).trans (le.trans size)
  · have mono : Monotone2 D := by
      intro g hg
      obtain ⟨op,arity⟩ := fan g hg
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op ⊢
      refine ⟨?_,arity⟩
      rcases op with h|h|h
      · exact .inl h
      · exact .inr h
      · exact False.elim (has ⟨g,hg,h⟩)
    have leftFull : forcedL (@table R C s) = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro i
      simp only [forcedL,Finset.mem_filter,Finset.mem_univ,true_and]
      let a := if i.val = 0 then 1 else 0
      have lt : a < s := by dsimp [a]; split <;> omega
      have ne : i.val ≠ a := by dsimp [a]; split <;> omega
      exact ⟨⟨a,by omega⟩,by simp [table,ne],⟨a,by omega⟩,by simp [table,lt]⟩
    have rightFull : forcedR (@table R C s) = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro i
      simp only [forcedR,Finset.mem_filter,Finset.mem_univ,true_and]
      let a := if i.val = 0 then 1 else 0
      have lt : a < s := by dsimp [a]; split <;> omega
      have ne : a ≠ i.val := by dsimp [a]; split <;> omega
      exact ⟨⟨a,by omega⟩,by simp [table,ne],⟨a,by omega⟩,by simp [table,lt]⟩
    have le := reads_le (@table R C s) ⟨D,mono,size,rep⟩
    simp [leftFull,rightFull] at le
    omega

private def matching {R C} (s : Nat) (p : Cell R C) := decide (p.1.val = p.2.val ∧ p.1.val < s)

-- One AND per forbidden pair, then one fewer OR than there are pairs.
private theorem buildPairs {R C} (j : Nat) (hr : j < R) (hc : j < C) :
    ∃ w, Extend (inputs R C) (2*j+1) w ∧ @matching R C (j+1) ∈ w := by
  induction j with
  | zero =>
    let r : Fin R := ⟨0,hr⟩
    let c : Fin C := ⟨0,hc⟩
    let a : Sig (Cell R C) := fun p => decide (r=p.1)
    let b : Sig (Cell R C) := fun p => decide (c=p.2)
    have ext : Extend (inputs R C) 1 (inputs R C ++ [bin true a b]) :=
      .gate .start true (rawRow _) (rawCol _)
    have eq : bin true a b = matching 1 := by
      funext p
      apply Bool.eq_iff_iff.mpr
      simp [bin,a,b,r,c,matching,Fin.ext_iff]; omega
    exact ⟨_,ext,eq ▸ List.mem_append_right _ (List.mem_singleton_self _)⟩
  | succ j ih =>
    obtain ⟨w,ext,old⟩ := ih (by omega) (by omega)
    let r : Fin R := ⟨j+1,hr⟩
    let c : Fin C := ⟨j+1,hc⟩
    let a : Sig (Cell R C) := fun p => decide (r=p.1)
    let b : Sig (Cell R C) := fun p => decide (c=p.2)
    have step := Extend.gate ext true (a:=a) (b:=b) (kept ext _ (rawRow _)) (kept ext _ (rawCol _))
    have add := Extend.gate step false (a:=matching (j+1)) (b:=bin true a b)
      (List.mem_append_left _ old) (List.mem_append_right _ (List.mem_singleton_self _))
    have eq : bin false (matching (j+1)) (bin true a b) = matching (j+2) := by
      funext p
      apply Bool.eq_iff_iff.mpr
      simp [bin,a,b,r,c,matching,Fin.ext_iff]; omega
    refine ⟨_,by convert add using 1,?_⟩
    rw [← eq]; simp

-- Appending NOT to any circuit costs exactly one gate in this construction.
private theorem negate {R C} {g : Fin R → Fin C → Bool} {D : Circuit}
    (fan : FanInTwo D) (rep : Represents g D) :
    ∃ B : Circuit, FanInTwo B ∧ B.size = D.size+1 ∧ Represents (fun r c => !g r c) B := by
  let neg : Gate := ⟨.not,[D.output]⟩
  let B : Circuit := ⟨D.gates++[neg],R+C+D.gates.length⟩
  refine ⟨B,?_,by simp [B,Circuit.size],?_⟩
  · intro t ht
    rcases List.mem_append.mp ht with old|last
    · exact fan t old
    · obtain rfl := List.mem_singleton.mp last
      simp [neg]
  · intro u v
    let x := oneEach u v
    have lx : x.length = R+C := by simp [x,oneEach]
    have eq := rep u v
    change (wiresFrom D.gates x).getD D.output false = g u v at eq
    change (wiresFrom (D.gates++[neg]) x).getD (R+C+D.gates.length) false = _
    rw [wiresFrom_snoc,getD_snoc,length_wiresFrom,lx]
    simp only [↓reduceIte]
    simpa [neg,GateOp.eval,-List.getD_eq_getElem?_getD] using congrArg Bool.not eq

private theorem upper {R C s} (hs : 2 ≤ s) (hr : s < R) (hc : s < C) :
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ 2*s ∧ Represents (@table R C s) D := by
  cases s with
  | zero => omega
  | succ j =>
    obtain ⟨w,ext,out⟩ := buildPairs j (by omega : j < R) (by omega : j < C)
    obtain ⟨D,ops,size,rep⟩ := circuitFrom (matching (j+1)) ext out
    have fan : FanInTwo D := by
      intro g hg
      obtain ⟨op,arity⟩ := ops g hg
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op
      rcases op with h|h <;> simp [h,arity]
    obtain ⟨B,fb,sz,rb⟩ := negate fan rep
    exact ⟨B,fb,by omega,rb⟩

theorem exactCost {R C s} (hs : 2 ≤ s) (hr : s < R) (hc : s < C) (k : Nat) :
    (∃ D : Circuit, FanInTwo D ∧ D.size ≤ k ∧ Represents (@table R C s) D) ↔ 2*s ≤ k := by
  constructor
  · rintro ⟨D,fan,size,rep⟩
    exact hasLower hs hr hc fan size rep
  · intro le
    obtain ⟨D,fan,size,rep⟩ := upper hs hr hc
    exact ⟨D,fan,size.trans le,rep⟩

theorem matchingCost {R C s} (hs : 2 ≤ s) (hr : s < R) (hc : s < C) (k : Nat) :
    RepSizeAtMost (fun (r : Fin R) (c : Fin C) => matching s (r,c)) k ↔ 2*s-1 ≤ k := by
  constructor
  · rintro ⟨D,ops,size,rep⟩
    have fan : FanInTwo D := by
      intro g hg
      obtain ⟨op,arity⟩ := ops g hg
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op
      rcases op with h|h <;> simp [h,arity]
    obtain ⟨B,fb,sz,rb⟩ := negate fan rep
    have le := hasLower (R:=R) (C:=C) (k:=D.size+1) hs hr hc fb sz.le rb
    omega
  · intro le
    cases s with
    | zero => omega
    | succ j =>
      obtain ⟨w,ext,out⟩ := buildPairs j (by omega : j<R) (by omega : j<C)
      obtain ⟨D,op,sz,rep⟩ := circuitFrom (matching (j+1)) ext out
      exact ⟨D,op,by omega,rep⟩

end PEqualNP.Outside.MissingMatching_aux

/-- Exact AND/OR/NOT cost of the complement and exact AND/OR cost of the matching. -/
theorem PEqualNP.Outside.MissingMatching :
  ∀ (R C s : Nat), 2 ≤ s → s < R → s < C → ∀ k : Nat,
    ((∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size ≤ k ∧
      PEqualNP.Represents.Represents
        (fun (u : Fin R) (v : Fin C) => !decide (u.val = v.val ∧ u.val < s)) D) ↔ 2*s ≤ k) ∧
    (PEqualNP.Represents.RepSizeAtMost
      (fun (u : Fin R) (v : Fin C) => decide (u.val = v.val ∧ u.val < s)) k ↔ 2*s-1 ≤ k) := by
  intro R C s hs hr hc k
  exact ⟨PEqualNP.Outside.MissingMatching_aux.exactCost hs hr hc k,
    PEqualNP.Outside.MissingMatching_aux.matchingCost hs hr hc k⟩
