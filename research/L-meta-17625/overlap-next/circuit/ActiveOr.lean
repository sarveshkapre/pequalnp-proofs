import SwitchCore
import Mathlib.Combinatorics.SimpleGraph.Bipartite

namespace ActiveOr
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing

attribute [local instance] gateOpDecEq

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- A path from a top descends through ordinary ORs, stopping at its first exception. -/
def ordinaryStep (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (w v : ℕ) :=
  OrStep n C w v ∧ ∃ k ∈ lam G C, w = n+k

private theorem plainPath {w v : ℕ} (p : Relation.ReflTransGen (ordinaryStep G C) w v) :
    Relation.ReflTransGen (OrStep n C) w v := by
  induction p with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail step.1

/-- Exceptional ORs first reached from a top operand. Both their raw inputs
and the route through ordinary ORs are properties of the wiring alone. -/
noncomputable def atTops (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) : Finset ℕ := by
  classical
  exact (orN G C \ lam G C).filter fun h => (orIn n C (n+h)).Nonempty ∧
    ∃ a ∈ tops G C, ∃ b : Fin 2, Relation.ReflTransGen (ordinaryStep G C) (opnd C a b) (n+h)

private theorem firstSource (ao : IsAO2 n C) (x : Fin n → Bool) (w : ℕ)
    (bound : w < n+C.gates.length) (raw : (orIn n C w).Nonempty)
    (fires : val C (List.ofFn x) w = true) :
    (∃ t ∈ orIn n C w, x t = true) ∨
      ∃ h ∈ orN G C \ lam G C, (orIn n C (n+h)).Nonempty ∧
        Relation.ReflTransGen (ordinaryStep G C) w (n+h) ∧ gateVal n C h x = true := by
  classical
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases input : w < n
    · let t : Fin n := ⟨w,input⟩
      exact .inl ⟨t,reach_mem_orIn t .refl,(val_ofFn C x t).symm.trans fires⟩
    obtain ⟨h,rfl⟩ : ∃ h, w = n+h := ⟨w-n,by omega⟩
    have len : h < C.gates.length := by omega
    obtain ⟨t,mt⟩ := raw
    have op : (gateAt C h).op = GateOp.or := by
      rcases ao.1 _ (gateAt_mem len) with a|o
      · rw [andRawEmpty a] at mt; exact ((Finset.notMem_empty _) mt).elim
      · exact o
    by_cases ordinary : h ∈ lam G C
    · obtain ⟨_,r0,r1,_⟩ := Finset.mem_filter.mp ordinary
      obtain ⟨v,member,smaller,on⟩ := (val_or (n := n) (by simp) len op).mp fires
      obtain ⟨i,vi⟩ := inputsAsOpnd ao len member
      have rv : (orIn n C v).Nonempty := by
        rw [vi]
        fin_cases i
        · exact r0
        · exact r1
      have step : OrStep n C (n+h) v := ⟨h,len,rfl,op,member,smaller⟩
      rcases ih v smaller (by omega) rv on with ⟨u,hu,yes⟩|⟨j,hj,present,path,yes⟩
      · exact .inl ⟨u,reach_mem_orIn u (.head step (mem_orIn_reach u hu)),yes⟩
      · exact .inr ⟨j,hj,present,.head ⟨step,h,ordinary,rfl⟩ path,yes⟩
    · have offTarget : ¬ BelowF G C h := by
        intro below
        have on := reach_var_val (pairInput t t) _ t (mem_orIn_reach t mt) (pairInput_left t t)
        exact G.irrefl ((graphFun_pair G t t).mp (below _ on))
      have exception : h ∈ orN G C \ lam G C := Finset.mem_sdiff.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr len,op,offTarget⟩,ordinary⟩
      exact .inr ⟨h,exception,⟨t,mt⟩,.refl,fires⟩

private theorem missing_operand (least : IsLeastAO G C) {u v : Fin n}
    (he : s(u,v) ∈ Ustar G C) {a : ℕ} (ha : a ∈ tops G C) :
    ∃ b : Fin 2, ¬ ∃ w ∈ side (n := n) C a b, w = u ∨ w = v := by
  classical
  let lit (b : Fin 2) := ∃ w ∈ side (n := n) C a b, w = u ∨ w = v
  have fresh : ∃ b, ¬ lit b := by
    by_contra! both
    obtain ⟨l,ml,hl⟩ := both 0
    obtain ⟨r,mr,hr⟩ := both 1
    have old := cleanAdj least.1 ha 0 ml mr
    obtain ⟨adj,kept⟩ := SimpleGraph.deleteEdges_adj.mp old
    rcases hl with rfl|rfl <;> rcases hr with rfl|rfl
    · exact adj.ne rfl
    · exact kept he
    · exact kept (Sym2.eq_swap .. ▸ he)
    · exact adj.ne rfl
  exact fresh

private theorem source (least : IsLeastAO G C) (empty : centreless G C = ∅)
    (h : ℕ) (unique : ∀ k ∈ atTops G C, k = h) (t : Fin n) (raw : t ∈ orIn n C (n+h))
    (u v : Fin n) (he : s(u,v) ∈ Ustar G C) :
    ∃ p d : Fin n, s(p,d) = s(u,v) ∧ (G.deleteEdges ↑(Ustar G C)).Adj t p ∧
      gateVal n C h (pairInput p d) = true ∧
      (∀ x : Fin n → Bool, x p = true → graphFun G ∅ x = false → gateVal n C h x = false) := by
  classical
  have real := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1
  obtain ⟨a,ha,fire⟩ := acceptedTop least real
  have data := topData ha
  let lit (b : Fin 2) := ∃ w ∈ side (n := n) C a b, w = u ∨ w = v
  have fresh := missing_operand least he ha
  have route (b : Fin 2) (absent : ¬ lit b) :
      Relation.ReflTransGen (OrStep n C) (opnd C a b) (n+h) ∧
        gateVal n C h (pairInput u v) = true := by
    have on := (andValOperands least.1 data.1 data.2.1 _).mp fire b
    have bound := opndBound least.1 data.1 b
    have nonempty := topSides empty ha b
    rcases firstSource (G := G) least.1 _ _ (by omega) nonempty on with
        ⟨w,m,yes⟩ | ⟨k,elig,rawK,pathK,yes⟩
    · exact (absent ⟨w,m,(pairInput_true _ _ _).mp yes⟩).elim
    · have same := unique k (Finset.mem_filter.mpr ⟨elig,rawK,a,ha,b,pathK⟩)
      subst k
      exact ⟨plainPath pathK,yes⟩
  obtain ⟨b,miss⟩ := fresh
  obtain ⟨path,on⟩ := route b miss
  have tl := reach_mem_orIn t (path.trans (mem_orIn_reach t raw))
  have oppositeHit : lit (1-b) := by
    by_contra no
    obtain ⟨path2,_⟩ := route (1-b) no
    have tr := reach_mem_orIn t (path2.trans (mem_orIn_reach t raw))
    exact (cleanAdj least.1 ha b tl tr).ne rfl
  obtain ⟨p,mp,sideEq⟩ := oppositeHit
  have old := cleanAdj least.1 ha b tl mp
  have safe (x : Fin n → Bool) (xp : x p = true) (off : graphFun G ∅ x = false) : gateVal n C h x = false := by
    apply Bool.eq_false_iff.mpr
    intro signal
    exact Bool.false_ne_true (off.symm.trans (firingTop least.1 ha path mp x signal xp))
  rcases sideEq with rfl|rfl
  · exact ⟨_,_,rfl,old,on,safe⟩
  · refine ⟨_,_,Sym2.eq_swap ..,old,?_,safe⟩
    have eq : pairInput p u = pairInput u p := by funext i; simp only [pairInput]; grind
    rwa [eq]



/-- A single exceptional OR available at all tops must distinguish every
transversal of the oriented matching except the unguarded one. -/
theorem single_capacity (bip : G.IsBipartite) (four : NoFourCycle G)
    (least : IsLeastAO G C) (top : TopForm G C) (empty : centreless G C = ∅)
    (h : ℕ) (single : atTops G C = {h}) (M : Finset (Sym2 (Fin n))) (sub : M ⊆ Ustar G C)
    (disjoint : ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ x ∈ e, x ∉ f) :
    2^M.card ≤ 2^(junk G C).card + 1 := by
  classical
  have mh : h ∈ atTops G C := single ▸ Finset.mem_singleton_self _
  obtain ⟨_, rawH, a, ma, b, path⟩ := Finset.mem_filter.mp mh
  obtain ⟨t,raw⟩ := rawH
  have one (k : ℕ) (mk : k ∈ atTops G C) : k = h := by simpa [single] using mk
  have chooseSource (e : M) :
      ∃ p d : Fin n, s(p,d) = e.val ∧ (G.deleteEdges ↑(Ustar G C)).Adj t p ∧
        gateVal n C h (pairInput p d) = true ∧
        (∀ x : Fin n → Bool, x p = true → graphFun G ∅ x = false → gateVal n C h x = false) := by
    have mem := sub e.2
    generalize eq : e.val = y at *
    induction y using Sym2.ind with
    | h u v => exact source least empty h one t raw u v mem
  choose p d pairEq old hit quiet using chooseSource
  obtain ⟨color⟩ := bip
  have edge (i : M) : G.Adj (p i) (d i) := by
    have m : s(p i,d i) ∈ G.edgeFinset := by rw [pairEq i]; exact (Finset.mem_sdiff.mp (sub i.2)).1
    exact SimpleGraph.mem_edgeFinset.mp m
  have anchor (i : M) := (SimpleGraph.deleteEdges_adj.mp (old i)).1
  have pinj {i j : M} (diff : i ≠ j) : p i ≠ p j := by
    intro eq
    have no := disjoint i i.2 j j.2 (Subtype.val_inj.not.mpr diff) (p i)
      ((pairEq i) ▸ Sym2.mem_mk_left _ _)
    exact no (eq ▸ ((pairEq j) ▸ Sym2.mem_mk_left _ _))
  have offCross {i j : M} (diff : i ≠ j) : ¬ G.Adj (p i) (d j) := by
    intro cross
    have unique := Finset.card_le_one.mp (four _ _ (pinj diff)) t
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (anchor i).symm, (anchor j).symm⟩) (d j)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, cross, edge j⟩)
    have kept := (SimpleGraph.deleteEdges_adj.mp (old j).symm).2
    rw [unique, pairEq j] at kept
    exact kept (sub j.2)
  have sameColor (i j : M) : color (p i) = color (p j) := by
    have a := color.valid (anchor i)
    have b := color.valid (anchor j)
    omega
  let endp (i : M) (pick : Bool) := if pick then d i else p i
  have independent (i j : M) (diff : i ≠ j) (r s : Bool) : ¬ G.Adj (endp i r) (endp j s) := by
    cases r <;> cases s <;> simp only [endp,ite_true,ite_false,Bool.false_eq_true]
    · exact fun a => color.valid a (sameColor i j)
    · exact offCross diff
    · exact fun a => offCross diff.symm a.symm
    · intro a
      have ci := color.valid (edge i)
      have cj := color.valid (edge j)
      have same := sameColor i j
      have apart := color.valid a
      omega
  let T := (Finset.univ : Finset (M → Bool)).erase (fun _ => true)
  let neg (q : T) (v : Fin n) := decide (∃ i : M, v = endp i (q.val i))
  have contains (q : T) (i : M) : neg q (endp i (q.val i)) = true := by exact decide_eq_true ⟨i,rfl⟩
  have clean (q : T) : graphFun G ∅ (neg q) = false := by
    apply Bool.eq_false_iff.mpr
    intro fired
    simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,decide_eq_true_eq] at fired
    simp only [neg,decide_eq_true_eq] at fired
    obtain ⟨u,v,adj,⟨i,rfl⟩,j,rfl⟩ := fired
    by_cases eq : i = j
    · subst j; exact adj.ne rfl
    · exact independent i j eq _ _ adj
  have off (q : T) : gateVal n C h (neg q) = false := by
    have someFalse : ∃ i, q.val i = false := by
      by_contra! no
      apply (Finset.mem_erase.mp q.2).1
      funext i; simpa using no i
    obtain ⟨i,hi⟩ := someFalse
    exact quiet i _ (by simpa [hi,endp] using contains q i) (clean q)
  have valid : SwitchCore.valid C (∅ : Finset ℕ) := by simp [SwitchCore.valid]
  let code (q : T) := SwitchCore.switches G C ∅ (neg q)
  have injection : Function.Injective code := by
    intro q r eq
    apply Subtype.ext
    funext i
    by_contra diff
    have covered : ∀ l, pairInput (p i) (d i) l = true → neg q l = true ∨ neg r l = true := by
      intro l on
      have cq := contains q i
      have cr := contains r i
      rcases (pairInput_true _ _ _).mp on with rfl | rfl <;>
        cases qv : q.val i <;> cases rv : r.val i <;> simp_all [endp]
    have left := SwitchCore.selected_on (G := G) least.1 valid (neg q)
    have right : SwitchCore.compatible G C ∅ (neg r) (code q) := by
      rw [eq]; exact SwitchCore.selected_on least.1 valid _
    have under : SwitchCore.observed G C ∅ (n+h) :=
      .inl ⟨a,(topData ma).1,(topData ma).2.1,b,plainPath path⟩
    rcases SwitchCore.union_compatible least.1 top valid covered left right _ under (hit i) with on | on
    · exact Bool.false_ne_true ((off q).symm.trans on)
    · exact Bool.false_ne_true ((off r).symm.trans on)
  have bound := Fintype.card_le_of_injective code injection
  simp only [Fintype.card_coe,Fintype.card_fun,Fintype.card_bool] at bound
  have cards := Finset.card_erase_add_one (s := (Finset.univ : Finset (M → Bool))) (Finset.mem_univ (fun _ => true))
  simp only [Finset.card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_coe] at cards
  change T.card + 1 = _ at cards
  simp only [SwitchCore.gates,Finset.union_empty] at bound
  omega


/-- A residual pair needs a first exceptional OR on a top operand. -/
theorem atTops_nonempty (least : IsLeastAO G C) (empty : centreless G C = ∅)
    (nonempty : (Ustar G C).Nonempty) : (atTops G C).Nonempty := by
  classical
  obtain ⟨e,he⟩ := nonempty
  induction e using Sym2.ind with
  | h u v =>
    have real := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1
    obtain ⟨a,ha,fire⟩ := acceptedTop least real
    obtain ⟨b,missing⟩ := missing_operand least he ha
    have data := topData ha
    have on := (andValOperands least.1 data.1 data.2.1 _).mp fire b
    have bd := opndBound least.1 data.1 b
    rcases firstSource (G := G) least.1 _ _ (by omega) (topSides empty ha b) on with
      ⟨w,m,yes⟩|⟨j,elig,raw,path,_⟩
    · exact (missing ⟨w,m,(pairInput_true _ _ _).mp yes⟩).elim
    · exact ⟨j,Finset.mem_filter.mpr ⟨elig,raw,a,ha,b,path⟩⟩

/-- For three disjoint residual edges and two dirty ANDs, both exceptional ORs
must independently reach top operands without passing through the other one. -/
theorem three_need_both (bip : G.IsBipartite) (four : NoFourCycle G)
    (least : IsLeastAO G C) (top : TopForm G C) (empty : centreless G C = ∅)
    (twoDirty : (junk G C).card = 2) (twoOR : (orN G C \ lam G C).card = 2)
    (M : Finset (Sym2 (Fin n))) (sub : M ⊆ Ustar G C) (three : 3 ≤ M.card)
    (disjoint : ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ x ∈ e, x ∉ f) :
    atTops G C = orN G C \ lam G C := by
  classical
  have subset : atTops G C ⊆ orN G C \ lam G C := Finset.filter_subset _ _
  apply Finset.eq_of_subset_of_card_le subset
  rw [twoOR]
  by_contra! few
  have mem : M.Nonempty := Finset.card_pos.mp (by omega)
  have pos := Finset.card_pos.mpr (atTops_nonempty least empty (mem.mono sub))
  obtain ⟨h,one⟩ := Finset.card_eq_one.mp (show (atTops G C).card = 1 by omega)
  have bound := single_capacity bip four least top empty h one M sub disjoint
  rw [twoDirty] at bound
  have eight : 2^3 ≤ 2^M.card := Nat.pow_le_pow_right (by decide) three
  omega

#print axioms three_need_both

#print axioms single_capacity
end ActiveOr
