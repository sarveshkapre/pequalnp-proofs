import GeneralThree
import StarGrowth

namespace PrivateMatching
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

abbrev shape (a b c d e : Fin n) : Finset (Sym2 (Fin n)) :=
  {s(a,b),s(b,c),s(d,e)}


/-- Every ordinary top gets its own matched edge. The remaining two matched
edges use the middle of the two-edge path and both endpoints of the isolated
edge. No ordinary matched leaf can also be a center. -/
structure Guards (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (a b c d e : Fin n) where
  port : tops G C → Fin 2
  center : tops G C → Fin n
  leaf : tops G C → Fin n
  raw : ∀ t : tops G C, side (n := n) C t (port t) = {center t}
  member : ∀ t : tops G C, leaf t ∈ side (n := n) C t (1 - port t)
  distinct : Function.Injective leaf
  distinctCenters : Function.Injective center
  other : ∀ t u, leaf t ≠ center u
  serve : ∀ u v, (G.deleteEdges ↑(Ustar G C)).Adj u v → ∃ t,
    (u = center t ∧ v ∈ side (n := n) C t (1 - port t)) ∨
    (v = center t ∧ u ∈ side (n := n) C t (1 - port t))
  pathTip : Fin n
  pathTip_eq : pathTip = a ∨ pathTip = c
  avoid : ∀ t, leaf t ≠ b ∧ leaf t ≠ pathTip ∧ leaf t ≠ d ∧ leaf t ≠ e
  centerAvoid : ∀ t, center t ≠ b ∧ center t ≠ pathTip ∧ center t ≠ d ∧ center t ≠ e

theorem private_guards (four : NoFourCycle G) (nonempty : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (top : TopForm G C) (three : (Ustar G C).card = 3)
    (S : Finset (Fin n)) (f : S → Fin n) (inj : Function.Injective f)
    (partners : ∀ i, f i ∉ S ∧ G.Adj i.val (f i)) (failure : ¬ GeneralThree.wireBound G C S)
    (a b c d e : Fin n) (pattern : Ustar G C = shape a b c d e) :
    Nonempty (Guards G C a b c d e) := by
  classical
  obtain ⟨_,zero,_,_⟩ := GeneralThree.remaining G C four nonempty least top three S f inj partners failure
  have tight := (GeneralThree.tight_if_failed G C four nonempty least top three S f inj partners failure).1
  obtain ⟨p,z,raw,serve⟩ := topIndexedStars four least.1 (Finset.card_eq_zero.mp zero)
  let Slot := tops G C ⊕ Bool
  let center : Slot → Fin n := Sum.elim z (fun i => if i then d else b)
  let acceptable : Slot → Fin n → Prop := Sum.elim
    (fun t w => w ∈ side (n := n) C t (1 - p t))
    (fun i w => if i then w = e else w = a ∨ w = c)
  let edge (i : S) := s(i.val,f i)
  have assign (i : S) : ∃ j : Slot, ∃ w, edge i = s(center j,w) ∧ acceptable j w := by
    by_cases residual : edge i ∈ Ustar G C
    · rw [pattern] at residual
      simp only [shape,Finset.mem_insert,Finset.mem_singleton] at residual
      rcases residual with h|h|h
      · exact ⟨.inr false,a,h.trans (Sym2.eq_swap),Or.inl rfl⟩
      · exact ⟨.inr false,c,h,Or.inr rfl⟩
      · exact ⟨.inr true,e,h,rfl⟩
    · obtain ⟨t,⟨hx,hy⟩|⟨hx,hy⟩⟩ := serve i.val (f i) (SimpleGraph.deleteEdges_adj.mpr ⟨(partners i).2,residual⟩)
      · exact ⟨.inl t, f i, by change s(i.val,f i) = s(z t,f i); rw [hx],hy⟩
      · exact ⟨.inl t, i.val, by change s(i.val,f i) = s(z t,i.val); rw [hx,Sym2.eq_swap],hy⟩
  choose j w hw using assign
  have disj {i k : S} {x : Fin n} (hi : x = i.val ∨ x = f i)
      (hk : x = k.val ∨ x = f k) : i = k := by
    rcases hi with rfl|rfl <;> rcases hk with h|h
    · exact Subtype.ext h
    · exact ((partners k).1 (h ▸ i.property)).elim
    · exact ((partners i).1 (h.symm ▸ k.property)).elim
    · exact inj h
  have onEdge (i : S) : (center (j i) = i.val ∨ center (j i) = f i) ∧ (w i = i.val ∨ w i = f i) := by
    rcases Sym2.eq_iff.mp (hw i).1 with h|h
    · exact ⟨Or.inl h.1.symm,Or.inr h.2.symm⟩
    · exact ⟨Or.inr h.2.symm,Or.inl h.1.symm⟩
  have jinj : Function.Injective j := by
    intro i k h
    exact disj (onEdge i).1 (h.symm ▸ (onEdge k).1)
  have bij := (Fintype.bijective_iff_injective_and_card j).mpr
    ⟨jinj,by simpa [Slot] using tight⟩
  let get := (Equiv.ofBijective j bij).symm
  have back (u : Slot) : j (get u) = u := (Equiv.ofBijective j bij).apply_symm_apply u
  let tip (u : Slot) := w (get u)
  have owned (u : Slot) : edge (get u) = s(center u,tip u) ∧ acceptable u (tip u) := by
    simpa only [tip,back] using hw (get u)
  have cMem (u : Slot) : center u = (get u).val ∨ center u = f (get u) := by
    simpa only [back] using (onEdge (get u)).1
  have lMem (u : Slot) : tip u = (get u).val ∨ tip u = f (get u) := (onEdge (get u)).2
  have cInj : Function.Injective center := by
    intro u v h; exact get.injective (disj (cMem u) (h.symm ▸ cMem v))
  have lInj : Function.Injective tip := by
    intro u v h; exact get.injective (disj (lMem u) (h.symm ▸ lMem v))
  have sep (u v : Slot) : tip u ≠ center v := by
    intro h
    have same := get.injective (disj (lMem u) (h.symm ▸ cMem v))
    subst v
    have neq := (partners (get u)).2.ne
    rcases Sym2.eq_iff.mp (owned u).1 with he|he
    · exact neq (he.1.trans (h.symm.trans he.2.symm))
    · exact neq (he.1.trans (h.trans he.2.symm))
  have re : tip (.inr true) = e := (owned (.inr true)).2
  have lTest (t : tops G C) (x : Bool) : tip (.inl t) ≠ tip (.inr x) :=
    by intro h; cases lInj h
  have cTest (t : tops G C) (x : Bool) : center (.inl t) ≠ center (.inr x) :=
    by intro h; cases cInj h
  refine ⟨⟨p,z,(fun t => tip (.inl t)),raw,(fun t => (owned (.inl t)).2),
    (fun _ _ h => Sum.inl.inj (lInj h)),(fun _ _ h => Sum.inl.inj (cInj h)),
    (fun t u => sep (.inl t) (.inl u)),serve,tip (.inr false),(owned (.inr false)).2,?_,?_⟩⟩
  · intro t
    exact ⟨sep (.inl t) (.inr false),lTest t false,sep (.inl t) (.inr true),re ▸ lTest t true⟩
  · intro t
    exact ⟨cTest t false,(sep (.inr false) (.inl t)).symm,cTest t true,re ▸ (sep (.inr true) (.inl t)).symm⟩


namespace Guards
variable {a b c d e : Fin n} (g : Guards G C a b c d e)

/-- Set all star centers to false. On the path, switch between deleting
its middle and deleting both tips. On the separate edge, delete one endpoint. -/
noncomputable def neg (middleOn dropD : Bool) (x : Fin n) : Bool := by
  classical
  exact decide ((∀ t, x ≠ g.center t) ∧
    (if middleOn then x ≠ a ∧ x ≠ c else x ≠ b) ∧ x ≠ (if dropD then d else e))

theorem neg_iff (q r : Bool) (x : Fin n) : g.neg q r x = true ↔
    (∀ t, x ≠ g.center t) ∧ (if q then x ≠ a ∧ x ≠ c else x ≠ b) ∧
      x ≠ (if r then d else e) := by classical simp [neg]

theorem independent (pattern : Ustar G C = shape a b c d e) (q r : Bool) :
    graphFun G ∅ (g.neg q r) = false := by
  classical
  apply Bool.eq_false_iff.mpr
  intro isEdge
  simp [graphFun] at isEdge
  obtain ⟨u,v,adj,hu,hv⟩ := isEdge
  obtain ⟨unc,up,us⟩ := (g.neg_iff q r u).mp hu
  obtain ⟨vnc,vp,vs⟩ := (g.neg_iff q r v).mp hv
  by_cases h : s(u,v) ∈ Ustar G C
  · rw [pattern] at h
    simp only [shape,Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with h|h|h
    · rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> cases q <;> simp_all
    · rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> cases q <;> simp_all
    · rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> cases r <;> simp_all
  · obtain ⟨t,⟨eq,_⟩|⟨eq,_⟩⟩ := g.serve u v (SimpleGraph.deleteEdges_adj.mpr ⟨adj,h⟩)
    · exact unc t eq
    · exact vnc t eq

theorem min_guard (r : Bool) (t : tops G C) : g.neg false r (g.leaf t) = true := by
  apply (g.neg_iff ..).mpr
  exact ⟨g.other t,(g.avoid t).1,by cases r <;> simp [(g.avoid t).2.2.1,(g.avoid t).2.2.2]⟩

theorem extra_guard_iff (r : Bool) (t : tops G C) :
    g.neg true r (g.leaf t) = true ↔ g.leaf t ≠ a ∧ g.leaf t ≠ c := by
  rw [neg_iff]
  cases r
  · simp [g.other, (g.avoid t).2.2.2]
  · simp [g.other, (g.avoid t).2.2.1]

theorem common_exception (r s : Bool) {t u : tops G C}
    (blocked : g.neg true r (g.leaf t) = false) (blocked' : g.neg true s (g.leaf u) = false) : t = u := by
  have tip {v : tops G C} {i : Bool} (h : g.neg true i (g.leaf v) = false) :
      g.leaf v = a ∨ g.leaf v = c := by
    by_contra! no
    exact Bool.noConfusion (h.symm.trans ((g.extra_guard_iff i v).mpr no))
  rcases g.pathTip_eq with ha | hc
  · have onlyC (v : tops G C) : g.leaf v ≠ a := fun h => (g.avoid v).2.1 (h.trans ha.symm)
    exact g.distinct (((tip blocked).resolve_left (onlyC t)).trans ((tip blocked').resolve_left (onlyC u)).symm)
  · have onlyA (v : tops G C) : g.leaf v ≠ c := fun h => (g.avoid v).2.1 (h.trans hc.symm)
    exact g.distinct (((tip blocked).resolve_right (onlyA t)).trans ((tip blocked').resolve_right (onlyA u)).symm)


/-- Whenever an actual center operand fires on a negative graph input, every
raw leaf on the opposite operand must be off. -/
theorem far_off (ao : IsAO2 n C) (t : tops G C) (x : Fin n → Bool)
    (negative : graphFun G ∅ x = false)
    (on : val C (List.ofFn x) (opnd C t (g.port t)) = true) :
    ∀ v ∈ side (n := n) C t (1 - g.port t), x v = false := by
  intro v mv
  apply Bool.eq_false_iff.mpr
  intro yes
  have far := sideVal mv yes
  obtain ⟨len,hand,clean⟩ := topData t.2
  have accepts := clean x ((andValOperands ao len hand x).mpr (fun p => by
    rcases opposite (g.port t) p with rfl | rfl
    · exact on
    · exact far))
  exact Bool.false_ne_true (negative.symm.trans accepts)

/-- Distinct top center operands cannot light on the two extra negative
inputs, even if they light on different choices of the isolated edge. -/
theorem unique_center_firing (ao : IsAO2 n C) (pattern : Ustar G C = shape a b c d e)
    {t u : tops G C} {r s : Bool}
    (on : val C (List.ofFn (g.neg true r)) (opnd C t (g.port t)) = true)
    (on' : val C (List.ofFn (g.neg true s)) (opnd C u (g.port u)) = true) : t = u :=
  g.common_exception r s
    (g.far_off ao t _ (g.independent pattern ..) on _ (g.member t))
    (g.far_off ao u _ (g.independent pattern ..) on' _ (g.member u))

/-- If a center operand lights on both extra inputs, its raw far port can
contain only its own private matched leaf and top centers. The two path
tips cannot be simultaneous neighbors of this center because they already
have the path middle as a common neighbor. -/
theorem exceptional_far (four : NoFourCycle G) (ao : IsAO2 n C)
    (pattern : Ustar G C = shape a b c d e) (ac : a ≠ c) (de : d ≠ e)
    (ab : G.Adj a b) (bc : G.Adj b c) (t : tops G C)
    (on : ∀ r : Bool, val C (List.ofFn (g.neg true r)) (opnd C t (g.port t)) = true) :
    (g.leaf t = a ∨ g.leaf t = c) ∧
    ∀ v ∈ side (n := n) C t (1 - g.port t), v = g.leaf t ∨ ∃ u, v = g.center u := by
  classical
  have off (r : Bool) := g.far_off ao t _ (g.independent pattern true r) (on r)
  have tips : g.leaf t = a ∨ g.leaf t = c := by
    by_contra! missed
    exact Bool.false_ne_true ((off false _ (g.member t)).symm.trans ((g.extra_guard_iff false t).mpr missed))
  refine ⟨tips,?_⟩
  intro v mem
  by_cases central : ∃ u, v = g.center u
  · exact Or.inr central
  push Not at central
  have vtip : v = a ∨ v = c := by
    by_contra! missed
    have yes (r : Bool) (test : v ≠ (if r then d else e)) : g.neg true r v = true :=
      (g.neg_iff ..).mpr ⟨central,missed,test⟩
    by_cases eqd : v = d
    · exact Bool.false_ne_true ((off false v mem).symm.trans (yes false (fun h => de (eqd.symm.trans h))))
    · exact Bool.false_ne_true ((off true v mem).symm.trans (yes true eqd))
  have existsC : g.center t ∈ side (n := n) C t (g.port t) := by rw [g.raw]; simp
  have adj (k : Fin n) (hit : k ∈ side (n := n) C t (1 - g.port t)) : G.Adj (g.center t) k :=
    (SimpleGraph.deleteEdges_adj.mp (cleanAdj ao t.2 (g.port t) existsC hit)).1
  have noBoth (ga : G.Adj (g.center t) a) (gc : G.Adj (g.center t) c) : False :=
    ac (Finset.card_le_one.mp (four (g.center t) b (g.centerAvoid t).1)
      a (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ga,ab.symm⟩)
      c (Finset.mem_filter.mpr ⟨Finset.mem_univ _,gc,bc⟩))
  have al := adj _ (g.member t)
  have av := adj v mem
  left
  rcases tips with l|l <;> rcases vtip with h|h
  · exact h.trans l.symm
  · exact (noBoth ((congrArg (G.Adj (g.center t)) l).mp al) ((congrArg (G.Adj (g.center t)) h).mp av)).elim
  · exact (noBoth ((congrArg (G.Adj (g.center t)) h).mp av) ((congrArg (G.Adj (g.center t)) l).mp al)).elim
  · exact h.trans l.symm


/-- In the ordinary graph each neighbor of a private leaf is a center.
A private leaf outside the five named vertices has the same property even
before the residual edges are removed. -/
theorem ordinary_neighbor (t : tops G C) {v : Fin n}
    (h : (G.deleteEdges ↑(Ustar G C)).Adj (g.leaf t) v) : ∃ u, v = g.center u := by
  obtain ⟨u,⟨bad,_⟩ | ⟨eq,_⟩⟩ := g.serve _ _ h
  · exact (g.other t u bad).elim
  · exact ⟨u,eq⟩

theorem private_neighbor (pattern : Ustar G C = shape a b c d e) (t : tops G C)
    {v : Fin n} (adj : G.Adj (g.leaf t) v) :
    (∃ u, v = g.center u) ∨ ((g.leaf t = a ∨ g.leaf t = c) ∧ v = b) := by
  classical
  by_cases res : s(g.leaf t,v) ∈ Ustar G C
  · rw [pattern] at res
    simp only [shape,Finset.mem_insert,Finset.mem_singleton] at res
    rcases res with h|h|h <;> rcases Sym2.eq_iff.mp h with ⟨l,r⟩|⟨l,r⟩
    · exact .inr ⟨.inl l,r⟩
    · exact ((g.avoid t).1 l).elim
    · exact ((g.avoid t).1 l).elim
    · exact .inr ⟨.inr l,r⟩
    · exact ((g.avoid t).2.2.1 l).elim
    · exact ((g.avoid t).2.2.2 l).elim
  · exact .inl (g.ordinary_neighbor t (SimpleGraph.deleteEdges_adj.mpr ⟨adj,res⟩))

/-- Explicit extension of a negative input by the matched leaf. This works
for every input with centers off. The exceptional path-tip leaf also works
whenever the path middle is off. -/
theorem extend_by_leaf (pattern : Ustar G C = shape a b c d e)
    (t : tops G C) (x : Fin n → Bool) (negative : graphFun G ∅ x = false)
    (centersOff : ∀ u, x (g.center u) = false)
    (guard : (g.leaf t ≠ a ∧ g.leaf t ≠ c) ∨ x b = false) :
    graphFun G ∅ (fun v => if v = g.leaf t then true else x v) = false := by
  have neighbors (v : Fin n) (adj : G.Adj (g.leaf t) v) : x v = false := by
    rcases g.private_neighbor pattern t adj with ⟨u, rfl⟩ | ⟨l,rfl⟩
    · exact centersOff u
    · rcases guard with h|h
      · exact l.elim (fun m => (h.1 m).elim) (fun m => (h.2 m).elim)
      · exact h
  apply Bool.eq_false_iff.mpr
  intro yes
  simp [graphFun] at yes
  obtain ⟨u,v,adj,hu,hv⟩ := yes
  by_cases lu : u = g.leaf t
  · subst u
    have ne := adj.ne.symm
    simp [ne,neighbors v adj] at hv
  by_cases lv : v = g.leaf t
  · subst v
    simp [lu,neighbors u adj.symm] at hu
  have active : graphFun G ∅ x = true := by
    simp [graphFun]
    exact ⟨u,v,adj,by simpa [lu] using hu,by simpa [lv] using hv⟩
  exact Bool.false_ne_true (negative.symm.trans active)

theorem rejects_guarded (ao : IsAO2 n C) (pattern : Ustar G C = shape a b c d e)
    (t : tops G C) (x : Fin n → Bool) (negative : graphFun G ∅ x = false)
    (centersOff : ∀ u, x (g.center u) = false)
    (guard : (g.leaf t ≠ a ∧ g.leaf t ≠ c) ∨ x b = false) :
    val C (List.ofFn x) (opnd C t (g.port t)) = false := by
  let y (v : Fin n) := if v = g.leaf t then true else x v
  have quiet := g.extend_by_leaf pattern t x negative centersOff guard
  apply Bool.eq_false_iff.mpr
  intro fired
  have inc (v : Fin n) (on : x v = true) : y v = true := by simp [y,on]
  have lim := opndBound ao (topData t.2).1 (g.port t)
  have on : val C (List.ofFn y) (opnd C t (g.port t)) = true :=
    StarGrowth.wire_mono ao inc (by have ht := (topData t.2).1; omega) fired
  have blocked := g.far_off ao t y quiet on _ (g.member t)
  simp [y] at blocked

/-- If the unmatched path tip is a top center, every center operand is off on
every graph-negative row supported on the other four vertices. -/
theorem inside_four (ao : IsAO2 n C) (pattern : Ustar G C = shape a b c d e)
    (tipA : g.pathTip = a) (inside : ∃ u, c = g.center u)
    (x : Fin n → Bool) (supp : ∀ v, x v = true → v = a ∨ v = b ∨ v = d ∨ v = e)
    (negative : graphFun G ∅ x = false) (t : tops G C) :
    val C (List.ofFn x) (opnd C t (g.port t)) = false := by
  obtain ⟨u,eq⟩ := inside
  apply g.rejects_guarded ao pattern t x negative
  · intro v; apply Bool.eq_false_iff.mpr; intro h
    rcases supp _ h with m|m|m|m
    · exact (g.centerAvoid v).2.1 (m.trans tipA.symm)
    · exact (g.centerAvoid v).1 m
    · exact (g.centerAvoid v).2.2.1 m
    · exact (g.centerAvoid v).2.2.2 m
  · exact Or.inl ⟨fun h => (g.avoid t).2.1 (h.trans tipA.symm),fun h => g.other t u (h.trans eq)⟩

end Guards
#print axioms private_guards
#print axioms Guards.independent
#print axioms Guards.common_exception
#print axioms Guards.unique_center_firing
#print axioms Guards.exceptional_far
#print axioms Guards.rejects_guarded
#print axioms Guards.inside_four
end PrivateMatching
