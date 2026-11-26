import MatchingLabels
import MatchingRows
import MatchProjected

namespace MatchingBridge
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open MatchingRows MatchProjected

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

def coord : Fin 6 → Fin 3 × Bool := ![(0,false),(1,false),(2,false),(0,true),(1,true),(2,true)]
def v (D : MatchingLabels.Labels G C) (i : Fin 6) :=
  if (coord i).2 then D.right (coord i).1 else D.left (coord i).1

theorem vinj (D : MatchingLabels.Labels G C) : Function.Injective (v D) := by
  exact D.distinct.comp (by decide : Function.Injective coord)

def code (D : MatchingLabels.Labels G C) : Cross := PathBits.pack
  ![decide (G.Adj (D.left 2) (D.right 0)),decide (G.Adj (D.left 2) (D.right 1)),
    decide (G.Adj (D.left 0) (D.right 2)),decide (G.Adj (D.left 1) (D.right 2))]

private def lr (c : Cross) (i j : Fin 3) : Bool :=
  decide (i = j) || (decide (i = 2 ∧ j = 0) && c.getLsbD 0)
    || (decide (i = 2 ∧ j = 1) && c.getLsbD 1) || (decide (i = 0 ∧ j = 2) && c.getLsbD 2)
    || (decide (i = 1 ∧ j = 2) && c.getLsbD 3)
private def edgeAt (c : Cross) (i j : Fin 6) : Bool :=
  let a := coord i; let b := coord j
  if a.2 = b.2 then false else if a.2 then lr c b.1 a.1 else lr c a.1 b.1
private def diag (i j : Fin 6) : Bool := decide ((coord i).2 ≠ (coord j).2 ∧ (coord i).1 = (coord j).1)

private theorem diagAdj (D : MatchingLabels.Labels G C) (i : Fin 3) : G.Adj (D.left i) (D.right i) :=
  SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (D.diagonal i)).1

private theorem lrAdj (D : MatchingLabels.Labels G C) (i j : Fin 3) :
    G.Adj (D.left i) (D.right j) ↔ lr (code D) i j = true := by
  have restricted (h : G.Adj (D.left i) (D.right j)) : i = j ∨ i = 2 ∨ j = 2 := by
    by_cases mem : s(D.left i,D.right j) ∈ Ustar G C
    · obtain ⟨k,eq⟩ := (D.residual _).mp mem
      rcases Sym2.eq_iff.mp eq with e|e
      · have idl := @D.distinct (i,false) (k,false) e.1
        have idr := @D.distinct (j,true) (k,true) e.2
        exact .inl ((congrArg Prod.fst idl).trans (congrArg Prod.fst idr).symm)
      · have bad := @D.distinct (i,false) (k,true) e.1
        cases bad
    · obtain ⟨t,⟨eq,_⟩|⟨eq,_⟩⟩ := D.serves _ _ (SimpleGraph.deleteEdges_adj.mpr ⟨h,mem⟩)
      · exact .inr (.inl (by by_contra ne; exact (D.avoid t i ne).1 eq.symm))
      · exact .inr (.inr (by by_contra ne; exact (D.avoid t j ne).2 eq.symm))
  have bits (k : Fin 4) : (code D).getLsbD k =
      ![decide (G.Adj (D.left 2) (D.right 0)),decide (G.Adj (D.left 2) (D.right 1)),
        decide (G.Adj (D.left 0) (D.right 2)),decide (G.Adj (D.left 1) (D.right 2))] k := PathBits.get_pack ..
  have b0 := bits 0; have b1 := bits 1; have b2 := bits 2; have b3 := bits 3
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val] at b0 b1 b2 b3
  fin_cases i <;> fin_cases j <;> simp_all [lr,diagAdj]

private theorem edge_iff (D : MatchingLabels.Labels G C) (i j : Fin 6) :
    G.Adj (v D i) (v D j) ↔ edgeAt (code D) i j = true := by
  cases hi : (coord i).2 <;> cases hj : (coord j).2
  · simp only [v,edgeAt,hi,hj,ite_true,Bool.false_eq_true,ite_false]
    exact ⟨fun a => D.color.valid a ((D.leftColor _).trans (D.leftColor _).symm),False.elim⟩
  · simpa [v,edgeAt,hi,hj] using lrAdj D (coord i).1 (coord j).1
  · simpa [v,edgeAt,hi,hj,G.adj_comm] using lrAdj D (coord j).1 (coord i).1
  · simp only [v,edgeAt,hi,hj,ite_true,Bool.false_eq_true]
    exact ⟨fun a => D.color.valid a ((D.rightColor _).trans (D.rightColor _).symm),False.elim⟩

private theorem diag_mem (D : MatchingLabels.Labels G C) {i j : Fin 6} (h : diag i j = true) :
    s(v D i,v D j) ∈ Ustar G C := by
  obtain ⟨diff,same⟩ := of_decide_eq_true h
  cases hi : (coord i).2 <;> cases hj : (coord j).2
  · exact (diff (hi.trans hj.symm)).elim
  · simpa [v,hi,hj,same] using D.diagonal (coord j).1
  · simpa [v,hi,hj,same,Sym2.eq_swap (a := D.right (coord j).1)] using D.diagonal (coord j).1
  · exact (diff (hi.trans hj.symm)).elim

private theorem sideColor (D : MatchingLabels.Labels G C) {i j : Fin 6}
    (h : D.color (v D i) = D.color (v D j)) : (coord i).2 = (coord j).2 := by
  cases hi : (coord i).2 <;> cases hj : (coord j).2 <;> simp_all [v,D.leftColor,D.rightColor]

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

private def geometric (c : Cross) (m : Raw) :=
  ∀ i j : Fin 6, m.getLsbD i = true → m.getLsbD j = true →
    (coord i).2 = (coord j).2 ∧ (i ≠ j → ∀ k : Fin 6, edgeAt c k i = true → edgeAt c k j = true →
      diag k i ≠ true ∧ diag k j ≠ true)

private theorem allowed_of_geom : ∀ (c : Cross) (m : Raw), geometric c m → allowed c m = true := by
  unfold geometric
  decide

private theorem leafAllowed (D : MatchingLabels.Labels G C) (four : NoFourCycle G)
    (ao : IsAO2 n C) (a : tops G C) :
    allowed (code D) (raw (v D) (side (n := n) C a (1-D.port a))) = true := by
  apply allowed_of_geom
  intro i j hi hj
  obtain ⟨same,four'⟩ := leaf_geometry (v D) (vinj D) ao four D.color a (D.port a) (D.center a) (D.raw a) i j hi hj
  refine ⟨sideColor D same,?_⟩
  intro ne k ki kj
  have off := four' ne (v D k) ((edge_iff D ..).mpr ki) ((edge_iff D ..).mpr kj)
  exact ⟨fun h => off.1 (diag_mem D h),fun h => off.2 (diag_mem D h)⟩

private theorem literalAllowed (D : MatchingLabels.Labels G C) (u : Fin n) :
    allowed (code D) (raw (v D) {u}) = true := by
  apply allowed_of_geom
  intro i j hi hj
  have ei : v D i = u := by simpa only [raw_bit,decide_eq_true_eq,Finset.mem_singleton] using hi
  have ej : v D j = u := by simpa only [raw_bit,decide_eq_true_eq,Finset.mem_singleton] using hj
  have eq := vinj D (ei.trans ej.symm)
  exact ⟨eq ▸ rfl,fun ne => (ne eq).elim⟩

private theorem allowed_sub : ∀ (c : Cross) (a b : Raw), (a &&& ~~~b) = 0 →
    allowed c b = true → allowed c a = true := by decide

private theorem ordAllowed (D : MatchingLabels.Labels G C) (four : NoFourCycle G)
    (ao : IsAO2 n C) {k : Nat} (hk : k ∈ lam G C) :
    allowed (code D) (raw (v D) (orIn n C (n+k))) = true := by
  obtain ⟨_,_,_,t,ht,p,_,reach⟩ := Finset.mem_filter.mp hk
  let a : tops G C := ⟨t,ht⟩
  have sub : orIn n C (n+k) ⊆ side (n := n) C a p := fun x hx =>
    reach_mem_orIn x ((orReaches_reach _ _ reach).1.trans (mem_orIn_reach x hx))
  apply allowed_sub _ _ _ (raw_sub _ sub)
  rcases opposite (D.port a) p with rfl|rfl
  · rw [D.raw]; exact literalAllowed ..
  · exact leafAllowed D four ao a

private theorem graphOK' (D : MatchingLabels.Labels G C) (four : NoFourCycle G) : graphOK (code D) = true := by
  have leftNe (i : Fin 3) (hi : i ≠ 2) : D.left i ≠ D.left 2 := by
    intro h; exact hi (congrArg Prod.fst (@D.distinct (i,false) (2,false) h))
  have rightNe (i : Fin 3) (hi : i ≠ 2) : D.right i ≠ D.right 2 := by
    intro h; exact hi (congrArg Prod.fst (@D.distinct (i,true) (2,true) h))
  have excl (i : Fin 3) (hi : i ≠ 2) (a : G.Adj (D.left 2) (D.right i))
      (b : G.Adj (D.left i) (D.right 2)) : False :=
    rightNe _ hi (Finset.card_le_one.mp (four _ _ (leftNe i hi)) (D.right i)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,diagAdj D i,a⟩) (D.right 2)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,b,diagAdj D 2⟩))
  have bit (k : Fin 4) := PathBits.get_pack
    (f := ![decide (G.Adj (D.left 2) (D.right 0)),decide (G.Adj (D.left 2) (D.right 1)),
      decide (G.Adj (D.left 0) (D.right 2)),decide (G.Adj (D.left 1) (D.right 2))]) k
  have h0 := bit 0; have h1 := bit 1; have h2 := bit 2; have h3 := bit 3
  change (code D).getLsbD 0 = decide (G.Adj (D.left 2) (D.right 0)) at h0
  change (code D).getLsbD 1 = decide (G.Adj (D.left 2) (D.right 1)) at h1
  change (code D).getLsbD 2 = decide (G.Adj (D.left 0) (D.right 2)) at h2
  change (code D).getLsbD 3 = decide (G.Adj (D.left 1) (D.right 2)) at h3
  simp only [graphOK,h0,h1,h2,h3,Bool.and_eq_true,Bool.not_eq_true',Bool.and_eq_false_imp,
    decide_eq_true_eq,decide_eq_false_iff_not]
  exact ⟨excl 0 (by decide),excl 1 (by decide)⟩

private theorem leaf_rule : ∀ (c : Cross) (z m : Raw),
    (∀ i : Fin 6, z.getLsbD i = true → i = 2 ∨ i = 5) →
    (∀ i j : Fin 6, z.getLsbD i = true → z.getLsbD j = true → i = j) →
    (∀ i j : Fin 6, z.getLsbD i = true → m.getLsbD j = true →
      edgeAt c i j = true ∧ diag i j ≠ true) →
    leafOK c z m = true := by decide

private theorem centerOK (D : MatchingLabels.Labels G C) (ao : IsAO2 n C) (t : tops G C) :
    leafOK (code D) (raw (v D) (side (n := n) C t (D.port t)))
      (raw (v D) (side (n := n) C t (1-D.port t))) = true := by
  have eq (i : Fin 6) (h : (raw (v D) (side (n := n) C t (D.port t))).getLsbD i = true) :
      v D i = D.center t := by simpa only [raw_bit,D.raw,Finset.mem_singleton,decide_eq_true_eq] using h
  apply leaf_rule
  · intro i h
    have q := eq i h
    have a := D.avoid t 0 (by decide)
    have b := D.avoid t 1 (by decide)
    fin_cases i <;> simp_all [v,coord]
  · intro i j hi hj
    exact vinj D ((eq i hi).trans (eq j hj).symm)
  · intro i j hi hj
    have fact := leaf_spec (v D) ao t (D.port t) _ (D.raw t) hi hj
    exact ⟨(edge_iff D ..).mp fact.1,fun h => fact.2 (diag_mem D h)⟩

private theorem independent_rule : ∀ (c : Cross) (m : Raw), independent c m = true →
    ∀ i j : Fin 6, edgeAt c i j = true → m.getLsbD i = true → m.getLsbD j ≠ true := by decide

private theorem neg (D : MatchingLabels.Labels G C) (r : Raw) (h : independent (code D) r = true) :
    graphFun G ∅ (input (v D) r) = false := by
  apply Bool.eq_false_iff.mpr
  intro yes
  obtain ⟨i,j,edge,hi,hj⟩ := (edge_on_row G (v D) r).mp yes
  exact independent_rule _ r h i j ((edge_iff D ..).mp edge) hi hj

private theorem positive_rule : ∀ (k : Fin 3) (i : Fin 6),
    (positive k).getLsbD i = true ↔ (coord i).1 = k := by decide

private theorem pos (D : MatchingLabels.Labels G C) (k : Fin 3) :
    input (v D) (positive k) = pairInput (D.left k) (D.right k) := by
  funext u
  apply Bool.eq_iff_iff.mpr
  rw [pairInput_true]
  simp only [input,decide_eq_true_eq]
  constructor
  · rintro ⟨i,rfl,hi⟩
    have eq := (positive_rule k i).mp hi
    cases h : (coord i).2 <;> simp [v,h,eq]
  · have both : ∀ k : Fin 3, (∃ i : Fin 6, coord i = (k,false)) ∧
        (∃ i : Fin 6, coord i = (k,true)) := by decide
    rintro (rfl|rfl)
    · obtain ⟨i,hi⟩ := (both k).1
      exact ⟨i,by simp [v,hi],(positive_rule k i).mpr (congrArg Prod.fst hi)⟩
    · obtain ⟨i,hi⟩ := (both k).2
      exact ⟨i,by simp [v,hi],(positive_rule k i).mpr (congrArg Prod.fst hi)⟩

structure Facts (D : MatchingLabels.Labels G C) : Prop where
  graph : graphOK (code D) = true
  literal : ∀ u, allowed (code D) (raw (v D) {u}) = true
  ordinary : ∀ k ∈ lam G C, allowed (code D) (raw (v D) (orIn n C (n+k))) = true
  leaf : ∀ a : tops G C, allowed (code D) (raw (v D) (side (n := n) C a (1-D.port a))) = true
  center : ∀ a : tops G C, leafOK (code D) (raw (v D) (side (n := n) C a (D.port a)))
    (raw (v D) (side (n := n) C a (1-D.port a))) = true
  positive : ∀ i, input (v D) (MatchProjected.positive i) = pairInput (D.left i) (D.right i)
  negative : ∀ r, independent (code D) r = true → graphFun G ∅ (input (v D) r) = false

theorem facts (D : MatchingLabels.Labels G C) (four : NoFourCycle G) (ao : IsAO2 n C) : Facts D :=
  ⟨graphOK' D four,literalAllowed D,fun _ hk => ordAllowed D four ao hk,leafAllowed D four ao,
    centerOK D ao,pos D,neg D⟩

#print axioms facts
end MatchingBridge
