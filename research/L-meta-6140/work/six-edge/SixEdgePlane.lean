import SixEdgeCircuit
import FourEdges

namespace SixEdge.Plane

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open ResidualDegree PlaneFour

/-- One ordinary top at each line, with its singleton side specified. -/
structure Stars (C : Circuit) where
  index : Fin 13 ≃ ↥(tops plane C)
  center : ↥(tops plane C) → Fin 2
  singleton : ∀ l, side (n := 26) C (index l).val (center (index l)) = {ln l}

variable {C : Circuit}

def leaf (S : Stars C) (l : Fin 13) : Finset (Fin 26) :=
  side (n := 26) C (S.index l).val (1-S.center (S.index l))

private theorem colors : ∀ u v, plane.Adj u v → (u.val < 13 ↔ ¬ v.val < 13) := by decide
private theorem finTwo (b : Fin 2) : b = 0 ∨ b = 1 := by fin_cases b <;> simp

def positives : Finset (Fin 13 × Fin 13) :=
  Finset.univ.filter fun (p,l) => incident p l

theorem positives_card : positives.card = 52 := by decide

theorem adj_coordinates : ∀ p l : Fin 13, incident p l ↔ plane.Adj (pt p) (ln l) := by decide

theorem leaf_nonempty (S : Stars C) (empty : centreless plane C = ∅) (l : Fin 13) :
    (leaf S l).Nonempty :=
  topSides empty (S.index l).property _

theorem leaf_neighbor (S : Stars C) (ao : IsAO2 26 C)
    {l : Fin 13} {v : Fin 26} (mem : v ∈ leaf S l) : plane.Adj v (ln l) := by
  have cl : ln l ∈ side (n := 26) C (S.index l).val (S.center (S.index l)) := by
    rw [S.singleton]; simp
  have adj := cleanAdj ao (S.index l).property (S.center (S.index l)) cl mem
  exact (SimpleGraph.deleteEdges_adj.mp adj).1.symm

theorem leaf_point (S : Stars C) (ao : IsAO2 26 C) {l : Fin 13} {v : Fin 26}
    (mem : v ∈ leaf S l) : ∃ p : Fin 13, v = pt p := by
  have lt := (colors v (ln l) (leaf_neighbor S ao mem)).mpr (by simp [ln])
  exact ⟨⟨v.val,lt⟩, Fin.ext rfl⟩

theorem matches_ports (S : Stars C) (least : IsLeastAO plane C) (top : TopForm plane C)
    {g : ℕ} (hg : g ∈ charged plane C) (i : Fin 2) :
    (∃ k ∈ charged plane C, k < g ∧ opnd C g i = 26+k) ∨
    ((side (n := 26) C g i).Nonempty ∧
      ((∃ v : Fin 26, side (n := 26) C g i ⊆ {v}) ∨
        ∃ l : Fin 13, side (n := 26) C g i ⊆ leaf S l) ∧
      (∀ k ∈ portPromotions plane C (opnd C g i), k ∈ exceptional plane C ∧ k < g ∧
        (orIn 26 C (26+k)).Nonempty ∧ orIn 26 C (26+k) ⊆ side C g i) ∧
      ∀ x, val C (List.ofFn x) (opnd C g i) = true ↔
        (∃ u ∈ side (n := 26) C g i, x u = true) ∨
        ∃ k ∈ portPromotions plane C (opnd C g i), gateVal 26 C k x = true) := by
  have singleton (a : ↥(tops plane C)) :
      ∃ t : Fin 26, side (n := 26) C a.val (S.center a) = {t} := by
    obtain ⟨l, rfl⟩ := S.index.surjective a
    exact ⟨ln l,S.singleton l⟩
  rcases charged_port least top S.center singleton hg i with direct | ⟨raw, fit, other⟩
  · exact Or.inl direct
  refine Or.inr ⟨raw, ?_, other⟩
  rcases fit with one | ⟨a, fits⟩
  · exact Or.inl one
  · obtain ⟨l, rfl⟩ := S.index.surjective a
    exact Or.inr ⟨l,fits⟩

theorem centre_promoter_unique (S : Stars C) {l m : Fin 13} {g : ℕ}
    (h₁ : g ∈ portPromotions plane C (opnd C (S.index l).val (S.center (S.index l))))
    (h₂ : g ∈ portPromotions plane C (opnd C (S.index m).val (S.center (S.index m)))) :
    l = m := by
  classical
  obtain ⟨_, ⟨u, raw⟩, reach₁⟩ := Finset.mem_filter.mp h₁
  obtain ⟨_, _, reach₂⟩ := Finset.mem_filter.mp h₂
  have at₁ : u ∈ side (n := 26) C (S.index l).val (S.center (S.index l)) :=
    reach_mem_orIn u ((orReaches_reach g _ reach₁).1.trans (mem_orIn_reach u raw))
  have at₂ : u ∈ side (n := 26) C (S.index m).val (S.center (S.index m)) :=
    reach_mem_orIn u ((orReaches_reach g _ reach₂).1.trans (mem_orIn_reach u raw))
  rw [S.singleton] at at₁ at₂
  exact Fin.ext (by
    have eq := (Finset.mem_singleton.mp at₁).symm.trans (Finset.mem_singleton.mp at₂)
    have values := congrArg Fin.val eq
    change 13 + l.val = 13 + m.val at values
    omega)

/-- A raw star retains an incidence exactly when its point is on the leaf port
    of the top indexed by that line. -/
theorem kept_iff_mem_leaf (S : Stars C) (ao : IsAO2 26 C) (p l : Fin 13) :
    (plane.deleteEdges ↑(Ustar plane C)).Adj (pt p) (ln l) ↔ pt p ∈ leaf S l := by
  classical
  constructor
  · intro h
    obtain ⟨adj, keep⟩ := SimpleGraph.deleteEdges_adj.mp h
    have star : s(pt p, ln l) ∈ starEdges plane C := by
      by_contra missing
      exact keep (Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr adj, missing⟩)
    obtain ⟨a, ha, cross⟩ := Finset.mem_biUnion.mp star
    obtain ⟨⟨u,v⟩, uv, eq⟩ := Finset.mem_image.mp cross
    obtain ⟨left, right⟩ := Finset.mem_product.mp uv
    obtain ⟨j, ej⟩ := S.index.surjective ⟨a,ha⟩
    have rawCenter := S.singleton j
    have la : (S.index j).val = a := congrArg Subtype.val ej
    let b := S.center (S.index j)
    have left' : u ∈ side (n := 26) C (S.index j).val 0 := la ▸ left
    have right' : v ∈ side (n := 26) C (S.index j).val 1 := la ▸ right
    have route : (u = ln j ∧ v ∈ leaf S j) ∨ (v = ln j ∧ u ∈ leaf S j) := by
      change side (n := 26) C (S.index j).val b = {ln j} at rawCenter
      change u ∈ _ at left'
      rcases finTwo b with zero | one
      · left
        rw [zero] at rawCenter
        exact ⟨Finset.mem_singleton.mp (rawCenter ▸ left'), by simpa [leaf, ← show b = S.center (S.index j) from rfl, zero] using right'⟩
      · right
        rw [one] at rawCenter
        exact ⟨Finset.mem_singleton.mp (rawCenter ▸ right'), by simpa [leaf, ← show b = S.center (S.index j) from rfl, one] using left'⟩
    have separate : ∀ (p j : Fin 13), pt p ≠ ln j := by
      intro p j eq
      have vals := congrArg Fin.val eq
      change p.val = 13 + j.val at vals
      omega
    have lineInj : Function.Injective ln := by
      intro j l eq
      have vals := congrArg Fin.val eq
      change 13 + j.val = 13 + l.val at vals
      exact Fin.ext (by omega)
    change s(u,v) = s(pt p,ln l) at eq
    rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      rcases route with ⟨r, h⟩ | ⟨r, h⟩
    · exact (separate _ _ r).elim
    · simpa only [← lineInj r] using h
    · simpa only [← lineInj r] using h
    · exact (separate _ _ r).elim
  · intro h
    have raw : ln l ∈ side (n := 26) C (S.index l).val (S.center (S.index l)) := by
      rw [S.singleton]; simp
    exact (cleanAdj ao (S.index l).property _ raw h).symm

/-- Every incidence fires at least one top and every edge-free input fires none.
    In particular this holds on the selected finite test rows. -/
theorem test_obligations (S : Stars C) (least : IsLeastAO plane C) :
    (∀ p l : Fin 13, plane.Adj (pt p) (ln l) →
      ∃ j : Fin 13, gateVal 26 C (S.index j).val (pairInput (pt p) (ln l)) = true) ∧
    (∀ x : Fin 26 → Bool, graphFun plane ∅ x = false →
      ∀ j : Fin 13, gateVal 26 C (S.index j).val x = false) := by
  constructor
  · intro p l adj
    obtain ⟨a, ha, on⟩ := acceptedTop least adj
    obtain ⟨j, eq⟩ := S.index.surjective ⟨a,ha⟩
    exact ⟨j, congrArg Subtype.val eq ▸ on⟩
  · intro x off j
    exact Bool.eq_false_iff.mpr
      (fun on => Bool.false_ne_true (off.symm.trans ((topData (S.index j).property).2.2 x on)))

noncomputable def residualPairs (S : Stars C) : Finset (Fin 13 × Fin 13) := by
  classical
  exact positives.filter fun (p,l) => pt p ∉ leaf S l

theorem residual_card (S : Stars C) (ao : IsAO2 26 C) :
    (residualPairs S).card = (Ustar plane C).card := by
  classical
  have mem (p l : Fin 13) : (p,l) ∈ residualPairs S ↔ edge p l ∈ Ustar plane C := by
    simp only [residualPairs, positives, Finset.mem_filter, Finset.mem_univ, true_and,
      adj_coordinates]
    rw [← kept_iff_mem_leaf S ao, SimpleGraph.deleteEdges_adj]
    simp only [SetLike.mem_coe]
    constructor
    · rintro ⟨adj, missing⟩
      by_contra nr
      exact missing ⟨adj,nr⟩
    · intro he
      exact ⟨SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1, fun h => h.2 he⟩
  have coordinates (v : Fin 26) : (∃ p : Fin 13, v = pt p) ∨ (∃ l : Fin 13, v = ln l) := by
    by_cases h : v.val < 13
    · exact Or.inl ⟨⟨v.val,h⟩, Fin.ext rfl⟩
    · right
      let l : Fin 13 := ⟨v.val-13, by have := v.isLt; omega⟩
      exact ⟨l, Fin.ext (by change v.val = 13+(v.val-13); omega)⟩
  apply Finset.card_bij (fun q _ => edge q.1 q.2)
  · rintro ⟨p,l⟩ h
    exact (mem p l).mp h
  · rintro ⟨p,l⟩ _ ⟨q,m⟩ _ eq
    change s(pt p,ln l) = s(pt q,ln m) at eq
    rcases Sym2.eq_iff.mp eq with ⟨ep, el⟩ | ⟨bad,_⟩
    · have vp := congrArg Fin.val ep
      have vl := congrArg Fin.val el
      change p.val = q.val at vp
      change 13+l.val = 13+m.val at vl
      have sameLine : l = m := Fin.ext (by omega)
      exact Prod.ext (Fin.ext vp) sameLine
    · have vals := congrArg Fin.val bad
      change p.val = 13+m.val at vals
      have := p.isLt
      omega
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have both := colors u v (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1)
      rcases coordinates u with ⟨p,rfl⟩ | ⟨l,rfl⟩ <;>
        rcases coordinates v with ⟨q,rfl⟩ | ⟨m,rfl⟩
      · simp [pt, p.isLt, q.isLt] at both
      · exact ⟨(p,m), (mem p m).mpr he, rfl⟩
      · have sw : edge q l = s(ln l,pt q) := Sym2.eq_swap ..
        exact ⟨(q,l), (mem q l).mpr (sw ▸ he), sw⟩
      · simp [ln] at both

theorem case_covered (S : Stars C) (least : IsLeastAO plane C)
    (empty : centreless plane C = ∅) (two : (junk plane C).card = 2)
    (three : (exceptional plane C).card = 3) :
    let count := charged_card two three
    (ofSlots (dirtyAt count), ofSlots (centerAt count S.center)) ∈ cases :=
  circuit_case least empty two three S.center

#print axioms matches_ports
#print axioms case_covered
#print axioms residual_card

end SixEdge.Plane
