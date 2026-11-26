import PathGeometry
import P4Ports
import StarGrowth

namespace PathPromotion
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open PathGeometry

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

private theorem maximal_masks : ∀ v : Fin 4 → Bool,
    (¬ ∃ j : Fin 3, v j.castSucc = true ∧ v j.succ = true) →
    ∃ i : Fin 3, ∀ j, v j = true → kept i j = true := by decide

private theorem monotone (ao : IsAO2 n C) (h : ℕ) (len : h < C.gates.length)
    {x y : Fin n → Bool} (incl : ∀ u, x u = true → y u = true)
    (on : gateVal n C h x = true) : gateVal n C h y = true := by
  rw [gateVal_eq_val] at on ⊢
  exact StarGrowth.wire_mono ao incl (by omega) on

/-- A fixed selection of earlier exceptional ORs computes exactly the three-edge
path on its four vertices. Each selected OR has nonempty global raw support,
but no raw support among the four path vertices. -/
theorem separate (least : IsLeastAO G C) (e : Fin 4 → Fin n) (W : Witness G C e) :
    ∃ K : Finset ℕ,
      (∀ h ∈ K, h ∈ P4Ports.active G C ∧ h ∈ orN G C \ lam G C ∧
        (gateAt C h).op = GateOp.or ∧ (orIn n C (n+h)).Nonempty ∧
        ∀ j, e j ∉ orIn n C (n+h)) ∧
      ∀ x : Fin n → Bool, (∀ v, x v = true → ∃ j, v = e j) →
        ((∃ h ∈ K, gateVal n C h x = true) ↔
         ∃ j : Fin 3, x (e j.castSucc) = true ∧ x (e j.succ) = true) := by
  classical
  let pairs (i : Fin 3) := (e i.castSucc,e i.succ)
  obtain ⟨K,form,positive,negative⟩ := starPromotionSeparation least W.b W.z W.raw pairs
    W.positive (fun i a => ⟨W.outside a i.castSucc,W.outside a i.succ⟩)
    W.neg W.noEdge W.leaf
  refine ⟨K,?_,?_⟩
  · intro h m
    obtain ⟨ex,nonempty,a,path⟩ := form h m
    have route := (orReaches_reach h _ path).1
    have belongs : h ∈ P4Ports.active G C := Finset.mem_union_right _ (Finset.mem_filter.mpr
      ⟨ex,a,(topData a.2).1,(topData a.2).2.1,W.b a,route⟩)
    refine ⟨belongs,ex,(orData ex).2.1,nonempty,?_⟩
    intro j raw
    have yes : e j ∈ side (n := n) C a (W.b a) :=
      reach_mem_orIn _ (route.trans (mem_orIn_reach _ raw))
    rw [W.raw,Finset.mem_singleton] at yes
    exact W.outside a j yes.symm
  · intro x supp
    constructor
    · rintro ⟨h,m,on⟩
      by_contra miss
      obtain ⟨i,covers⟩ := maximal_masks (fun j => x (e j)) miss
      have incl (v : Fin n) (yes : x v = true) : W.neg i v = true := by
        obtain ⟨j,rfl⟩ := supp v yes
        rw [W.bits]; exact covers j yes
      have active := monotone least.1 h (orData (form h m).1).1 incl on
      exact Bool.false_ne_true ((negative i h m).symm.trans active)
    · rintro ⟨j,left,right⟩
      obtain ⟨h,m,on⟩ := positive j
      refine ⟨h,m,monotone least.1 h (orData (form h m).1).1 ?_ on⟩
      intro v hit
      rcases (pairInput_true _ _ _).mp hit with rfl|rfl
      · exact left
      · exact right

#print axioms separate
end PathPromotion
