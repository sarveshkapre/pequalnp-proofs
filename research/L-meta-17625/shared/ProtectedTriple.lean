import SharedSwitch

namespace ProtectedResiduals
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_7465_aux
open PEqualNP.Outside.L_meta_7465_aux.Routing
open PEqualNP.Outside.L_meta_7465_aux.ThreeMatching

variable {n k : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- All protected residual pairs jointly require at least this many dirty ANDs.
At most three dirty ANDs and two exceptional ORs give a sharper six-clause bound.
The second assertion uses the generic upstream finite enumeration in L-meta-7465. -/
theorem limits (least : IsLeastAO G C) (top : TopForm G C)
    (port : tops G C → Fin 2) (z : tops G C → Fin n)
    (one : ∀ a : tops G C, side (n := n) C a (port a) = {z a})
    (e : Fin k → Bool → Fin n) (edges : ∀ i, G.Adj (e i false) (e i true))
    (outside : ∀ i a, z a ≠ e i false ∧ z a ≠ e i true)
    (neg : (Fin k → Bool) → Fin n → Bool) (noEdge : ∀ b, graphFun G ∅ (neg b) = false)
    (contains : ∀ b i, neg b (e i (b i)) = true)
    (leaves : ∀ (a : tops G C) b, ∃ w ∈ side C a (1-port a), neg b w = true) :
    k ≤ (junk G C).card ∧
      ((junk G C).card ≤ 3 → (orN G C \ lam G C).card ≤ 2 → k ≤ 2) := by
  classical
  let pair (i : Fin k) := (e i false, e i true)
  obtain ⟨S,form,positive,negative⟩ := starPromotionSeparation least port z one pair edges outside
    neg noEdge leaves
  have andRoute {h : ℕ} (mem : h ∈ S) : SharedSwitch.belowAnd n C (n+h) := by
    obtain ⟨_,_,a,path⟩ := form h mem
    exact ⟨a,(topData a.2).1,(topData a.2).2.1,port a,(orReaches_reach h _ path).1⟩
  let W : Set ℕ := {w | ∃ h ∈ S, w=n+h}
  have under (w : ℕ) (hw : w ∈ W) : SharedSwitch.belowAnd n C w := by
    obtain ⟨h,hm,rfl⟩ := hw
    exact andRoute hm
  have yes (i) : ∃ w ∈ W, SharedSwitch.value C (pairInput (e i false) (e i true)) w = true := by
    obtain ⟨h,hm,on⟩ := positive i
    exact ⟨n+h,⟨h,hm,rfl⟩,on⟩
  have no (b w) (hw : w ∈ W) : SharedSwitch.value C (neg b) w = false := by
    obtain ⟨h,hm,rfl⟩ := hw
    exact negative b h hm
  refine ⟨by simpa using SharedSwitch.matched_pairs_le_dirty least.1 top e neg W under contains yes no,?_⟩
  intro few small
  by_contra! big
  obtain ⟨g,hg,_⟩ := positive (⟨0,by omega⟩ : Fin k)
  obtain ⟨raw,f,bound,rep⟩ := selectedSix least.1 top S ⟨g,hg⟩ few small (by
    intro h mem
    obtain ⟨ex,occupied,a,path⟩ := form h mem
    exact ⟨ex,occupied,a,(topData a.2).1,(topData a.2).2.1,port a,path⟩)
  let N (b : Fin k → Bool) : Set (Fin n) := {v | neg b v = true}
  have pos (i : Fin k) : holds f (fun a => e i false ∈ raw a ∨ e i true ∈ raw a) := by
    have hit := (rep (pairInput (e i false) (e i true))).mpr (positive i)
    have same (a : ℕ) : (∃ v ∈ raw a, pairInput (e i false) (e i true) v = true) ↔
        e i false ∈ raw a ∨ e i true ∈ raw a := by
      constructor
      · rintro ⟨v,hv,on⟩
        rcases (pairInput_true _ _ _).mp on with rfl | rfl
        · exact Or.inl hv
        · exact Or.inr hv
      · rintro (left | right)
        · exact ⟨_,left,pairInput_left _ _⟩
        · exact ⟨_,right,pairInput_right _ _⟩
    exact (funext (fun a => propext (same a))) ▸ hit
  have rejects (b : Fin k → Bool) : ¬ holds f (fun a => ∃ v ∈ raw a, v ∈ N b) := by
    intro h
    obtain ⟨m,hm,on⟩ := (rep (neg b)).mp h
    exact Bool.false_ne_true ((negative b m hm).symm.trans on)
  have lower := substitutionLower f raw e N contains pos rejects
  simp only [Fintype.card_fin] at lower
  have eight := Nat.pow_le_pow_right (n := 2) (by decide) (show 3 ≤ k by omega)
  omega

#print axioms limits
end ProtectedResiduals
