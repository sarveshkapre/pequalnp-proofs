import SharedSwitch

namespace CentreSwitch
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_7465_aux
open PEqualNP.Outside.L_meta_7465_aux.Routing

variable {n k : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- At an AND, a true input with no OR-only route to a variable has a true dirty
AND somewhere below it. This works on an arbitrary assignment. -/
theorem empty_port_needs_dirty (ao : IsAO2 n C) (top : TopForm G C) {a : ℕ}
    (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and) {p : Fin 2}
    (empty : side (n := n) C a p = ∅) (x : Fin n → Bool)
    (on : SharedSwitch.value C x (opnd C a p) = true) :
    ∃ j ∈ junk G C, gateVal n C j x = true := by
  obtain ⟨w,path,yes,h⟩ := or_trace (n := n) (C := C) (x := List.ofFn x) (by simp) _ on
  rcases h with input | ⟨j,len,rfl,op⟩
  · have mem : (⟨w,input⟩ : Fin n) ∈ side C a p := reach_mem_orIn _ path
    simp [empty] at mem
  · have reach := reach_orReaches path j rfl len
    exact ⟨j,operandOrAndJunk ao top ha hop reach ((ao.1 _ (gateAt_mem len)).resolve_right op),yes⟩

/-- A centreless top has a permanently forced switch when all its dirty
predecessors are off. Hence the switch counting bound is strict. -/
theorem strict_bound (ao : IsAO2 n C) (top : TopForm G C)
    (existsCentre : (centreless G C).Nonempty)
    (e : Fin k → Bool → Fin n) (neg : (Fin k → Bool) → Fin n → Bool) (S : Finset ℕ)
    (under : ∀ h ∈ S, SharedSwitch.belowAnd n C (n+h))
    (contains : ∀ b i, neg b (e i (b i)) = true)
    (positive : ∀ i, ∃ h ∈ centreless G C ∪ S,
      gateVal n C h (pairInput (e i false) (e i true)) = true)
    (quiet : ∀ b h, h ∈ centreless G C ∪ S → gateVal n C h (neg b) = false) :
    k < (junk G C).card + (centreless G C).card := by
  classical
  let E := centreless G C
  let W : Set ℕ := {w | ∃ h ∈ E ∪ S, w = n+h}
  have ve : SwitchCore.valid C E := by
    intro h mem
    have data := topData (Finset.mem_filter.mp mem).1
    exact ⟨data.1,data.2.1⟩
  have scope (w : ℕ) (hw : w ∈ W) : SwitchCore.observed G C E w := by
    obtain ⟨h,hm,rfl⟩ := hw
    rcases Finset.mem_union.mp hm with he | hs
    · exact Or.inr ⟨h,he,rfl⟩
    · exact Or.inl (under h hs)
  have yes (i : Fin k) : ∃ w ∈ W, SharedSwitch.value C (pairInput (e i false) (e i true)) w = true := by
    obtain ⟨h,hm,on⟩ := positive i
    exact ⟨n+h,⟨h,hm,rfl⟩,on⟩
  have no (b) (w) (hw : w ∈ W) : SharedSwitch.value C (neg b) w = false := by
    obtain ⟨h,hm,rfl⟩ := hw
    exact quiet b h hm
  have lower := SwitchCore.matched_pairs_le_gates ao top ve e neg W scope contains yes no
  have sub := Finset.card_union_le (junk G C) E
  simp only [Fintype.card_fin] at lower
  change (junk G C ∪ E).card ≥ k at lower
  change k < (junk G C).card + E.card
  by_contra! full
  have eq : Fintype.card (Fin k) = (SwitchCore.gates G C E).card := by
    simpa only [Fintype.card_fin] using (show k = (junk G C ∪ E).card by omega)
  have different := SwitchCore.equal_budget_forces_opposite ao top ve e neg W scope contains yes no eq
  let f (b : Fin k → Bool) := SwitchCore.switches G C E (neg b)
  have inj : Function.Injective f := by
    intro b c same
    exact SwitchCore.compatible_transversals_equal ao top ve e neg W scope contains yes no
      (SwitchCore.selected_on ao ve (neg b)) (by
        change SwitchCore.compatible G C E (neg c) (f b)
        rw [same]
        exact SwitchCore.selected_on ao ve _)
  have surj : Function.Surjective f := ((Fintype.bijective_iff_injective_and_card f).mpr
    ⟨inj,by simp only [Fintype.card_fun,Fintype.card_coe]; rw [eq]⟩).2
  have allOff (b) (j) (hj : j ∈ junk G C) : gateVal n C j (neg b) = false := by
    apply Bool.eq_false_iff.mpr
    intro on
    let idx : SwitchCore.gates G C E := ⟨j,Finset.mem_union_left _ hj⟩
    have dt := junkData hj
    obtain ⟨left,right⟩ := (andValBoth ao dt.1 dt.2.1 _).mp on
    exact different b idx (left.trans right.symm)
  obtain ⟨a,ha⟩ := existsCentre
  let ix : SwitchCore.gates G C E := ⟨a,Finset.mem_union_right _ ha⟩
  have hd := topData (Finset.mem_filter.mp ha).1
  rcases (Finset.mem_filter.mp ha).2 with empty | empty
  · obtain ⟨b,code⟩ := surj (fun _ => true)
    have on : SharedSwitch.value C (neg b) (opnd C a 0) = true := congrFun code ix
    obtain ⟨j,jm,fire⟩ := empty_port_needs_dirty ao top hd.1 hd.2.1 empty _ on
    exact Bool.false_ne_true ((allOff b j jm).symm.trans fire)
  · obtain ⟨b,code⟩ := surj (fun _ => false)
    have off : SharedSwitch.value C (neg b) (opnd C a 0) = false := congrFun code ix
    have on : SharedSwitch.value C (neg b) (opnd C a 1) = true := by
      cases h : SharedSwitch.value C (neg b) (opnd C a 1) with
      | true => rfl
      | false => exact (different b ix (off.trans h.symm)).elim
    obtain ⟨j,jm,fire⟩ := empty_port_needs_dirty ao top hd.1 hd.2.1 empty _ on
    exact Bool.false_ne_true ((allOff b j jm).symm.trans fire)

#print axioms strict_bound
end CentreSwitch
