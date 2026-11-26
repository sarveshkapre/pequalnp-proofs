import CentreSwitch

namespace ThreeStates
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_7465_aux
open PEqualNP.Outside.L_meta_7465_aux.Routing

variable {n k : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- At most three states per dirty AND suffice even if there are arbitrarily
many centreless tops. -/
theorem capacity (ao : IsAO2 n C) (top : TopForm G C)
    (e : Fin k → Bool → Fin n) (neg : (Fin k → Bool) → Fin n → Bool) (S : Finset ℕ)
    (under : ∀ h ∈ S, SharedSwitch.belowAnd n C (n+h))
    (contains : ∀ b i, neg b (e i (b i)) = true)
    (positive : ∀ i, ∃ h ∈ centreless G C ∪ S,
      gateVal n C h (pairInput (e i false) (e i true)) = true)
    (quiet : ∀ b h, h ∈ centreless G C ∪ S → gateVal n C h (neg b) = false) :
    2^k ≤ 3^(junk G C).card := by
  classical
  let E : Finset ℕ := ∅
  have ve : SwitchCore.valid C E := by simp [E,SwitchCore.valid]
  let D := SwitchCore.gates G C E
  let tag (x : Fin n → Bool) (j : D) : Option Bool :=
    if gateVal n C j x = true then none else some (SwitchCore.switches G C E x j)
  have decode (x : Fin n → Bool) (j : D) : (tag x j).getD true = SwitchCore.switches G C E x j := by
    by_cases on : gateVal n C j x = true
    · have hd := SwitchCore.gate_data ve j
      have first := ((andValBoth ao hd.1 hd.2 x).mp on).1
      simp [tag,on,SwitchCore.switches]
      exact first
    · simp [tag,on]
  let f (b : Fin k → Bool) := tag (neg b)
  have inj : Function.Injective f := by
    intro b c same
    have comp : SwitchCore.switches G C E (neg b) = SwitchCore.switches G C E (neg c) := by
      funext j
      exact (decode _ j).symm.trans ((congrArg (fun v : Option Bool => v.getD true) (congrFun same j)).trans (decode _ j))
    have agree (j : D) : gateVal n C j (neg b) = gateVal n C j (neg c) := by
      have tr := congrFun same j
      change tag (neg b) j = tag (neg c) j at tr
      cases l : gateVal n C j (neg b) <;> cases r : gateVal n C j (neg c) <;> simp_all [tag]
    funext i
    by_contra diff
    let x := pairInput (e i false) (e i true)
    have sub (v) (on : x v = true) : neg b v = true ∨ neg c v = true := by
      have two := (pairInput_true _ _ _).mp on
      have hb := contains b i
      have hc := contains c i
      rcases two with rfl | rfl <;> cases hbi : b i <;> cases hci : c i <;> simp_all
    have promotes {w : ℕ} (scope : SharedSwitch.belowAnd n C w)
        (on : SharedSwitch.value C x w = true) :
        SharedSwitch.value C (neg b) w = true ∨ SharedSwitch.value C (neg c) w = true :=
      SwitchCore.union_compatible ao top ve sub (SwitchCore.selected_on ao ve (neg b))
        (by rw [comp]; exact SwitchCore.selected_on ao ve _) w (Or.inl scope) on
    obtain ⟨a,ha,hit⟩ := positive i
    have contradiction (side : gateVal n C a (neg b) = true ∨ gateVal n C a (neg c) = true) :
        False := side.elim (fun h => Bool.false_ne_true ((quiet b a ha).symm.trans h))
                            (fun h => Bool.false_ne_true ((quiet c a ha).symm.trans h))
    apply contradiction
    rcases Finset.mem_union.mp ha with root | regular
    · have data := topData (Finset.mem_filter.mp root).1
      have pick : ∃ p : Fin 2, side (n := n) C a p = ∅ := by
        rcases (Finset.mem_filter.mp root).2 with h | h
        · exact ⟨0,h⟩
        · exact ⟨1,h⟩
      obtain ⟨p,empty⟩ := pick
      let o : Fin 2 := 1-p
      have allOn := (andValOperands ao data.1 data.2.1 x).mp hit
      obtain ⟨w,path,on,raw | ⟨j,jlen,rfl,jn⟩⟩ :=
        or_trace (n := n) (C := C) (x := List.ofFn x) (by simp) _ (allOn p)
      · have m : (⟨w,raw⟩ : Fin n) ∈ side C a p := reach_mem_orIn _ path
        simp [empty] at m
      · have jdirty := operandOrAndJunk ao top data.1 data.2.1 (reach_orReaches path j rfl jlen)
            ((ao.1 _ (gateAt_mem jlen)).resolve_right jn)
        let jx : D := ⟨j, Finset.mem_union_left _ jdirty⟩
        have sameGate := agree jx
        have seen := promotes ⟨a,data.1,data.2.1,p,path⟩ on
        have both : gateVal n C j (neg b) = true ∧ gateVal n C j (neg c) = true := by
          rcases seen with l | r
          · exact ⟨l,sameGate.symm.trans l⟩
          · exact ⟨sameGate.trans r,r⟩
        have make (t : Fin n → Bool) (jOn : gateVal n C j t = true)
            (other : SharedSwitch.value C t (opnd C a o) = true) : gateVal n C a t = true := by
          apply (andValOperands ao data.1 data.2.1 _).mpr
          intro q
          rcases (show q = p ∨ q = o by fin_cases p <;> fin_cases q <;> decide) with rfl | rfl
          · exact orStep_up (n := n) (by simp) path jOn
          · exact other
        have branch := promotes ⟨a,data.1,data.2.1,o,.refl⟩ (allOn o)
        exact branch.imp (make _ both.1) (make _ both.2)
    · exact promotes (under a regular) hit
  have card := Fintype.card_le_of_injective f inj
  simpa [f,D,SwitchCore.gates,E] using card

#print axioms capacity
end ThreeStates
