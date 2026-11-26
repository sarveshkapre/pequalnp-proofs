import PathPhysical
import P4PortLift

/-! Encoding a real circuit prefix in the four-gate search. -/
namespace PathSchedule
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open PathBits PathSearch PathPhysical
attribute [local instance] gateOpDecEq
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {e : Fin 4 → Fin n}

private theorem base_fields : ∀ m : BitVec 4, m ∈ ([0,1,2,4,8] : List (BitVec 4)) →
    (⟨literal m,m,true⟩ : Wire) ∈ single ∧ thin m = true := by decide

theorem available (W : PathGeometry.Witness G C e) (einj : Function.Injective e)
    (ao : IsAO2 n C) (top : TopForm G C) {j : ℕ} (ac : j ∈ P4Ports.active G C) (i : Fin 2) :
    wire e C (opnd C j i) ∈ ports ((activePrefix G C j).map (gate e C)) := by
  classical
  rcases P4Ports.port_law ao top _ (fun _ h => thin_lam W h) ac i with ⟨k,ka,lt,eq⟩|⟨global,little,K,keys,sem⟩
  · rw [eq]
    exact P4PortLift.direct_port _ _ (mem_prefix.mpr ⟨lt,ka⟩)
  let R := side (n := n) C j i
  let mask := raw e R
  let base : Wire := ⟨literal mask,mask,true⟩
  let keep (k : ℕ) := decide (k ∈ K)
  have info := base_fields mask (thin_mask einj R little)
  have elig (k : ℕ) (_hk : k ∈ activePrefix G C j) (kept : keep k = true) :
      (gate e C k).1 = true ∧ (gate e C k).2.nz = true ∧ base.raw ||| (gate e C k).2.raw = base.raw := by
    obtain ⟨_,_,hor,nz,sub⟩ := keys k (of_decide_eq_true kept)
    exact ⟨decide_eq_true (orData hor).2.1,decide_eq_true nz,raw_sub sub⟩
  have avail := P4PortLift.selected_port (activePrefix G C j) (gate e C) keep base info.1 rfl info.2 elig
  have eq : signal e C (opnd C j i) =
      literal mask ||| P4PortLift.selectedValue (activePrefix G C j) (gate e C) keep := by
    apply bit_ext; intro row
    apply Bool.eq_iff_iff.mpr
    simp only [signal,get_pack,BitVec.getLsbD_or,Bool.or_eq_true,P4PortLift.selected_bit]
    rw [literal_spec,sem]
    constructor
    · rintro (h|⟨k,h,on⟩)
      · exact Or.inl h
      · have hk := keys k h
        exact Or.inr ⟨k, mem_prefix.mpr ⟨hk.2.1,hk.1⟩,decide_eq_true h,by
          change (signal e C (n+k)).getLsbD row = true
          simpa only [signal,get_pack,gateVal_eq_val] using on⟩
    · rintro (h|⟨k,_,h,on⟩)
      · exact Or.inl h
      · refine Or.inr ⟨k,of_decide_eq_true h,?_⟩
        change (signal e C (n+k)).getLsbD row = true at on
        simpa only [signal,get_pack,gateVal_eq_val] using on
  change Wire.mk _ _ _ ∈ _
  rw [eq, show decide (orIn n C (opnd C j i)).Nonempty = true from decide_eq_true global]
  exact avail

theorem valid (W : PathGeometry.Witness G C e) (einj : Function.Injective e)
    (ao : IsAO2 n C) (top : TopForm G C) (j : ℕ) :
    Valid ((activePrefix G C j).map (gate e C)) := by
  classical
  induction j with
  | zero => exact .nil
  | succ j ih =>
    have step : activePrefix G C (j+1) = activePrefix G C j ++ (if j ∈ P4Ports.active G C then [j] else []) := by
      by_cases mem : j ∈ P4Ports.active G C <;> simp [activePrefix,List.range_succ,mem]
    rw [step,List.map_append]
    split
    next ac =>
      simp only [List.map_cons,List.map_nil,gate_eq e ao (P4Ports.active_length ac)]
      exact .snoc ih _ _ _ (available W einj ao top ac 0) (available W einj ao top ac 1)
    next => simpa using ih

end PathSchedule
