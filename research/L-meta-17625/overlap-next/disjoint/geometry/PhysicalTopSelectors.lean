import FiveRows
import PhysicalPortMasks

namespace PhysicalTopSelectors
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open DisjointProjected

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- The four physical-source flags can be chosen simultaneously on all rows. -/
theorem encode_side (ao : IsAO2 n C) (v : Fin 5 → Fin n)
    (ids : Fin 4 → ℕ) (ws : Fin 4 → Wire)
    (all : ∀ h ∈ P4Ports.active G C, ∃ k, ids k = h)
    (matched : ∀ k, ids k ∈ P4Ports.active G C → ws k = FiveRows.physical v C (n + ids k))
    (t : tops G C) (p : Fin 2) (nonempty : (PEqualNP.TopForm.side (n := n) C t p).Nonempty) :
    ∃ sel : BitVec 4,
      DisjointProjected.side (FiveRows.raw v (PEqualNP.TopForm.side (n := n) C t p)) sel
        (ws 0) (ws 1) (ws 2) (ws 3) = FiveRows.signal v C (opnd C t p) := by
  classical
  let K := PhysicalPortMasks.sources G C t p
  let m := FiveRows.raw v (PEqualNP.TopForm.side (n := n) C t p)
  let sel := PathBits.pack fun k : Fin 4 => decide (ids k ∈ K)
  have act {h} (mem : h ∈ K) : h ∈ P4Ports.active G C := (PhysicalPortMasks.source_active ao (topData t.2).1
      ⟨t,(topData t.2).1,(topData t.2).2.1,p,.refl⟩ mem).1
  have included (k : Fin 4) (r : Fin 10) : (includeOr m (sel.getLsbD k.val) (ws k)).getLsbD r.val = true ↔
      ids k ∈ K ∧ gateVal n C (ids k) (FiveRows.input v r) = true := by
    change (includeOr m ((PathBits.pack _).getLsbD k.val) (ws k)).getLsbD r.val = true ↔ _
    rw [PathBits.get_pack]
    by_cases hit : ids k ∈ K
    · obtain ⟨_,nz,_,sub⟩ := PhysicalPortMasks.source_data hit
      have raw := FiveRows.raw_sub v sub
      rw [matched k (act hit)]
      simp only [includeOr,hit,decide_true,FiveRows.physical,nz,raw,m,beq_self_eq_true,Bool.and_true,
        ite_true,true_and]
      rw [FiveRows.signal_bit,gateVal_eq_val]
    · simp [includeOr,hit]
  have source (r : Fin 10) : (∃ k : Fin 4, ids k ∈ K ∧ gateVal n C (ids k) (FiveRows.input v r) = true) ↔
      ∃ h ∈ K, gateVal n C h (FiveRows.input v r) = true := by
    constructor
    · rintro ⟨k,mem,on⟩; exact ⟨ids k,mem,on⟩
    · rintro ⟨h,mem,on⟩; obtain ⟨k,eq⟩ := all h (act mem); exact ⟨k,eq ▸ mem,eq ▸ on⟩
  refine ⟨sel,?_⟩
  apply PathBits.bit_ext
  intro r
  apply Bool.eq_iff_iff.mpr
  rw [FiveRows.signal_bit,PhysicalPortMasks.port_value (G := G) ao (topData t.2).1 p nonempty]
  change ((DisjointProjected.side m sel (ws 0) (ws 1) (ws 2) (ws 3)).getLsbD r.val = true) ↔ _
  simp only [DisjointProjected.side,BitVec.getLsbD_or,Bool.or_eq_true]
  have form (k : Fin 4) := included k r
  rw [show (literal m).getLsbD r.val = true ↔ _ from FiveRows.literal_spec v _ r]
  rw [←source r]
  constructor
  · rintro ((((lit | s₀) | s₁) | s₂) | s₃)
    · exact .inl lit
    · exact .inr ⟨0,(form 0).mp s₀⟩
    · exact .inr ⟨1,(form 1).mp s₁⟩
    · exact .inr ⟨2,(form 2).mp s₂⟩
    · exact .inr ⟨3,(form 3).mp s₃⟩
  · rintro (lit | ⟨k,hit⟩)
    · exact .inl (.inl (.inl (.inl lit)))
    · fin_cases k
      · exact .inl (.inl (.inl (.inr ((form 0).mpr hit))))
      · exact .inl (.inl (.inr ((form 1).mpr hit)))
      · exact .inl (.inr ((form 2).mpr hit))
      · exact .inr ((form 3).mpr hit)

/-- The nine selector bits of the designated tip-center top fix the same
center and leaf masks across all ten projected rows. -/
theorem inside_selectors (cross hasE : Bool) (centerSel leafSel : BitVec 4) (w x y z : Wire) :
    ∃ s : BitVec 9, centerTop cross s w x y z =
      DisjointProjected.side 4 centerSel w x y z &&&
      DisjointProjected.side (if cross && hasE then 16 else 0) leafSel w x y z := by
  let s := ((BitVec.ofBool hasE) ++ leafSel) ++ centerSel
  refine ⟨s,?_⟩
  have low : s.extractLsb' 0 4 = centerSel := by dsimp [s]; bv_decide
  have high : s.extractLsb' 4 4 = leafSel := by dsimp [s]; bv_decide
  have top : s.getLsbD 8 = hasE := by dsimp [s]; bv_decide
  simp only [centerTop,low,high,top]

/-- The twelve selector bits of one outside top pack the two sets of physical
OR sources and the common raw leaf mask. -/
theorem outside_selectors (inside : Bool) (neg : T) (tag centerSel leafSel : BitVec 4) (w x y z : Wire)
    (guard : if inside then DisjointProjected.side 0 centerSel w x y z &&& 848 = 0 else
      DisjointProjected.side 0 centerSel w x y z &&& neg = 0 ∨ rawMask tag = 4 ∨ rawMask tag = 12) :
    ∃ s : BitVec 12, outsideTop inside neg s w x y z =
      DisjointProjected.side 0 centerSel w x y z &&& DisjointProjected.side (rawMask tag) leafSel w x y z := by
  let s := (tag ++ leafSel) ++ centerSel
  refine ⟨s,?_⟩
  have low : s.extractLsb' 0 4 = centerSel := by dsimp [s]; bv_decide
  have mid : s.extractLsb' 4 4 = leafSel := by dsimp [s]; bv_decide
  have high : s.extractLsb' 8 4 = tag := by dsimp [s]; bv_decide
  cases hi : inside <;> simp_all [outsideTop,or_assoc]

#print axioms encode_side
#print axioms inside_selectors
#print axioms outside_selectors
end PhysicalTopSelectors
