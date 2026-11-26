import PhysicalPortMasks
import ProjectedSchedule
import PathPhysical

namespace PhysicalSchedule
open DisjointProjected
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
attribute [local instance] gateOpDecEq

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

structure Projection (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) where
  rows : Fin 10 → Fin n → Bool
  mask : Finset (Fin n) → R
  literal_spec : ∀ s (i : Fin 10), (literal (mask s)).getLsbD i = true ↔ ∃ u ∈ s, rows i u = true
  raw_sub : ∀ {s t}, s ⊆ t → mask s &&& ~~~(mask t) = 0
  raw_union : ∀ s t, mask (s ∪ t) = mask s ||| mask t
  raw_empty : mask ∅ = 0
  tag_lit : ∀ u, ∃ tag, rawMask tag = mask {u}
  tag_lam : ∀ k ∈ lam G C, ∃ tag, rawMask tag = mask (orIn n C (n+k))

def Projection.physical (p : Projection G C) (w : ℕ) : Wire :=
  ⟨PathBits.pack (fun i => val C (List.ofFn (p.rows i)) w), p.mask (orIn n C w), decide (orIn n C w).Nonempty⟩

theorem Projection.gate_eq (p : Projection G C) (ao : IsAO2 n C) {g : ℕ}
    (len : g < C.gates.length) :
    p.physical (n+g) = gate (PathPhysical.kind C g)
      (p.physical (opnd C g 0)) (p.physical (opnd C g 1)) := by
  rcases ao.1 _ (gateAt_mem len) with op|op
  · have kind : PathPhysical.kind C g = false := by simp [PathPhysical.kind,op]
    have raw := andRawEmpty (n := n) op
    have sig : (p.physical (n+g)).val = (p.physical (opnd C g 0)).val &&&
        (p.physical (opnd C g 1)).val := by
      apply PathBits.bit_ext; intro i
      apply Bool.eq_iff_iff.mpr
      simp only [physical,BitVec.getLsbD_and,PathBits.get_pack,Bool.and_eq_true]
      exact andValBoth ao len op _
    rw [kind]
    change Wire.mk _ _ _ = Wire.mk _ _ _
    congr 1
    · rw [raw,p.raw_empty]
    · simp [raw]
  · have kind : PathPhysical.kind C g = true := by simp [PathPhysical.kind,op]
    have raw := orRawUnion ao len op
    have sig : (p.physical (n+g)).val = (p.physical (opnd C g 0)).val |||
        (p.physical (opnd C g 1)).val := by
      apply PathBits.bit_ext; intro i
      apply Bool.eq_iff_iff.mpr
      simp only [physical,BitVec.getLsbD_or,PathBits.get_pack,Bool.or_eq_true]
      exact PathPhysical.or_value ao len op _
    rw [kind]
    change Wire.mk _ _ _ = Wire.mk _ _ _
    congr 1
    · rw [raw,p.raw_union]; rfl
    · simp [physical,raw,Finset.union_nonempty,PEqualNP.TopForm.side]

/-- Three predecessor positions, with zero in every unused position. -/
def previous (ws : Fin 4 → Wire) (k : Fin 4) (j : Fin 3) : Wire :=
  if j.castSucc < k then ws j.castSucc else zero

def baseSel (tag : BitVec 4) (a b c : Bool) : P :=
  (BitVec.ofBool false ++ BitVec.ofBool c ++ BitVec.ofBool b ++ BitVec.ofBool a) ++ tag

theorem baseSel_eq (tag : BitVec 4) (a b c : Bool) (x y z : Wire) :
    port (baseSel tag a b c) x y z =
      ⟨literal (rawMask tag) ||| includeOr (rawMask tag) a x ||| includeOr (rawMask tag) b y |||
        includeOr (rawMask tag) c z,rawMask tag,true⟩ := by
  have fields : ∀ (tag : BitVec 4) (a b c : Bool),
      (baseSel tag a b c).extractLsb' 0 4 = tag ∧
      (baseSel tag a b c).getLsbD 7 = false ∧ (baseSel tag a b c).getLsbD 4 = a ∧
      (baseSel tag a b c).getLsbD 5 = b ∧ (baseSel tag a b c).getLsbD 6 = c := by decide
  obtain ⟨f,h,l,m,r⟩ := fields tag a b c
  unfold port
  dsimp only
  rw [f,h,l,m,r]
  rfl

theorem directSel (x : Fin 3 → Wire) (i : Fin 3) : ∃ p, port p (x 0) (x 1) (x 2) = x i := by
  fin_cases i
  · exact ⟨129,by rfl⟩
  · exact ⟨130,by rfl⟩
  · exact ⟨128,by rfl⟩

theorem merge_spec (m : R) (s : Fin 3 → Bool) (x : Fin 3 → Wire) (i : Fin 10)
    (elig : ∀ j, s j = true → (x j).nz = true ∧ (x j).raw &&& ~~~m = 0) :
    (literal m ||| includeOr m (s 0) (x 0) ||| includeOr m (s 1) (x 1) |||
      includeOr m (s 2) (x 2)).getLsbD i = true ↔
      (literal m).getLsbD i = true ∨ ∃ j, s j = true ∧ (x j).val.getLsbD i = true := by
  have part (j : Fin 3) :
      (includeOr m (s j) (x j)).getLsbD i = true ↔ s j = true ∧ (x j).val.getLsbD i = true := by
    cases h : s j with
    | false => simp [includeOr]
    | true => simp [includeOr,(elig _ h).1,(elig _ h).2]
  simp only [BitVec.getLsbD_or,Bool.or_eq_true,part,Fin.exists_fin_succ,Fin.exists_fin_zero,or_false]
  tauto

end PhysicalSchedule
