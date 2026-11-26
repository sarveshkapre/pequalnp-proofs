import PEqualNP.FiveRows.ThresholdProof
import PEqualNP.FiveRows.Partition

namespace FiveRowDistinct
open Set TwoIntersections ThreeIntersectionsFormula FiveRowThreshold

def Distinct {n} (z : Region n) : Prop :=
  Function.Injective (fun j : Fin n => {i : Fin 5 | (i,j) ∈ z})

def DistinctGap (n : Nat) : Prop :=
  ∃ z : Region n, Distinct z ∧ ThreeIntersections.Three Rectangle z ∧ ¬ Two Rectangle z ∧
    Formula Rectangle 4 z ∧ ∀ k, k < 4 → ¬ Formula Rectangle k z

private def masks22 : Fin 5 → BitVec 22 := ![2962218,3627545,3775570,4071267,4186236]
private def z22 : Region 22 := {p | (masks22 p.1).getLsbD p.2.val = true}
private def cs22 : Fin 6 → BitVec 22 := ![3635769,3775574,4071267,4186236,2962222,4185691]
private def box (k : Fin 6) : Region 22 :=
  {r | (FiveRowSharing.rowSides k).getLsbD r.val = true} ×ˢ
  {c | (cs22 k).getLsbD c.val = true}
private theorem rect_box (k : Fin 6) : Rectangle (box k) := ⟨_,_,rfl⟩
private theorem construction : z22 = (box 2 ∪ (box 3 ∩ (box 0 ∪ box 1))) ∩
    (box 4 ∪ (box 5 ∩ (box 0 ∪ box 1))) := by
  ext p
  revert p
  unfold z22 masks22 box FiveRowSharing.rowSides cs22
  decide +kernel

private theorem circ22 : ThreeIntersections.Three Rectangle z22 := by
  apply (ThreeIntersections.rectangle_normal_iff _).mpr
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_,_,_,_,_,_,rect_box 0,rect_box 1,
    rect_box 2,rect_box 3,rect_box 4,rect_box 5,construction⟩)))

private theorem tree22 : Formula Rectangle 4 z22 := by
  rw [construction]
  exact diamond_four_formula (rect_box 0) (rect_box 1) (rect_box 2) (rect_box 3) (rect_box 4) (rect_box 5)

private theorem distinct22 : Distinct z22 := by
  have sep : ∀ x y : Fin 22, x ≠ y → ∃ r : Fin 5,
    (masks22 r).getLsbD x.val ≠ (masks22 r).getLsbD y.val := by decide +kernel
  intro x y eq
  by_contra ne
  obtain ⟨r,hr⟩ := sep x y ne
  apply hr
  exact Bool.eq_iff_iff.mpr (Set.ext_iff.mp eq r)

private theorem first_seven : pull (Fin.castLE (by decide : 7 ≤ 22)) z22 = FiveRowSharing.zero := by
  ext p
  revert p
  change ∀ p : Fin 5 × Fin 7, (masks22 p.1).getLsbD p.2.val = true ↔
    (FiveSevenCheck.masks p.1).getLsbD p.2.val = true
  decide +kernel

theorem intermediate (n : Nat) (lo : 7 ≤ n) (hi : n ≤ 22) : DistinctGap n := by
  let z := pull (Fin.castLE hi) z22
  have same : pull (Fin.castLE lo) z = FiveRowSharing.zero := first_seven
  have lower (k : Nat) (lt : k < 4) : ¬ Formula Rectangle k z := by
    intro hz
    have h := pull_formula (Fin.castLE lo) hz
    rw [same] at h
    exact FiveRowSharing.formula_lower lt h
  have distinct : Distinct z := by
    intro x y h
    have eq : Fin.castLE hi x = Fin.castLE hi y := distinct22 h
    exact Fin.ext (congrArg (fun q : Fin 22 => q.val) eq)
  exact ⟨z, distinct, pull_three _ circ22, fun two => lower 2 (by decide) (two_formula two),
    pull_formula _ tree22, lower⟩

theorem uses_shared {n} {z : Region n} (circ : ThreeIntersections.Three Rectangle z)
    (lower : ¬ Formula Rectangle 3 z) (different : Distinct z) :
    ∃ (rows : Fin 5 → FiveRowPartition.Code) (cols : Fin n → FiveRowPartition.Code),
      ∀ i j, (∀ r, FiveRowPartition.shared (rows r &&& cols i) =
        FiveRowPartition.shared (rows r &&& cols j)) → i = j := by
  classical
  have no4 (h : ThreeIntersectionsSharingGap.FirstFour Rectangle z) := lower (first_four_formula h)
  rcases (ThreeIntersections.rectangle_normal_iff _).mp circ with a | b | c | d | h
  · exact False.elim (no4 (Or.inl a))
  · exact False.elim (no4 (Or.inr (Or.inl b)))
  · exact False.elim (no4 (Or.inr (Or.inr (Or.inl c))))
  · exact False.elim (no4 (Or.inr (Or.inr (Or.inr d))))
  obtain ⟨a,b,c,d,e,f,ha,hb,hc,hd,he,hf,hz⟩ := h
  obtain ⟨ra,ca,rfl⟩ := ha
  obtain ⟨rb,cb,rfl⟩ := hb
  obtain ⟨rc,cc,rfl⟩ := hc
  obtain ⟨rd,cd,rfl⟩ := hd
  obtain ⟨re,ce,rfl⟩ := he
  obtain ⟨rf,cf,rfl⟩ := hf
  let R (i : Fin 5) : FiveRowPartition.Code := BitVec.ofBoolListLE
    [decide (i ∈ ra),decide (i ∈ rb),decide (i ∈ rc),decide (i ∈ rd),decide (i ∈ re),decide (i ∈ rf)]
  let C (i : Fin n) : FiveRowPartition.Code := BitVec.ofBoolListLE
    [decide (i ∈ ca),decide (i ∈ cb),decide (i ∈ cc),decide (i ∈ cd),decide (i ∈ ce),decide (i ∈ cf)]
  have cells (i : Fin 5) (j : Fin n) :
      FiveRowPartition.shared (R i &&& C j) = true ↔ (i,j) ∈ z := by
    rw [hz]
    simp only [R,C,FiveRowPartition.shared,BitVec.getLsbD_and,BitVec.getLsbD_ofBoolListLE]
    simp [List.getD]
  refine ⟨R,C,?_⟩
  intro x y h
  apply different
  ext i
  change (i,x) ∈ z ↔ (i,y) ∈ z
  rw [← cells,← cells,h i]
end FiveRowDistinct
