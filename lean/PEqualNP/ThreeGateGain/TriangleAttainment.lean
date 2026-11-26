import PEqualNP.ThreeGateGain.TriangleRectangle
import PEqualNP.ThreeGateGain.TriangleLeafFormula
import PEqualNP.ThreeGateGain.TwoIntersections

namespace TriangleOptimality
open Finset Configuration TriangleLeafFormula

private theorem select {α : Type*} [Fintype α] [DecidableEq α] (S : Finset α) (f : α → ℤ) :
    (∑ x : α, if x ∈ S then f x else 0) = ∑ x ∈ S, f x := by
  rw [← Finset.sum_filter]
  simp

private theorem pull {α : Type*} [Fintype α] (c : Prop) [Decidable c] (f : α → ℤ) :
    (∑ x : α, if c then f x else 0) = if c then ∑ x : α, f x else 0 := by
  by_cases h : c <;> simp [h]

variable {P L : Type*} [Membership P L] [ProjectivePlane P L] [Fintype P] [Fintype L]

/-- Count both wrong answers with unit cost, on a prediction specified by its zero set. -/
noncomputable def errors (I : P → L → Prop) (zeros : Set (P × L)) : ℤ :=
  ∑ p : P, ∑ l : L, hit (fun p l => ¬ ((p,l) ∉ zeros ↔ I p l)) p l

theorem row_total (p : P) : (∑ l : L, hit (fun p l => p ∈ l) p l) =
    (ProjectivePlane.order P L : ℤ)+1 := by
  have h := PlaneCenterSupports.sum_flag (P:=P) (L:=L) p
  exact_mod_cast (show (∑ l : L, hit (fun p l => p ∈ l) p l) =
    ((ProjectivePlane.order P L+1 : ℕ) : ℤ) by
      rw [← h, Nat.cast_sum]; apply sum_congr rfl; intro l _
      classical
      by_cases e : p∈l <;> simp [hit,PlaneCenterSupports.flag,e])

theorem col_total (l : L) : (∑ p : P, hit (fun p l => p ∈ l) p l) =
    (ProjectivePlane.order P L : ℤ)+1 := by
  classical
  have h := ProjectivePlane.pointCount_eq P l
  rw [pointCount, Nat.card_eq_fintype_card, Fintype.card_of_subtype
    (univ.filter (fun p : P => p ∈ l)) (by simp)] at h
  simp [hit, Finset.sum_boole, h]

/-- Splitting the accepted flags into selected rows and columns, subtracting their overlap. -/
private theorem centered_count (X : Finset P) (Y : Finset L)
    (z : Set (P×L)) (hz : ∀ p l, (p,l) ∉ z ↔ p ∈ l ∧ (p ∈ X ∨ l ∈ Y)) :
    errors (fun p l => p ∈ l) z =
      (Fintype.card P - (X.card : ℤ) - Y.card) * (ProjectivePlane.order P L + (1:ℤ))
        + edges (fun p l => p ∈ l) X Y := by
  classical
  let I (p : P) (l : L) := hit (fun p l => p ∈ l) p l
  have cell (p : P) (l : L) : hit (fun p l => ¬ ((p,l) ∉ z ↔ p ∈ l)) p l =
      I p l - (if p ∈ X then I p l else 0) - (if l ∈ Y then I p l else 0)
        + (if p ∈ X then (if l ∈ Y then I p l else 0) else 0) := by
    simp only [hit,I,hz]
    by_cases a : p∈l <;> by_cases b : p∈X <;> by_cases c : l∈Y <;> simp [a,b,c]
  have row (p : P) : ∑ l : L, I p l = (ProjectivePlane.order P L:ℤ)+1 := row_total p
  have col (l : L) : ∑ p : P, I p l = (ProjectivePlane.order P L:ℤ)+1 := col_total l
  unfold errors
  simp_rw [cell]
  simp only [sum_add_distrib,sum_sub_distrib]
  have r : (∑ p : P, ∑ l : L, if p ∈ X then I p l else 0) =
      (X.card : ℤ) * (ProjectivePlane.order P L+1) := by
    simp_rw [pull,select,row]
    simp
  have c : (∑ p : P, ∑ l : L, if l ∈ Y then I p l else 0) =
      (Y.card : ℤ) * (ProjectivePlane.order P L+1) := by
    rw [sum_comm]; simp_rw [pull,select,col]; simp
  have xy : (∑ p : P, ∑ l : L, if p ∈ X then (if l∈Y then I p l else 0) else 0) =
      edges (fun p l => p∈l) X Y := by
    simp_rw [pull,select]; rfl
  rw [r,c,xy]; simp_rw [row]; simp; ring

def triangleZeros {o : P} {h : L} (w : Wedge o h) : Set (P × L) :=
  {x | ¬ (Formula.meet (clause o h) w.arms).eval x.1 x.2}

omit [ProjectivePlane P L] [Fintype P] [Fintype L] in
/-- The upper witness uses the very same two-paid-gate predicate as the atlas. -/
theorem atlas_triangle {o : P} {h : L} (w : Wedge o h) :
    TwoIntersections.Two TwoIntersections.Rectangle (triangleZeros w) := by
  apply (TwoIntersections.rectangle_normal_iff _).mpr
  left
  let R (p : P) (l : L) : Set (P×L) := ({x : P | x ∉ l} : Set P) ×ˢ {j : L | p ∉ j}
  have rect (p : P) (l : L) : TwoIntersections.Rectangle (R p l) := ⟨_,_,rfl⟩
  refine ⟨R o h,R w.a w.v,R w.b w.u,rect ..,rect ..,rect ..,?_⟩
  ext x
  change ¬ ((x.1∈h ∨ o∈x.2) ∧ (x.1∈w.v ∨ w.a∈x.2) ∧ (x.1∈w.u ∨ w.b∈x.2)) ↔
    ((x.1∉h ∧ o∉x.2) ∨ (x.1∉w.v ∧ w.a∉x.2)) ∨ (x.1∉w.u ∧ w.b∉x.2)
  tauto

theorem triangle_errors {o : P} {h : L} (away : o ∉ h) (w : Wedge o h) :
    errors (fun (p:P) (l:L) => p ∈ l) (triangleZeros w) =
      ((ProjectivePlane.order P L : ℤ)^2 + ProjectivePlane.order P L + 1) *
        (ProjectivePlane.order P L + 1) - 6*ProjectivePlane.order P L := by
  classical
  have uh : w.u ≠ h := fun eq => away (eq ▸ w.ou)
  have vh : w.v ≠ h := fun eq => away (eq ▸ w.ov)
  have av : w.a ∉ w.v := fun a =>
    vh ((Nondegenerate.eq_or_eq w.ah w.bh a w.bv).resolve_left w.ab).symm
  have bu : w.b ∉ w.u := fun b =>
    uh ((Nondegenerate.eq_or_eq w.ah w.bh w.au b).resolve_left w.ab).symm
  have uv : w.u ≠ w.v := fun eq => av (eq ▸ w.au)
  have oa : o ≠ w.a := fun eq => away (eq.symm ▸ w.ah)
  have ob : o ≠ w.b := fun eq => away (eq.symm ▸ w.bh)
  let X : Finset P := {o,w.a,w.b}
  let Y : Finset L := {h,w.u,w.v}
  have e := centered_count X Y (triangleZeros w) (fun p l => by
    change (¬ ¬ _) ↔ _
    rw [not_not, TriangleLeafFormula.triangle away w]
    simp [Wedge.center,X,Y, or_assoc])
  have xy : edges (fun (p:P) (l:L) => p∈l) X Y = 6 := by
    simp [edges,X,Y,oa,ob,w.ab,uh.symm,vh.symm,uv]
    simp [hit,away,w.ah,w.bh,w.ou,w.ov,w.au,w.bv,av,bu]
  rw [e,xy,ProjectivePlane.card_points P L]
  simp [X,Y,oa,ob,w.ab,uh.symm,vh.symm,uv]; ring

theorem exists_triangle_attaining :
    ∃ z : Set (P×L), TwoIntersections.Two TwoIntersections.Rectangle z ∧
      errors (fun (p:P) (l:L) => p∈l) z =
        ((ProjectivePlane.order P L : ℤ)^2 + ProjectivePlane.order P L + 1) *
          (ProjectivePlane.order P L+1) - 6*ProjectivePlane.order P L := by
  obtain ⟨o,a,b,_,h,_,away,_,_,ah,a',_,bh,b'⟩ := @ProjectivePlane.exists_config P L _ _
  have ab : a ≠ b := fun eq => b' (eq ▸ a')
  have oa : o ≠ a := fun eq => away (eq.symm ▸ ah)
  have ob : o ≠ b := fun eq => away (eq.symm ▸ bh)
  obtain ⟨u,⟨ou,au⟩,_⟩ := HasLines.existsUnique_line P L o a oa
  obtain ⟨v,⟨ov,bv⟩,_⟩ := HasLines.existsUnique_line P L o b ob
  let w : Wedge o h := ⟨a,b,u,v,ab,ah,bh,ou,au,ov,bv⟩
  exact ⟨_,atlas_triangle w,triangle_errors away w⟩

#print axioms exists_triangle_attaining
end TriangleOptimality
