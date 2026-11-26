import PEqualNP.Atlas56.Semantics

namespace Atlas56
open Set TwoIntersections ThreeIntersectionsFormula

theorem cube_models {z : Set Cell} (h : cube z) :
    ThreeIntersections.Three Rectangle z ∧ Formula Rectangle 3 z := by
  obtain ⟨a,b,c,d,e,f,ha,hb,hc,hd,he,hf,rfl⟩ := h
  constructor
  · exact (ThreeIntersections.rectangle_normal_iff _).mpr
      (Or.inr (Or.inr (Or.inl ⟨a,b,c,d,e,f,ha,hb,hc,hd,he,hf,rfl⟩)))
  · exact .meet (.meet (.join (.base ha) (.base hb)) (.join (.base hc) (.base hd)))
      (.join (.base he) (.base hf))

theorem formula_preimage (r : Row → Row) (c : Col → Col) {n : Nat} {z : Set Cell}
    (h : Formula Rectangle n z) :
    Formula Rectangle n ((fun p : Cell => (r p.1,c p.2)) ⁻¹' z) := by
  induction h with
  | base hr =>
    rcases hr with ⟨a,b,rfl⟩
    exact .base ⟨r ⁻¹' a,c ⁻¹' b,rfl⟩
  | meet _ _ ih jh => exact .meet ih jh
  | join _ _ ih jh => exact .join ih jh

theorem orbit_lower {z : Set Cell} (q : orbit z) :
    (¬ ThreeIntersections.Three Rectangle z) ∧ (∀ n, Formula Rectangle n z → 4 ≤ n) := by
  obtain ⟨r,c,hz⟩ := q
  have back : (fun p : Cell => (r.symm p.1,c.symm p.2)) ⁻¹' z = ThreeIntersectionsQuadrangle.zero := by
    ext ⟨i,j⟩
    rw [hz]
    change (r (r.symm i), c (c.symm j)) ∈ ThreeIntersectionsQuadrangle.zero ↔ (i,j) ∈ ThreeIntersectionsQuadrangle.zero
    simp
  constructor
  · intro h
    have t := ThreeIntersections.rectangle_normal_preimage r.symm c.symm
      ((ThreeIntersections.rectangle_normal_iff _).mp h)
    rw [back] at t
    exact QuadrangleStructural.no_normal t
  · intro n h
    have t := formula_preimage r.symm c.symm h
    rw [back] at t
    exact QuadrangleStructural.formula_lower_bound t

-- The row-by-row formula applies to all five-row matrices.
theorem formula_four (z : Set Cell) : Formula Rectangle 4 z := by
  let row (i : Row) : Set Cell := {i} ×ˢ {j | (i,j) ∈ z}
  have h (i : Row) : Rectangle (row i) := ⟨_,_,rfl⟩
  have hz : z = (((row 0 ∪ row 1) ∪ row 2) ∪ row 3) ∪ row 4 := by
    ext ⟨i,j⟩
    fin_cases i <;> simp [row]
  rw [hz]
  exact .join (.join (.join (.join (.base (h 0)) (.base (h 1))) (.base (h 2))) (.base (h 3))) (.base (h 4))

theorem classify (cover : ∀ z, cube z ∨ orbit z) (z : Set Cell) :
    (orbit z ↔ ¬ ThreeIntersections.Three Rectangle z) ∧
    (orbit z ↔ ¬ ∃ n < 4, Formula Rectangle n z) ∧
    (¬ orbit z → cube z) ∧ Formula Rectangle 4 z := by
  have h := cover z
  exact ⟨⟨fun q => (orbit_lower q).1,fun no => h.resolve_left (fun t => no (cube_models t).1)⟩,
    ⟨fun q ⟨n,lt,hn⟩ => (Nat.not_le_of_gt lt) ((orbit_lower q).2 n hn),
     fun no => h.resolve_left (fun t => no ⟨3,by decide,(cube_models t).2⟩)⟩,
    fun no => h.resolve_right no, formula_four z⟩

end Atlas56
