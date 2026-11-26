import SixEdgePlane

namespace SixEdge.Plane

open PlaneFour ResidualDegree PEqualNP.MetaComplexity.NestedCover

/-- A relabelling that keeps the point and line sides of the plane. -/
structure Relabelling where
  point : Fin 13 → Fin 13
  line : Fin 13 → Fin 13
  pointInjective : Function.Injective point
  lineInjective : Function.Injective line
  incidence : ∀ p l, incident (point p) (line l) ↔ incident p l

def relabelId : Relabelling where
  point := id
  line := id
  pointInjective := fun _ _ h => h
  lineInjective := fun _ _ h => h
  incidence := fun _ _ => Iff.rfl

def Relabelling.then (a b : Relabelling) : Relabelling where
  point p := b.point (a.point p)
  line l := b.line (a.line l)
  pointInjective := b.pointInjective.comp a.pointInjective
  lineInjective := b.lineInjective.comp a.lineInjective
  incidence p l := (b.incidence _ _).trans (a.incidence p l)

noncomputable def Relabelling.inverse (r : Relabelling) : Relabelling := by
  let p := Equiv.ofBijective r.point
    ⟨r.pointInjective, Finite.surjective_of_injective r.pointInjective⟩
  let l := Equiv.ofBijective r.line
    ⟨r.lineInjective, Finite.surjective_of_injective r.lineInjective⟩
  exact ⟨p.symm, l.symm, p.symm.injective, l.symm.injective, fun u v => by
    have preserve := r.incidence (p.symm u) (l.symm v)
    change incident (p (p.symm u)) (l (l.symm v)) ↔ _ at preserve
    simpa using preserve.symm⟩

theorem point_inverse (r : Relabelling) (p : Fin 13) : r.inverse.point (r.point p) = p := by
  exact (Equiv.ofBijective r.point
    ⟨r.pointInjective, Finite.surjective_of_injective r.pointInjective⟩).symm_apply_apply p

theorem line_inverse (r : Relabelling) (l : Fin 13) : r.inverse.line (r.line l) = l := by
  exact (Equiv.ofBijective r.line
    ⟨r.lineInjective, Finite.surjective_of_injective r.lineInjective⟩).symm_apply_apply l

private theorem translation_incident :
    ∀ p l d : Fin 13, incident (p+d) (l+d) ↔ incident p l := by decide

def translate (d : Fin 13) : Relabelling where
  point p := p+d
  line l := l+d
  pointInjective := fun _ _ h => add_right_cancel h
  lineInjective := fun _ _ h => add_right_cancel h
  incidence p l := translation_incident p l d

private def genA : Relabelling where
  point := ![1,0,4,3,5,6,11,8,10,9,7,12,2]
  line := ![0,4,3,2,5,10,8,7,9,6,11,12,1]
  pointInjective := by decide
  lineInjective := by decide
  incidence := by decide

private def genB : Relabelling where
  point := ![3,1,2,9,4,6,8,12,5,0,10,7,11]
  line := ![0,1,6,8,3,5,12,9,4,10,7,11,2]
  pointInjective := by decide
  lineInjective := by decide
  incidence := by decide

private def composition (steps : List Bool) : Relabelling :=
  steps.foldl (fun r b => r.then (if b then genB else genA)) relabelId

private def pointWords : List (List Bool) := [[],[false],[true],[true,true]]

private def lineWords : List (List Bool) :=
  [[], [false,true,false], [false,true], [false], [false,false],
    [false,true,false,true], [false,false,false,true], [false,true,true],
    [false,true,true,false], [false,false,false], [false,false,false,false],
    [false,false,false,false,false]]

private theorem coord_point : ∀ p : Fin 13, incident p 0 →
    ∃ w ∈ pointWords, (composition w).point 0 = p ∧ (composition w).line 0 = 0 := by decide

private theorem coord_line : ∀ l : Fin 13, l ≠ 0 →
    ∃ w ∈ lineWords, (composition w).line 1 = l ∧ (composition w).line 0 = 0 := by decide

theorem anchor_incidence (p l : Fin 13) (edge : incident p l) :
    ∃ r : Relabelling, r.point p = 0 ∧ r.line l = 0 := by
  let t := translate (-l)
  have tl : t.line l = 0 := by simp [t, translate]
  have atZero := (t.incidence p l).mpr edge
  rw [tl] at atZero
  obtain ⟨w, _, ep, el⟩ := coord_point _ atZero
  refine ⟨t.then (composition w).inverse, ?_, ?_⟩
  · change (composition w).inverse.point (t.point p) = 0
    rw [← ep, point_inverse]
  · change (composition w).inverse.line (t.line l) = 0
    calc
      _ = (composition w).inverse.line ((composition w).line 0) := by rw [tl, el]
      _ = 0 := line_inverse _ _

theorem anchor_lines (l m : Fin 13) (different : m ≠ l) :
    ∃ r : Relabelling, r.line l = 0 ∧ r.line m = 1 := by
  let t := translate (-l)
  have tl : t.line l = 0 := by simp [t, translate]
  have nonzero : t.line m ≠ 0 := fun h => different (t.lineInjective (h.trans tl.symm))
  obtain ⟨w, _, em, el⟩ := coord_line _ nonzero
  refine ⟨t.then (composition w).inverse, ?_, ?_⟩
  · change (composition w).inverse.line (t.line l) = 0
    calc
      _ = (composition w).inverse.line ((composition w).line 0) := by rw [tl, el]
      _ = 0 := line_inverse _ _
  · change (composition w).inverse.line (t.line m) = 1
    rw [← em, line_inverse]

def Relabelling.vertex (r : Relabelling) (v : Fin 26) : Fin 26 :=
  if small : v.val < 13 then pt (r.point ⟨v.val,small⟩)
  else ln (r.line ⟨v.val-13,by have := v.isLt; omega⟩)

@[simp] theorem point_vertex (r : Relabelling) (p : Fin 13) :
    r.vertex (pt p) = pt (r.point p) := by
  unfold Relabelling.vertex
  have small : (pt p).val < 13 := p.isLt
  rw [dite_eq_left small]
  rfl

@[simp] theorem line_vertex (r : Relabelling) (l : Fin 13) :
    r.vertex (ln l) = ln (r.line l) := by
  unfold Relabelling.vertex
  have large : ¬ (ln l).val < 13 := by change ¬ 13+l.val < 13; omega
  rw [dite_eq_right large]
  congr 2
  exact Fin.ext (by change 13+l.val-13 = l.val; omega)

private theorem vertex_forms (v : Fin 26) :
    (∃ p : Fin 13, v = pt p) ∨ (∃ l : Fin 13, v = ln l) := by
  by_cases small : v.val < 13
  · exact Or.inl ⟨⟨v.val,small⟩, Fin.ext rfl⟩
  · let l : Fin 13 := ⟨v.val-13,by have := v.isLt; omega⟩
    exact Or.inr ⟨l, Fin.ext (by change v.val = 13+(v.val-13); omega)⟩

private theorem no_two_points : ∀ p q : Fin 13, ¬ plane.Adj (pt p) (pt q) := by decide
private theorem no_two_lines : ∀ l m : Fin 13, ¬ plane.Adj (ln l) (ln m) := by decide

theorem Relabelling.graph_adj (r : Relabelling) (u v : Fin 26) :
    plane.Adj (r.vertex u) (r.vertex v) ↔ plane.Adj u v := by
  rcases vertex_forms u with ⟨p,rfl⟩ | ⟨l,rfl⟩ <;>
    rcases vertex_forms v with ⟨q,rfl⟩ | ⟨m,rfl⟩
  · simp only [point_vertex, no_two_points]
  · simpa only [point_vertex, line_vertex, ← adj_coordinates] using r.incidence p m
  · simpa only [point_vertex, line_vertex, plane.adj_comm (ln _) (pt _), ← adj_coordinates]
      using r.incidence q l
  · simp only [line_vertex, no_two_lines]

theorem Relabelling.vertex_surjective (r : Relabelling) : Function.Surjective r.vertex := by
  intro v
  rcases vertex_forms v with ⟨p,rfl⟩ | ⟨l,rfl⟩
  · obtain ⟨q,h⟩ := Finite.surjective_of_injective r.pointInjective p
    exact ⟨pt q, by simp [h]⟩
  · obtain ⟨m,h⟩ := Finite.surjective_of_injective r.lineInjective l
    exact ⟨ln m, by simp [h]⟩

theorem Relabelling.preserves_tests (r : Relabelling) (x : Fin 26 → Bool) :
    graphFun plane ∅ (x ∘ r.vertex) = graphFun plane ∅ x := by
  apply Bool.eq_iff_iff.mpr
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, Function.comp_apply]
  constructor
  · rintro ⟨u,v,adj,xu,xv⟩
    exact ⟨r.vertex u, r.vertex v, (r.graph_adj u v).mpr adj, xu, xv⟩
  · rintro ⟨u,v,adj,xu,xv⟩
    obtain ⟨p,rfl⟩ := r.vertex_surjective u
    obtain ⟨q,rfl⟩ := r.vertex_surjective v
    exact ⟨p,q,(r.graph_adj p q).mp adj,xu,xv⟩

/-- Exchange points and lines in the cyclic coordinates of the encoder. -/
def dual (v : Fin 26) : Fin 26 :=
  if small : v.val < 13 then ln (-⟨v.val,small⟩)
  else pt (-⟨v.val-13,by have := v.isLt; omega⟩)

theorem dual_involutive : Function.Involutive dual := by
  change ∀ v : Fin 26, dual (dual v) = v
  decide

theorem dual_adj : ∀ u v, plane.Adj (dual u) (dual v) ↔ plane.Adj u v := by decide

#print axioms anchor_incidence
#print axioms anchor_lines
#print axioms Relabelling.preserves_tests

end SixEdge.Plane
