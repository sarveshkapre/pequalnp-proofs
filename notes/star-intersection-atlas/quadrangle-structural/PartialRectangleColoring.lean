import TwoIntersections

/-!
# Partial rectangle covers are exactly cross-compatible colorings

Positive cells must be covered; forbidden cells must be avoided. The remaining
cells are unconstrained. A color class can be filled to its rectangular hull
exactly when none of its cross-cells is forbidden.

The rectangle-cover/incompatibility-graph correspondence is classical
(Lovász–Saks). See Pourmoradnasseri and Theis, "The Rectangle Covering Number
of Random Boolean Matrices" (2017), Proposition 1.1 and its preceding definition:
https://www.combinatorics.org/ojs/index.php/eljc/article/download/v24i2p37/pdf/
This file formalizes the partial positive/forbidden-cell version and supplies
an explicit hull construction for the shared-circuit residual application;
it does not claim a new historical rectangle-cover/coloring correspondence.

The theorem is independent of finiteness, graph sparsity, and the number of
colors. Colors are assigned only to the subtype of positive cells, so the
empty-positive/empty-color case requires no artificial inhabited assumption.
-/
namespace PartialRectangleColoring
open Set TwoIntersections

variable {ι κ γ : Type*}

/-- Cells with the same color have neither cross-cell forbidden. The diagonal
case also enforces that positive cells themselves are not forbidden. -/
def Compatible (P B : Set (ι × κ)) (color : P → γ) : Prop :=
  ∀ p q : P, color p = color q →
    (p.val.1,q.val.2) ∉ B ∧ (q.val.1,p.val.2) ∉ B

/-- A possibly infinite family of rectangles covering all positive cells and
containing no forbidden cell. -/
def Cover (P B : Set (ι × κ)) (r : γ → Set (ι × κ)) : Prop :=
  (∀ j, Rectangle (r j)) ∧
  (∀ j, Disjoint (r j) B) ∧
  (∀ p ∈ P, ∃ j, p ∈ r j)

/-- The rectangular hull of a color class: its row projection times its
column projection. -/
def colorHull (P : Set (ι × κ)) (color : P → γ) (j : γ) : Set (ι × κ) :=
  {i | ∃ p : P, color p = j ∧ p.val.1 = i} ×ˢ
  {k | ∃ p : P, color p = j ∧ p.val.2 = k}

theorem colorHull_rectangle (P : Set (ι × κ)) (color : P → γ) (j : γ) :
    Rectangle (colorHull P color j) := ⟨_,_,rfl⟩

theorem compatible_hulls_cover {P B : Set (ι × κ)} {color : P → γ}
    (h : Compatible P B color) : Cover P B (colorHull P color) := by
  refine ⟨colorHull_rectangle P color, ?_, ?_⟩
  · intro j
    apply Set.disjoint_left.mpr
    rintro x ⟨⟨p,hp,hpr⟩,⟨q,hq,hqc⟩⟩ hbad
    have hcross := (h p q (hp.trans hq.symm)).1
    apply hcross
    simpa only [hpr,hqc,Prod.eta] using hbad
  · intro p hp
    exact ⟨color ⟨p,hp⟩, ⟨⟨⟨p,hp⟩,rfl,rfl⟩,⟨⟨p,hp⟩,rfl,rfl⟩⟩⟩

theorem cover_has_compatible_coloring {P B : Set (ι × κ)}
    {r : γ → Set (ι × κ)} (h : Cover P B r) :
    ∃ color : P → γ, Compatible P B color := by
  classical
  let color : P → γ := fun p => Classical.choose (h.2.2 p.val p.property)
  have hc : ∀ p : P, p.val ∈ r (color p) :=
    fun p => Classical.choose_spec (h.2.2 p.val p.property)
  refine ⟨color,?_⟩
  intro p q hpq
  have hp := hc p
  have hq : q.val ∈ r (color p) := by rw [hpq]; exact hc q
  obtain ⟨rows,cols,hr⟩ := h.1 (color p)
  rw [hr] at hp hq
  constructor
  · intro hbad
    apply Set.disjoint_left.mp (h.2.1 (color p)) _ hbad
    rw [hr]
    exact ⟨hp.1,hq.2⟩
  · intro hbad
    apply Set.disjoint_left.mp (h.2.1 (color p)) _ hbad
    rw [hr]
    exact ⟨hq.1,hp.2⟩

/-- Exact semantic criterion: coverability by `γ` rectangles is colorability
of the positive cells under the forbidden-cross incompatibility relation. -/
theorem cover_iff_coloring (P B : Set (ι × κ)) :
    (∃ r : γ → Set (ι × κ), Cover P B r) ↔
      ∃ color : P → γ, Compatible P B color := by
  constructor
  · rintro ⟨r,hr⟩
    exact cover_has_compatible_coloring hr
  · rintro ⟨color,hcolor⟩
    exact ⟨colorHull P color,compatible_hulls_cover hcolor⟩

/-- An explicitly unpacked form, convenient for uses which do not introduce
the `Cover` abbreviation. -/
theorem rectangle_cover_iff_coloring (P B : Set (ι × κ)) :
    (∃ r : γ → Set (ι × κ),
      (∀ j, Rectangle (r j)) ∧ (∀ j, Disjoint (r j) B) ∧
      (∀ p ∈ P, ∃ j, p ∈ r j)) ↔
      ∃ color : P → γ, Compatible P B color := cover_iff_coloring P B

/-- The same compatibility condition in ordinary graph-coloring language:
forbidden-cross neighbors must receive different colors. -/
theorem compatible_iff_distinct_on_forbidden_cross {P B : Set (ι × κ)}
    (color : P → γ) : Compatible P B color ↔
      ∀ p q : P, ((p.val.1,q.val.2) ∈ B ∨ (q.val.1,p.val.2) ∈ B) →
        color p ≠ color q := by
  constructor
  · intro h p q hbad heq
    rcases hbad with hbad | hbad
    · exact (h p q heq).1 hbad
    · exact (h p q heq).2 hbad
  · intro h p q heq
    exact ⟨fun hb => h p q (Or.inl hb) heq, fun hb => h p q (Or.inr hb) heq⟩

/-- The partial two-rectangle problem is exactly two-colorability. This is
stronger than the sufficient obstruction supplied by a three-cell fooling set. -/
theorem two_rectangles_iff_coloring (P B : Set (ι × κ)) :
    (∃ a b : Set (ι × κ), Rectangle a ∧ Rectangle b ∧
      P ⊆ a ∪ b ∧ Disjoint (a ∪ b) B) ↔
      ∃ color : P → Fin 2, Compatible P B color := by
  constructor
  · rintro ⟨a,b,ha,hb,hcover,havoid⟩
    apply (rectangle_cover_iff_coloring (γ := Fin 2) P B).mp
    let r : Fin 2 → Set (ι × κ) := ![a,b]
    refine ⟨r,?_,?_,?_⟩
    · intro j
      fin_cases j <;> simpa [r] using (by assumption : Rectangle _)
    · intro j
      apply Set.disjoint_left.mpr
      intro p hp hbad
      apply Set.disjoint_left.mp havoid _ hbad
      fin_cases j
      · exact Or.inl hp
      · exact Or.inr hp
    · intro p hp
      rcases hcover hp with h | h
      · exact ⟨0,h⟩
      · exact ⟨1,h⟩
  · intro hc
    obtain ⟨r,hr,havoid,hcover⟩ :=
      (rectangle_cover_iff_coloring (γ := Fin 2) P B).mpr hc
    refine ⟨r 0,r 1,hr 0,hr 1,?_,?_⟩
    · intro p hp
      obtain ⟨j,hj⟩ := hcover p hp
      fin_cases j
      · exact Or.inl hj
      · exact Or.inr hj
    · apply Set.disjoint_left.mpr
      intro p hp hbad
      rcases hp with h | h
      · exact Set.disjoint_left.mp (havoid 0) h hbad
      · exact Set.disjoint_left.mp (havoid 1) h hbad

#print axioms compatible_hulls_cover
#print axioms cover_has_compatible_coloring
#print axioms cover_iff_coloring
#print axioms two_rectangles_iff_coloring
end PartialRectangleColoring
