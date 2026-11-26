import PEqualNP.Atlas56.QuadrangleSquareObstruction
/-! Six finite hull obstructions for the quadrangle base-union shape.
The search script generates candidate data; all its obligations are checked
in Lean below, independently of the Python program. -/
namespace QuadrangleBaseUnion
open Set TwoIntersections ThreeIntersectionsQuadrangle QuadrangleSquareObstruction
local instance (p : Cell) : Decidable (p ∈ graph) := by
  unfold graph
  infer_instance

def points : Fin 6 → Fin 8 → Cell := ![
  ![(0, 1), (1, 0), (2, 3), (3, 4), (0, 3), (2, 0), (2, 5), (3, 5)],
  ![(0, 1), (1, 0), (2, 3), (3, 4), (1, 4), (2, 0), (2, 5), (3, 5)],
  ![(0, 1), (1, 0), (2, 3), (4, 2), (0, 2), (1, 2), (4, 3), (4, 3)],
  ![(0, 1), (1, 0), (3, 4), (4, 2), (0, 2), (1, 2), (4, 4), (4, 4)],
  ![(0, 1), (2, 3), (3, 4), (4, 2), (0, 2), (3, 1), (4, 4), (4, 4)],
  ![(1, 0), (2, 3), (3, 4), (4, 2), (1, 2), (2, 0), (4, 3), (4, 3)]
]

def conflicts : Fin 6 → List Constraint := ![
  [((0, 5), (0, 5)), ((3, 5), (3, 5)), ((0, 6), (0, 6)), ((1, 6), (1, 6)), ((6, 3), (6, 3)), ((0, 7), (0, 7)), ((1, 7), (1, 7)), ((7, 2), (7, 2)), ((1, 4), (1, 4)), ((3, 4), (3, 4)), ((4, 6), (4, 6)), ((0, 6), (0, 7)), ((0, 7), (0, 6)), ((1, 2), (1, 4)), ((1, 4), (1, 2)), ((0, 1), (0, 5)), ((0, 5), (0, 1)), ((2, 0), (5, 0)), ((2, 3), (5, 3))],
  [((0, 4), (0, 4)), ((2, 4), (2, 4)), ((0, 5), (0, 5)), ((3, 5), (3, 5)), ((0, 6), (0, 6)), ((1, 6), (1, 6)), ((6, 3), (6, 3)), ((0, 7), (0, 7)), ((1, 7), (1, 7)), ((7, 2), (7, 2)), ((4, 7), (4, 7)), ((5, 4), (5, 4)), ((0, 1), (0, 5)), ((0, 3), (0, 4)), ((0, 4), (0, 3)), ((0, 5), (0, 1)), ((0, 6), (0, 7)), ((0, 7), (0, 6))],
  [((1, 6), (1, 6)), ((6, 0), (6, 0)), ((2, 4), (2, 4)), ((4, 1), (4, 1)), ((2, 5), (2, 5)), ((5, 0), (5, 0)), ((5, 6), (5, 6)), ((2, 4), (2, 5)), ((2, 5), (2, 4)), ((0, 1), (4, 1)), ((1, 2), (5, 6)), ((3, 0), (6, 0)), ((3, 1), (6, 1)), ((4, 1), (0, 1)), ((5, 6), (1, 2)), ((2, 3), (2, 4)), ((2, 3), (2, 5)), ((2, 4), (2, 3)), ((2, 5), (2, 3))],
  [((0, 6), (0, 6)), ((6, 1), (6, 1)), ((2, 4), (2, 4)), ((4, 1), (4, 1)), ((2, 5), (2, 5)), ((5, 0), (5, 0)), ((4, 6), (4, 6)), ((2, 4), (2, 5)), ((2, 5), (2, 4)), ((0, 2), (4, 6)), ((1, 0), (5, 0)), ((3, 0), (6, 0)), ((3, 1), (6, 1)), ((4, 6), (0, 2)), ((5, 0), (1, 0)), ((2, 3), (2, 4)), ((2, 3), (2, 5)), ((2, 4), (2, 3)), ((2, 5), (2, 3))],
  [((0, 6), (0, 6)), ((1, 6), (1, 6)), ((1, 4), (1, 4)), ((2, 4), (2, 4)), ((1, 5), (1, 5)), ((3, 5), (3, 5)), ((4, 6), (4, 6)), ((5, 4), (5, 4)), ((6, 5), (6, 5)), ((0, 2), (4, 6)), ((2, 3), (5, 4)), ((3, 0), (6, 5)), ((4, 6), (0, 2)), ((5, 4), (2, 3)), ((6, 5), (3, 0))],
  [((0, 6), (0, 6)), ((2, 6), (2, 6)), ((1, 4), (1, 4)), ((2, 4), (2, 4)), ((2, 5), (2, 5)), ((3, 5), (3, 5)), ((4, 6), (4, 6)), ((5, 4), (5, 4)), ((6, 5), (6, 5)), ((0, 1), (4, 6)), ((1, 3), (5, 4)), ((3, 0), (6, 5)), ((4, 6), (0, 1)), ((5, 4), (1, 3)), ((6, 5), (3, 0))]
]

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem points_zero : ∀ j i, points j i ∈ zero := by
  unfold points zero graph mask
  decide +kernel

theorem core_fooling : ∀ j, Fooling zero (fun i : Fin 4 => points j (i.castAdd 4)) := by
  unfold Fooling points zero graph mask
  decide +kernel

theorem conflicts_valid_check : ∀ j,
    (conflicts j).all (fun t => decide (Valid graph (points j) t)) = true := by
  unfold conflicts Valid graph points mask
  decide +kernel

theorem conflicts_valid : ∀ j t, t ∈ conflicts j → Valid graph (points j) t := by
  intro j t ht
  exact of_decide_eq_true ((List.all_eq_true.mp (conflicts_valid_check j)) t ht)

theorem conflicts_hit_check : ∀ j (a : Fin 4 → Code), Function.Injective a →
    ∀ b : Fin 4 → Code,
      (conflicts j).any (fun t => decide (Active (join a b) t)) = true := by
  unfold conflicts Active join Function.Injective
  decide +kernel

theorem conflicts_hit : ∀ j (a : Fin 4 → Code), Function.Injective a →
    ∀ b : Fin 4 → Code, ∃ t ∈ conflicts j, Active (join a b) t := by
  intro j a ha b
  simpa only [List.any_eq_true, decide_eq_true_eq] using conflicts_hit_check j a ha b

theorem rectangle_avoids_points : ∀ (r : Finset (Fin 5)) (c : Finset (Fin 6)),
    (∀ i ∈ r, ∀ j ∈ c, (i, j) ∈ zero) →
    ∃ k : Fin 6, ∀ i : Fin 8, (points k i).1 ∉ r ∨ (points k i).2 ∉ c := by
  unfold points zero graph mask
  decide +kernel

/-- The fourth three-intersection normal form is impossible. -/
theorem no_base_union_two_by_two :
    ¬ ∃ a b c d e : Set Cell,
      Rectangle a ∧ Rectangle b ∧ Rectangle c ∧ Rectangle d ∧ Rectangle e ∧
        zero = a ∪ ((b ∪ c) ∩ (d ∪ e)) := by
  classical
  rintro ⟨a, b, c, d, e, ha, hb, hc, hd, he, hz⟩
  obtain ⟨rows, cols, rfl⟩ := ha
  have hrect : ∀ i ∈ rows.toFinset, ∀ j ∈ cols.toFinset, (i, j) ∈ zero := by
    intro i hi j hj
    rw [hz]
    exact Or.inl ⟨by simpa using hi, by simpa using hj⟩
  obtain ⟨k, hk⟩ := rectangle_avoids_points rows.toFinset cols.toFinset hrect
  have hout : ∀ i, points k i ∉ rows ×ˢ cols := by
    intro i hi
    rcases hk i with h | h
    · exact h (by simpa using hi.1)
    · exact h (by simpa using hi.2)
  have hcover : ∀ i, points k i ∈ (b ∪ c) ∩ (d ∪ e) := by
    intro i
    have h := points_zero k i
    rw [hz] at h
    exact h.resolve_left (hout i)
  let r : Bool → Set Cell := fun u => if u then c else b
  let s : Bool → Set Cell := fun u => if u then e else d
  apply no_square_cover (points k) (core_fooling k) (conflicts k)
    (conflicts_valid k) (conflicts_hit k) r s
  · intro u
    cases u
    · exact hb
    · exact hc
  · intro u
    cases u
    · exact hd
    · exact he
  · intro i
    rcases hcover i with ⟨h | h, h' | h'⟩
    · exact ⟨false, false, h, h'⟩
    · exact ⟨false, true, h, h'⟩
    · exact ⟨true, false, h, h'⟩
    · exact ⟨true, true, h, h'⟩
  · intro p u v hu hv
    have hp : p ∈ (b ∪ c) ∩ (d ∪ e) := by
      constructor
      · cases u
        · exact Or.inl hu
        · exact Or.inr hu
      · cases v
        · exact Or.inl hv
        · exact Or.inr hv
    have hpz : p ∈ zero := by rw [hz]; exact Or.inr hp
    exact hpz

#print axioms conflicts_hit
#print axioms rectangle_avoids_points
#print axioms no_base_union_two_by_two
end QuadrangleBaseUnion
