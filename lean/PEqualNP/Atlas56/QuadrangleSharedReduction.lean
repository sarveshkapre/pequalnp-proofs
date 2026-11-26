import PEqualNP.Atlas56.QuadranglePartialFooling

/-!
The shared three-union diamond has a small partial rectangle-cover obstruction.
This reduction is independent of the quadrangle and of any finite computation.
-/
namespace QuadrangleSharedReduction
open Set TwoIntersections QuadranglePartialFooling

variable {ι κ : Type*}

/-- The least rectangle containing a set of cells. -/
def hull (s : Set (ι × κ)) : Set (ι × κ) :=
  (Prod.fst '' s) ×ˢ (Prod.snd '' s)

theorem hull_rectangle (s : Set (ι × κ)) : Rectangle (hull s) :=
  ⟨_, _, rfl⟩

theorem subset_hull (s : Set (ι × κ)) : s ⊆ hull s := by
  intro p hp
  exact ⟨⟨p, hp, rfl⟩, ⟨p, hp, rfl⟩⟩

theorem hull_minimal {s r : Set (ι × κ)} (hr : Rectangle r) (hs : s ⊆ r) :
    hull s ⊆ r := by
  obtain ⟨rows, cols, rfl⟩ := hr
  rintro p ⟨⟨x, hx, hxr⟩, ⟨y, hy, hyc⟩⟩
  exact ⟨hxr ▸ (hs hx).1, hyc ▸ (hs hy).2⟩

theorem hull_mono {s t : Set (ι × κ)} (h : s ⊆ t) : hull s ⊆ hull t :=
  hull_minimal (hull_rectangle t) (Subset.trans h (subset_hull t))

theorem hull_eq {s : Set (ι × κ)} (hs : Rectangle s) : hull s = s :=
  Subset.antisymm (hull_minimal hs (Subset.refl s)) (subset_hull s)

/-- The rectangle forced into the first filtered arm. -/
def leftHull (z c : Set (ι × κ)) := hull (z \ c)

/-- The forced residual fits in a rectangle exactly when that rectangle and
the original set cover the target. -/
theorem leftHull_subset_iff_union {z c d : Set (ι × κ)} (hd : Rectangle d) :
    leftHull z c ⊆ d ↔ z ⊆ c ∪ d := by
  constructor
  · intro h p hp
    by_cases hc : p ∈ c
    · exact Or.inl hc
    · exact Or.inr (h (subset_hull _ ⟨hp, hc⟩))
  · intro h
    apply hull_minimal hd
    intro p hp
    rcases h hp.1 with hc | hd
    · exact False.elim (hp.2 hc)
    · exact hd

/-- The residual-hull relation is symmetric on rectangles. Together with
antitonicity, this explains the identity `T³ = T`. -/
theorem leftHull_subset_iff_symmetric {z c d : Set (ι × κ)}
    (hc : Rectangle c) (hd : Rectangle d) :
    leftHull z c ⊆ d ↔ leftHull z d ⊆ c := by
  rw [leftHull_subset_iff_union hd, leftHull_subset_iff_union hc, Set.union_comm]

/-- Cells of the complement that the shared signal has to avoid. -/
def forbidden (z c e : Set (ι × κ)) : Set (ι × κ) :=
  zᶜ ∩ ((c ∩ leftHull z e) ∪ (leftHull z c ∩ e) ∪
    (leftHull z c ∩ leftHull z e))

/-- Every shared diamond induces a cover of `z \ (c ∩ e)` by its two shared
rectangles, avoiding `forbidden z c e`.  The arbitrary original arm rectangles
are eliminated using least rectangle hulls. -/
theorem diamond_partial_cover {z a b c d e f : Set (ι × κ)}
    (hd : Rectangle d) (hf : Rectangle f)
    (hz : z = (c ∪ (d ∩ (a ∪ b))) ∩ (e ∪ (f ∩ (a ∪ b)))) :
    c ∩ e ⊆ z ∧ z \ (c ∩ e) ⊆ a ∪ b ∧
      Disjoint (a ∪ b) (forbidden z c e) := by
  have hzd : z \ c ⊆ d := by
    intro p hp
    have hz' := hp.1
    rw [hz] at hz'
    rcases hz'.1 with hc | hdh
    · exact False.elim (hp.2 hc)
    · exact hdh.1
  have hzf : z \ e ⊆ f := by
    intro p hp
    have hz' := hp.1
    rw [hz] at hz'
    rcases hz'.2 with he | hfh
    · exact False.elim (hp.2 he)
    · exact hfh.1
  have hdd : leftHull z c ⊆ d := hull_minimal hd hzd
  have hff : leftHull z e ⊆ f := hull_minimal hf hzf
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    rw [hz]
    exact ⟨Or.inl hp.1, Or.inl hp.2⟩
  · intro p hp
    have hz' := hp.1
    rw [hz] at hz'
    rcases hz'.1 with hc | hdh
    · rcases hz'.2 with he | hfh
      · exact False.elim (hp.2 ⟨hc, he⟩)
      · exact hfh.2
    · exact hdh.2
  · apply Set.disjoint_left.mpr
    intro p hh hb
    apply hb.1
    rw [hz]
    rcases hb.2 with (h | h) | h
    · exact ⟨Or.inl h.1, Or.inr ⟨hff h.2, hh⟩⟩
    · exact ⟨Or.inr ⟨hdd h.1, hh⟩, Or.inl h.2⟩
    · exact ⟨Or.inr ⟨hdd h.1, hh⟩, Or.inr ⟨hff h.2, hh⟩⟩

/-- The partial-cover reduction is exact: its cover and avoidance conditions
reconstruct the diamond with the least possible arm rectangles. -/
theorem diamond_reconstruction {z h c e : Set (ι × κ)}
    (hi : c ∩ e ⊆ z) (cover : z \ (c ∩ e) ⊆ h)
    (avoid : Disjoint h (forbidden z c e)) :
    z = (c ∪ (leftHull z c ∩ h)) ∩ (e ∪ (leftHull z e ∩ h)) := by
  apply Set.Subset.antisymm
  · intro p hp
    by_cases hpc : p ∈ c
    · refine ⟨Or.inl hpc, ?_⟩
      by_cases hpe : p ∈ e
      · exact Or.inl hpe
      · exact Or.inr ⟨subset_hull _ ⟨hp, hpe⟩,
          cover ⟨hp, fun h => hpe h.2⟩⟩
    · have hph : p ∈ h := cover ⟨hp, fun h => hpc h.1⟩
      refine ⟨Or.inr ⟨subset_hull _ ⟨hp, hpc⟩, hph⟩, ?_⟩
      by_cases hpe : p ∈ e
      · exact Or.inl hpe
      · exact Or.inr ⟨subset_hull _ ⟨hp, hpe⟩, hph⟩
  · intro p hp
    by_contra hpz
    rcases hp with ⟨hc | hd, he | hf⟩
    · exact hpz (hi ⟨hc, he⟩)
    · exact Set.disjoint_left.mp avoid hf.2
        ⟨hpz, Or.inl (Or.inl ⟨hc, hf.1⟩)⟩
    · exact Set.disjoint_left.mp avoid hd.2
        ⟨hpz, Or.inl (Or.inr ⟨hd.1, he⟩)⟩
    · exact Set.disjoint_left.mp avoid hd.2
        ⟨hpz, Or.inr ⟨hd.1, hf.1⟩⟩

/-- A reusable sufficient condition excluding every shared three-union diamond.
The hypothesis asks for a three-cell partial fooling set for each pair of
unfiltered rectangles. -/
theorem no_diamond_of_partial_fooling {z : Set (ι × κ)}
    (obstruction : ∀ c e : Set (ι × κ), Rectangle c → Rectangle e → c ∩ e ⊆ z →
      ∃ w : Fin 3 → ι × κ, PartialFooling (z \ (c ∩ e)) (forbidden z c e) w) :
    ¬ ∃ a b c d e f : Set (ι × κ),
      Rectangle a ∧ Rectangle b ∧ Rectangle c ∧ Rectangle d ∧
      Rectangle e ∧ Rectangle f ∧
      z = (c ∪ (d ∩ (a ∪ b))) ∩ (e ∪ (f ∩ (a ∪ b))) := by
  rintro ⟨a, b, c, d, e, f, ha, hb, hc, hd, he, hf, hz⟩
  obtain ⟨hi, hcover, havoid⟩ := diamond_partial_cover hd hf hz
  obtain ⟨w, hw⟩ := obstruction c e hc he hi
  exact no_union_two hw ha hb hcover havoid

/-- If `d` is the hull of `z \ c`, then `hull (z \ d)` is the smallest
rectangle that can replace `c` while retaining that same residual hull. -/
theorem residual_hull_involution {z c : Set (ι × κ)} (hc : Rectangle c) :
    leftHull z (leftHull z (leftHull z c)) = leftHull z c := by
  have hsmall : leftHull z (leftHull z c) ⊆ c := by
    apply hull_minimal hc
    intro p hp
    by_contra hpc
    exact hp.2 (subset_hull _ ⟨hp.1, hpc⟩)
  apply Subset.antisymm
  · apply hull_minimal (hull_rectangle _)
    intro p hp
    by_contra hpd
    exact hp.2 (subset_hull _ ⟨hp.1, hpd⟩)
  · apply hull_mono
    intro p hp
    exact ⟨hp.1, fun hpc => hp.2 (hsmall hpc)⟩

/-- Canonically shrink `c` while retaining both a designated contained rectangle
`i` and the residual hull. -/
def canonical (z i c : Set (ι × κ)) : Set (ι × κ) :=
  hull (i ∪ leftHull z (leftHull z c))

theorem canonical_subset {z i c : Set (ι × κ)} (hc : Rectangle c) (hi : i ⊆ c) :
    canonical z i c ⊆ c := by
  apply hull_minimal hc
  rintro p (hp | hp)
  · exact hi hp
  · apply hull_minimal hc (s := z \ leftHull z c) (by
      intro q hq
      by_contra hqc
      exact hq.2 (subset_hull _ ⟨hq.1, hqc⟩)) hp

theorem subset_canonical (z i c : Set (ι × κ)) : i ⊆ canonical z i c := by
  intro p hp
  exact subset_hull _ (Or.inl hp)

theorem canonical_residual {z i c : Set (ι × κ)} (hc : Rectangle c) (hi : i ⊆ c) :
    leftHull z (canonical z i c) = leftHull z c := by
  apply Subset.antisymm
  · apply hull_minimal (hull_rectangle _)
    intro p hp
    by_contra hpd
    apply hp.2
    apply subset_hull
    exact Or.inr (subset_hull _ ⟨hp.1, hpd⟩)
  · apply hull_mono
    intro p hp
    exact ⟨hp.1, fun h => hp.2 (canonical_subset hc hi h)⟩

theorem canonical_intersection {z c e : Set (ι × κ)}
    (hc : Rectangle c) (he : Rectangle e) :
    canonical z (c ∩ e) c ∩ canonical z (c ∩ e) e = c ∩ e := by
  apply Subset.antisymm
  · intro p hp
    exact ⟨canonical_subset hc Set.inter_subset_left hp.1,
      canonical_subset he Set.inter_subset_right hp.2⟩
  · intro p hp
    exact ⟨subset_canonical _ _ _ hp, subset_canonical _ _ _ hp⟩

/-- Canonical shrinking can only remove forbidden cells and leaves the required
cells unchanged.  It is therefore sufficient to find partial fooling sets after
shrinking. -/
theorem canonical_forbidden_subset {z c e : Set (ι × κ)}
    (hc : Rectangle c) (he : Rectangle e) :
    forbidden z (canonical z (c ∩ e) c) (canonical z (c ∩ e) e) ⊆
      forbidden z c e := by
  unfold forbidden
  rw [canonical_residual hc Set.inter_subset_left,
    canonical_residual he Set.inter_subset_right]
  rintro p ⟨hp, (h | h) | h⟩
  · exact ⟨hp, Or.inl (Or.inl ⟨canonical_subset hc Set.inter_subset_left h.1, h.2⟩)⟩
  · exact ⟨hp, Or.inl (Or.inr ⟨h.1, canonical_subset he Set.inter_subset_right h.2⟩)⟩
  · exact ⟨hp, Or.inr h⟩

/-- Nested residual rectangles remove the genuine shared interaction: the
diamond becomes one rectangle union an intersection of two two-rectangle
unions (the fourth formula shape). -/
theorem diamond_nested {h c d e f : Set (ι × κ)} (hdf : d ⊆ f) :
    (c ∪ (d ∩ h)) ∩ (e ∪ (f ∩ h)) =
      (c ∩ e) ∪ (h ∩ ((c ∩ f) ∪ d)) := by
  ext p
  have hdf' : p ∈ d → p ∈ f := fun hp => hdf hp
  simp only [Set.mem_inter_iff, Set.mem_union]
  tauto

theorem rectangle_inter {c e : Set (ι × κ)}
    (hc : Rectangle c) (he : Rectangle e) : Rectangle (c ∩ e) := by
  obtain ⟨cr, cc, rfl⟩ := hc
  obtain ⟨er, ec, rfl⟩ := he
  exact ⟨cr ∩ er, cc ∩ ec, by ext p; simp; tauto⟩

/-- In a shared representation, inclusion of one least residual rectangle in
the other yields an ordinary three-union formula. -/
theorem nested_residual_formula {z a b c d e f : Set (ι × κ)}
    (ha : Rectangle a) (hb : Rectangle b) (hc : Rectangle c)
    (hd : Rectangle d) (he : Rectangle e) (hf : Rectangle f)
    (hz : z = (c ∪ (d ∩ (a ∪ b))) ∩ (e ∪ (f ∩ (a ∪ b))))
    (hdf : leftHull z c ⊆ leftHull z e) :
    ∃ i j k l m : Set (ι × κ), Rectangle i ∧ Rectangle j ∧ Rectangle k ∧
      Rectangle l ∧ Rectangle m ∧ z = i ∪ ((j ∪ k) ∩ (l ∪ m)) := by
  obtain ⟨hi, hcover, havoid⟩ := diamond_partial_cover hd hf hz
  have hn := diamond_reconstruction hi hcover havoid
  rw [diamond_nested hdf] at hn
  exact ⟨c ∩ e, a, b, c ∩ leftHull z e, leftHull z c,
    rectangle_inter hc he, ha, hb,
    rectangle_inter hc (hull_rectangle _), hull_rectangle _, hn⟩

/-- It suffices to check the canonically shrunken pairs: the required set is
unchanged, and every forbidden crossing obtained there remains forbidden. -/
theorem no_diamond_of_canonical_partial_fooling {z : Set (ι × κ)}
    (obstruction : ∀ c e : Set (ι × κ), Rectangle c → Rectangle e → c ∩ e ⊆ z →
      ∃ w : Fin 3 → ι × κ,
        PartialFooling (z \ (c ∩ e))
          (forbidden z (canonical z (c ∩ e) c) (canonical z (c ∩ e) e)) w) :
    ¬ ∃ a b c d e f : Set (ι × κ),
      Rectangle a ∧ Rectangle b ∧ Rectangle c ∧ Rectangle d ∧
      Rectangle e ∧ Rectangle f ∧
      z = (c ∪ (d ∩ (a ∪ b))) ∩ (e ∪ (f ∩ (a ∪ b))) := by
  apply no_diamond_of_partial_fooling
  intro c e hc he hi
  obtain ⟨w, hw⟩ := obstruction c e hc he hi
  refine ⟨w, hw.1, ?_⟩
  intro i j hij
  rcases hw.2 i j hij with h | h
  · exact Or.inl (canonical_forbidden_subset hc he h)
  · exact Or.inr (canonical_forbidden_subset hc he h)

/-- Increasing the unfiltered rectangle decreases its forced residual hull. -/
theorem leftHull_antitone {z c c' : Set (ι × κ)} (h : c ⊆ c') :
    leftHull z c' ⊆ leftHull z c := by
  apply hull_mono
  intro p hp
  exact ⟨hp.1, fun hpc => hp.2 (h hpc)⟩

/-- Forbidden cells that are already forced by rectangular lower and upper
bounds on `c,e`.  This makes a short interval certificate cover many cases. -/
def intervalForbidden (z cl cu el eu : Set (ι × κ)) : Set (ι × κ) :=
  zᶜ ∩ ((cl ∩ leftHull z eu) ∪ (leftHull z cu ∩ el) ∪
    (leftHull z cu ∩ leftHull z eu))

theorem interval_forbidden_subset {z c e cl cu el eu : Set (ι × κ)}
    (hcl : cl ⊆ c) (hcu : c ⊆ cu) (hel : el ⊆ e) (heu : e ⊆ eu) :
    intervalForbidden z cl cu el eu ⊆ forbidden z c e := by
  have hd := leftHull_antitone hcu (z := z)
  have hf := leftHull_antitone heu (z := z)
  rintro p ⟨hp, (h | h) | h⟩
  · exact ⟨hp, Or.inl (Or.inl ⟨hcl h.1, hf h.2⟩)⟩
  · exact ⟨hp, Or.inl (Or.inr ⟨hd h.1, hel h.2⟩)⟩
  · exact ⟨hp, Or.inr ⟨hd h.1, hf h.2⟩⟩

/-- A single certified partial fooling triple applies to every rectangle pair
between the indicated lower and upper bounds. -/
theorem interval_partial_fooling {z c e cl cu el eu : Set (ι × κ)}
    {w : Fin 3 → ι × κ}
    (hcl : cl ⊆ c) (hcu : c ⊆ cu) (hel : el ⊆ e) (heu : e ⊆ eu)
    (hw : PartialFooling (z \ (cu ∩ eu)) (intervalForbidden z cl cu el eu) w) :
    PartialFooling (z \ (c ∩ e)) (forbidden z c e) w := by
  refine ⟨?_, ?_⟩
  · intro i
    exact ⟨(hw.1 i).1, fun h => (hw.1 i).2 ⟨hcu h.1, heu h.2⟩⟩
  · intro i j hij
    rcases hw.2 i j hij with h | h
    · exact Or.inl (interval_forbidden_subset hcl hcu hel heu h)
    · exact Or.inr (interval_forbidden_subset hcl hcu hel heu h)

#print axioms diamond_partial_cover
#print axioms leftHull_subset_iff_union
#print axioms leftHull_subset_iff_symmetric
#print axioms diamond_reconstruction
#print axioms no_diamond_of_partial_fooling
#print axioms canonical_residual
#print axioms canonical_forbidden_subset
#print axioms nested_residual_formula
#print axioms no_diamond_of_canonical_partial_fooling
#print axioms interval_partial_fooling
end QuadrangleSharedReduction
