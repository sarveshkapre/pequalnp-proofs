import PEqualNP.ThreeGateGain.GainGeometryFrame

namespace GainSelection
open Finset TriangleOptimality GainGeometry
open scoped Classical

variable {P L I J : Type*}

structure Side (H : I → J → Prop) (r : P → I) (c : L → J) (A : Finset P) (B : Finset L) where
  centers : Finset P
  active : centers ⊆ A
  leaf : {p // p ∈ centers} → J
  big : ∀ p, 4 ≤ (fiber B c (leaf p)).card
  attached : ∀ p, H (r p.val) (leaf p)
  unique : ∀ p p' (_ : p' ∈ A), H (r p') (leaf p) → p' = p.val
  outside : ∀ p ∈ A, p ∉ centers → ∀ j, H (r p) j → (fiber B c j).card ≤ 3

/-- Every large column class that fires on an active row picks out just that
row. Pick one such class for each distinct physical center. -/
noncomputable def select (G : P → L → Prop) (hs : NoSquare G)
    (H : I → J → Prop) (r : P → I) (c : L → J) (A : Finset P) (B : Finset L)
    (positive : ∀ l ∈ B, 0 < ∑ p ∈ A, weight G (fun p l => H (r p) (c l)) p l) :
    Side H r c A B := by
  classical
  let X := A.filter (fun p => ∃ j, 4 ≤ (fiber B c j).card ∧ H (r p) j)
  have ex (p : {p // p ∈ X}) : ∃ j, 4 ≤ (fiber B c j).card ∧ H (r p.val) j :=
    (mem_filter.mp p.property).2
  let leaf (p : {p // p ∈ X}) := Classical.choose (ex p)
  have spec (p : {p // p ∈ X}) : 4 ≤ (fiber B c (leaf p)).card ∧ H (r p.val) (leaf p) :=
    Classical.choose_spec (ex p)
  refine ⟨X,filter_subset _ _,leaf,fun p => (spec p).1,fun p => (spec p).2,?_,?_⟩
  · intro p q hq h
    let U := A.filter (fun q => H (r q) (leaf p))
    have pos (l : L) (hl : l ∈ fiber B c (leaf p)) :
        0 < ∑ z ∈ U, signedCell (fun l z => G z l) l z := by
      have eq := (mem_filter.mp hl).2
      have hpos := positive l (mem_filter.mp hl).1
      simpa only [U, sum_filter, weight, signedCell, hit, eq] using hpos
    have sq : NoSquare (fun l p => G p l) :=
      fun l m p q h₁ h₂ h₃ h₄ => (hs p q l m h₁ h₃ h₂ h₄).symm
    have one := heavy_unique _ sq _ U (spec p).1 pos
    have ha : p.val ∈ U := mem_filter.mpr ⟨(mem_filter.mp p.property).1,(spec p).2⟩
    have hb : q ∈ U := mem_filter.mpr ⟨hq,h⟩
    obtain ⟨v,hv⟩ := card_eq_one.mp one
    rw [hv] at ha hb
    exact (mem_singleton.mp hb).trans (mem_singleton.mp ha).symm
  · intro p hp hn j hj
    by_contra! h
    exact hn (mem_filter.mpr ⟨hp,j,h,hj⟩)

namespace Side
variable {H : I → J → Prop} {r : P → I} {c : L → J} {A : Finset P} {B : Finset L}
    (s : Side H r c A B)

noncomputable def centerTypes := s.centers.image r
noncomputable def leafTypes := s.centers.attach.image s.leaf

theorem center_mem {p : P} (hp : p ∈ s.centers) : r p ∈ s.centerTypes :=
  mem_image.mpr ⟨p,hp,rfl⟩

theorem leaf_mem (p : {p // p ∈ s.centers}) : s.leaf p ∈ s.leafTypes :=
  mem_image.mpr ⟨p,mem_attach _ _,rfl⟩

theorem leaf_mem_iff {j : J} : j ∈ s.leafTypes ↔ ∃ p, s.leaf p = j := by
  simp [leafTypes]

theorem center_label_unique (p : {p // p ∈ s.centers}) (q : P) (hq : q ∈ A)
    (e : r q = r p.val) : q = p.val :=
  s.unique p q hq (e.symm ▸ s.attached p)

theorem center_count : s.centerTypes.card = s.centers.card := by
  apply card_image_of_injOn
  intro p hp q hq e
  exact s.center_label_unique ⟨q,hq⟩ p (s.active hp) e

theorem leaf_injective : Function.Injective s.leaf := by
  intro p q e
  apply Subtype.ext
  apply s.unique q _ (s.active p.property)
  rw [← e]
  exact s.attached p

theorem leaf_count : s.leafTypes.card = s.centers.card := by
  rw [leafTypes,card_image_of_injective _ s.leaf_injective,card_attach]

theorem center_single (p : {p // p ∈ s.centers}) : fiber A r (r p.val) = {p.val} := by
  ext q
  simp only [fiber,mem_filter,mem_singleton]
  constructor
  · rintro ⟨hq,eq⟩
    exact s.center_label_unique p q hq eq
  · rintro rfl
    exact ⟨s.active p.property,rfl⟩

theorem residual_avoids (p : P) (hp : p ∈ A) (out : p ∉ s.centers) :
    ∀ j ∈ s.leafTypes, ¬ H (r p) j := by
  intro j hj edge
  obtain ⟨q,rfl⟩ := s.leaf_mem_iff.mp hj
  have eq := s.unique q p hp edge
  exact out (eq ▸ q.property)

theorem leaf_big {j : J} (hj : j ∈ s.leafTypes) : 4 ≤ (fiber B c j).card := by
  obtain ⟨p,rfl⟩ := s.leaf_mem_iff.mp hj
  exact s.big p

theorem types_disjoint (t : Side (fun j i => H i j) c r B A) :
    Disjoint s.centerTypes t.leafTypes := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hi
  have one := s.center_single ⟨p,hp⟩
  have four := t.leaf_big hj
  rw [one] at four
  simp at four

theorem center_partners {i : I} (hi : i ∈ s.centerTypes) :
    ∃! j, j ∈ s.leafTypes ∧ H i j := by
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hi
  let v : {p // p ∈ s.centers} := ⟨p,hp⟩
  refine ⟨s.leaf v, ⟨s.leaf_mem v,s.attached v⟩,?_⟩
  rintro j ⟨hj,he⟩
  obtain ⟨u,rfl⟩ := s.leaf_mem_iff.mp hj
  have eq : v = u := Subtype.ext (s.unique u p (s.active hp) he)
  exact congrArg s.leaf eq.symm

theorem leaf_partners {j : J} (hj : j ∈ s.leafTypes) :
    ∃! i, i ∈ s.centerTypes ∧ H i j := by
  obtain ⟨p,rfl⟩ := s.leaf_mem_iff.mp hj
  refine ⟨r p.val,⟨s.center_mem p.property,s.attached p⟩,?_⟩
  rintro i ⟨hi,he⟩
  obtain ⟨q,hq,rfl⟩ := mem_image.mp hi
  exact congrArg r (s.unique p q (s.active hq) he)

theorem leaves_nonadjacent (t : Side (fun j i => H i j) c r B A)
    {i : I} (hi : i ∈ t.leafTypes) {j : J} (hj : j ∈ s.leafTypes) : ¬ H i j := by
  intro edge
  obtain ⟨p,rfl⟩ := s.leaf_mem_iff.mp hj
  have four := t.leaf_big hi
  obtain ⟨q,hq⟩ := card_pos.mp (show 0 < (fiber A r i).card by omega)
  obtain ⟨hqA,hqi⟩ := mem_filter.mp hq
  have eq := s.unique p q hqA (hqi ▸ edge)
  have inc : i ∈ s.centerTypes := by simpa only [← hqi,eq] using s.center_mem p.property
  exact (Finset.disjoint_left.mp (s.types_disjoint t)) inc hi

/-- The sum over physical centers can be computed on their distinct types. -/
theorem center_sum (f : I → ℤ) :
    (∑ i ∈ s.centerTypes, f i) = ∑ p ∈ s.centers, f (r p) := by
  apply sum_image
  intro p hp q hq e
  exact s.center_label_unique ⟨q,hq⟩ p (s.active hp) e

theorem center_edges (t : Side (fun j i => H i j) c r B A) :
    edges H s.centerTypes t.centerTypes =
      edges (fun p l => H (r p) (c l)) s.centers t.centers := by
  unfold edges
  rw [s.center_sum]
  apply sum_congr rfl
  intro p _
  exact t.center_sum _

end Side

/-- All remaining dependence on the geometry is the per-center degree bound. -/
theorem host_score (G : P → L → Prop) (sq : NoSquare G)
    {H : I → J → Prop} {r : P → I} {c : L → J} {A : Finset P} {B : Finset L}
    (s : Side H r c A B) (t : Side (fun j i => H i j) c r B A)
    (X : Finset I) (Y : Finset J)
    (cover : ∀ i j, (∀ k ∈ s.leafTypes, ¬ H i k) → (∀ k ∈ t.leafTypes, ¬ H k j) →
      H i j → i ∈ X ∧ j ∈ Y) (small : X.card ≤ 28) (d : ℤ)
    (row : ∀ p ∈ A, ∑ l ∈ B, hit G p l ≤ d)
    (col : ∀ l ∈ B, ∑ p ∈ A, hit G p l ≤ d) :
    score G (fun p l => H (r p) (c l)) A B ≤
      ((s.leafTypes.card:ℤ)+t.leafTypes.card)*d - edges H s.centerTypes t.centerTypes +
      min (3*((X.card:ℤ)+Y.card)) (3*edges H X Y) := by
  classical
  rw [s.leaf_count,t.leaf_count,s.center_edges t,min_comm]
  apply frame_bound G sq H r c A s.centers B t.centers X Y s.active t.active d
    (fun p hp => row p (s.active hp)) (fun l hl => col l (t.active hl)) _ small
  intro p hp op l hl ol edge
  have both := cover _ _ (s.residual_avoids p hp op) (t.residual_avoids l hl ol) edge
  exact ⟨both.1,both.2,t.outside l hl ol _ edge,s.outside p hp op _ edge⟩

end GainSelection
