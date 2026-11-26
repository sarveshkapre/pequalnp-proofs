import ThreeIntersectionsCubeGap

/-! Semantic bridge from three binary rectangle unions to three-dimensional boxes. -/
namespace ThreeIntersectionsBoxes
open Set TwoIntersections ThreeIntersectionsCubeGap
open ThreeIntersectionsRectangleGap

/-- The choices of rectangle side available at a specified row or column. -/
noncomputable def membershipBox {ι : Type*} (R : Fin 3 → Bool → Set ι) (r : ι) : Box := by
  classical
  exact fun j => Finset.univ.filter fun b => r ∈ R j b

theorem mem_membershipBox {ι : Type*} (R : Fin 3 → Bool → Set ι) (r : ι) (v : Code) :
    v ∈ cube (membershipBox R r) ↔ ∀ j, r ∈ R j (v j) := by
  classical
  simp [cube, membershipBox]

/-- A code in both boxes is exactly a common rectangle choice at every factor. -/
theorem boxes_inter_iff {ι κ : Type*} (R : Fin 3 → Bool → Set ι)
    (C : Fin 3 → Bool → Set κ) (r : ι) (c : κ) :
    ((cube (membershipBox R r)) ∩ (cube (membershipBox C c))).Nonempty ↔
      ∀ j, ∃ b, r ∈ R j b ∧ c ∈ C j b := by
  classical
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨hr,hc⟩ := Finset.mem_inter.mp hv
    have hr' := (mem_membershipBox R r v).mp hr
    have hc' := (mem_membershipBox C c v).mp hc
    intro j
    exact ⟨v j, hr' j, hc' j⟩
  · intro h
    choose v hv using h
    refine ⟨v, Finset.mem_inter.mpr ⟨?_,?_⟩⟩
    · exact (mem_membershipBox R r v).mpr (fun j => (hv j).1)
    · exact (mem_membershipBox C c v).mpr (fun j => (hv j).2)

/-- Any three binary-union rectangle factorization supplies the boxes used
by the cube obstruction, including empty factors and unrestricted rectangles. -/
theorem three_pair_products_boxes {a b c d e f : Set Cell}
    (ha : Rectangle a) (hb : Rectangle b) (hc : Rectangle c)
    (hd : Rectangle d) (he : Rectangle e) (hf : Rectangle f)
    (hz : zero = ((a ∪ b) ∩ (c ∪ d)) ∩ (e ∪ f)) :
    ∃ X Y : Fin 8 → Box,
      ∀ r c, (r,c) ∈ zero ↔ ((cube (X r)) ∩ (cube (Y c))).Nonempty := by
  classical
  obtain ⟨ar,ac,rfl⟩ := ha
  obtain ⟨br,bc,rfl⟩ := hb
  obtain ⟨cr,cc,rfl⟩ := hc
  obtain ⟨dr,dc,rfl⟩ := hd
  obtain ⟨er,ec,rfl⟩ := he
  obtain ⟨fr,fc,rfl⟩ := hf
  let R : Fin 3 → Bool → Set (Fin 8) :=
    ![fun q => if q then br else ar,
      fun q => if q then dr else cr,
      fun q => if q then fr else er]
  let C : Fin 3 → Bool → Set (Fin 8) :=
    ![fun q => if q then bc else ac,
      fun q => if q then dc else cc,
      fun q => if q then fc else ec]
  refine ⟨membershipBox R, membershipBox C, ?_⟩
  intro r c
  rw [boxes_inter_iff, hz]
  simp [R, C, Fin.forall_fin_succ, Bool.exists_bool]
  tauto

/-- The cube obstruction rules out the third formula shape for the actual matrix. -/
theorem not_three_pair_products :
    ¬ ∃ a b c d e f : Set Cell,
      Rectangle a ∧ Rectangle b ∧ Rectangle c ∧ Rectangle d ∧
      Rectangle e ∧ Rectangle f ∧
      zero = ((a ∪ b) ∩ (c ∪ d)) ∩ (e ∪ f) := by
  rintro ⟨a,b,c,d,e,f,ha,hb,hc,hd,he,hf,hz⟩
  obtain ⟨X,Y,hxy⟩ := three_pair_products_boxes ha hb hc hd he hf hz
  exact no_boxes X Y hxy

#print axioms boxes_inter_iff
#print axioms three_pair_products_boxes
#print axioms not_three_pair_products
end ThreeIntersectionsBoxes
