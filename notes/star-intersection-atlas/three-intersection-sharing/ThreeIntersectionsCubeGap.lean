import ThreeIntersectionsRectangleGap

/-! Subcube obstruction for the shared 8×8 rectangle example. -/
namespace ThreeIntersectionsCubeGap
open Set TwoIntersections
open ThreeIntersectionsRectangleGap

abbrev Code := Fin 3 → Bool
abbrev Box := Fin 3 → Finset Bool

def cube (b : Box) : Finset Code :=
  Finset.univ.filter fun v => ∀ j, v j ∈ b j

def neighbors (h : Code) : Finset Code :=
  Finset.univ.filter fun v =>
    ((Finset.univ : Finset (Fin 3)).filter fun j => v j ≠ h j).card = 1

def phi (h : Code) (b : Box) : Finset Code :=
  (cube b).erase h ∪ if h ∈ cube b then neighbors h else ∅

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cube_bounds : ∀ (h : Code) (b : Box),
    4 < ((cube b).erase h).card ∨ (phi h b).card < 4 ∨
      (cube b).card = 4 ∧ (phi h b).card = 4 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem phi_overlap : ∀ (h : Code) (b c : Box),
    (cube b).card = 4 → (cube c).card = 4 →
    ((cube b) ∩ (cube c)).Nonempty →
    2 ≤ ((phi h b) ∩ (phi h c)).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem two_vertex_neighbor : ∀ (b : Box) (v h : Code),
    v ∈ cube b → h ∈ cube b → (∀ w ∈ cube b, w = v ∨ w = h) → v ≠ h →
      v ∈ neighbors h := by
  decide +kernel

theorem single_hole (v : Fin 7 → Code) (hv : Function.Injective v) :
    ∃ h, (∀ i, v i ≠ h) ∧ ∀ w, w ≠ h → ∃ i, v i = w := by
  classical
  have code_card : Fintype.card Code = 8 := by decide +kernel
  have hex : ∃ h, ∀ i, v i ≠ h := by
    by_contra! hn
    have hs : Function.Surjective v := hn
    have bad := Fintype.card_le_of_surjective v hs
    rw [code_card, Fintype.card_fin] at bad
    omega
  obtain ⟨h, hh⟩ := hex
  let used := Finset.univ.image v
  have hc : used.card = 7 := by
    simp only [used, Finset.card_image_of_injective _ hv, Finset.card_univ,
      Fintype.card_fin]
  have he : ((Finset.univ : Finset Code).erase h).card = 7 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ h), Finset.card_univ, code_card]
  have sub : used ⊆ Finset.univ.erase h := by
    intro w hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    simp [hh i]
  have eqn : used = Finset.univ.erase h :=
    Finset.eq_of_subset_of_card_le sub (by omega)
  refine ⟨h, hh, ?_⟩
  intro w hw
  have mem : w ∈ used := by rw [eqn]; simp [hw]
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp mem
  exact ⟨i, hi⟩

theorem hit_sandwich (v : Fin 7 → Code) (h : Code)
    (hne : ∀ i, v i ≠ h) (all : ∀ w, w ≠ h → ∃ i, v i = w)
    (ys : Fin 7 → Box) (owned : ∀ i, v i ∈ cube (ys i))
    (bound : ∀ i w, w ∈ cube (ys i) → w = v i ∨ w = h)
    (b : Box) (p : Finset (Fin 7))
    (hits : ∀ i, i ∈ p ↔ ((cube b) ∩ (cube (ys i))).Nonempty) :
    (cube b).erase h ⊆ p.image v ∧ p.image v ⊆ phi h b := by
  classical
  constructor
  · intro w hw
    obtain ⟨wne, wmem⟩ := Finset.mem_erase.mp hw
    obtain ⟨i, hi⟩ := all w wne
    apply Finset.mem_image.mpr
    refine ⟨i, (hits i).mpr ?_, hi⟩
    refine ⟨w, Finset.mem_inter.mpr ⟨wmem, ?_⟩⟩
    simpa only [← hi] using owned i
  · intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨x, hx⟩ := (hits i).mp hi
    obtain ⟨hxb, hxy⟩ := Finset.mem_inter.mp hx
    rcases bound i x hxy with hxi | hxh
    · subst x
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_erase.mpr ⟨hne i, hxb⟩))
    · subst x
      have hn := two_vertex_neighbor (ys i) (v i) h (owned i) hxy
        (bound i) (hne i)
      apply Finset.mem_union.mpr
      exact Or.inr (by simpa only [ite_eq_left hxb] using hn)

theorem phi_eq_of_four (h : Code) (b : Box) (a : Finset Code)
    (lo : (cube b).erase h ⊆ a) (hi : a ⊆ phi h b) (hc : a.card = 4) :
    a = phi h b ∧ (cube b).card = 4 := by
  rcases cube_bounds h b with bad | bad | ⟨hbox, hphi⟩
  · have := Finset.card_le_card lo
    omega
  · have := Finset.card_le_card hi
    omega
  · exact ⟨Finset.eq_of_subset_of_card_le hi (by omega), hbox⟩

def p : Finset (Fin 7) := {0, 2, 4, 6}
def q : Finset (Fin 7) := {0, 1, 3, 5}

theorem zero_core : ∀ i j : Fin 7,
    (i.castSucc, j.castSucc) ∈ zero ↔ i = j := by
  unfold zero rowMasks
  decide +kernel

theorem zero_last_row : ∀ i : Fin 7,
    (7, i.castSucc) ∈ zero ↔ i ∈ p := by
  unfold zero rowMasks p
  decide +kernel

theorem zero_last_col : ∀ i : Fin 7,
    (i.castSucc, 7) ∈ zero ↔ i ∈ q := by
  unfold zero rowMasks q
  decide +kernel

theorem no_boxes (x y : Fin 8 → Box)
    (hm : ∀ r c, (r, c) ∈ zero ↔ ((cube (x r)) ∩ (cube (y c))).Nonempty) :
    False := by
  classical
  have hd : ∀ i : Fin 7,
      ((cube (x i.castSucc)) ∩ (cube (y i.castSucc))).Nonempty := by
    intro i
    exact (hm _ _).mp ((zero_core i i).mpr rfl)
  choose v hv using hd
  have hx : ∀ i, v i ∈ cube (x i.castSucc) :=
    fun i => (Finset.mem_inter.mp (hv i)).1
  have hy : ∀ i, v i ∈ cube (y i.castSucc) :=
    fun i => (Finset.mem_inter.mp (hv i)).2
  have vinj : Function.Injective v := by
    intro i j hij
    apply (zero_core i j).mp
    apply (hm _ _).mpr
    exact ⟨v i, Finset.mem_inter.mpr ⟨hx i, by rw [hij]; exact hy j⟩⟩
  obtain ⟨h, hne, all⟩ := single_hole v vinj
  have xb : ∀ i w, w ∈ cube (x i.castSucc) → w = v i ∨ w = h := by
    intro i w hw
    by_cases wh : w = h
    · exact Or.inr wh
    obtain ⟨j, hj⟩ := all w wh
    have ij : i = j := (zero_core i j).mp ((hm _ _).mpr
      ⟨w, Finset.mem_inter.mpr ⟨hw, by rw [← hj]; exact hy j⟩⟩)
    exact Or.inl (by rw [ij]; exact hj.symm)
  have yb : ∀ i w, w ∈ cube (y i.castSucc) → w = v i ∨ w = h := by
    intro i w hw
    by_cases wh : w = h
    · exact Or.inr wh
    obtain ⟨j, hj⟩ := all w wh
    have ji : j = i := (zero_core j i).mp ((hm _ _).mpr
      ⟨w, Finset.mem_inter.mpr ⟨by rw [← hj]; exact hx j, hw⟩⟩)
    exact Or.inl (by rw [← ji]; exact hj.symm)
  have ps := hit_sandwich v h hne all (fun i => y i.castSucc) hy yb (x 7) p
    (fun i => (zero_last_row i).symm.trans (hm 7 i.castSucc))
  have qs := hit_sandwich v h hne all (fun i => x i.castSucc) hx xb (y 7) q
    (by
      intro i
      rw [Finset.inter_comm]
      exact (zero_last_col i).symm.trans (hm i.castSucc 7))
  have pc : (p.image v).card = 4 := by
    rw [Finset.card_image_of_injective _ vinj]
    decide +kernel
  have qc : (q.image v).card = 4 := by
    rw [Finset.card_image_of_injective _ vinj]
    decide +kernel
  have pqc : ((p.image v) ∩ (q.image v)).card = 1 := by
    rw [← Finset.image_inter p q vinj, Finset.card_image_of_injective _ vinj]
    decide +kernel
  obtain ⟨pe, px⟩ := phi_eq_of_four h (x 7) (p.image v) ps.1 ps.2 pc
  obtain ⟨qe, qy⟩ := phi_eq_of_four h (y 7) (q.image v) qs.1 qs.2 qc
  have corner : ((cube (x 7)) ∩ (cube (y 7))).Nonempty :=
    (hm 7 7).mp (by unfold zero rowMasks; decide +kernel)
  have bad := phi_overlap h (x 7) (y 7) px qy corner
  rw [← pe, ← qe, pqc] at bad
  omega

#print axioms cube_bounds
#print axioms phi_overlap
#print axioms two_vertex_neighbor
#print axioms no_boxes
end ThreeIntersectionsCubeGap
