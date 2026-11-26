import SourceBudget
import CentreTransfer
import ThreeBranches

namespace GeneralThree
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.Outside.L_meta_7465_aux.Routing
open ResidualSourceBudget

abbrev matchingEdges {n : ℕ} (S : Finset (Fin n)) (f : S → Fin n) : Finset (Sym2 (Fin n)) :=
  Finset.univ.image fun v : S => s(v.val, f v)

/-- The size of a matching is at most an old cover plus the number of its edges
that were removed. All counts refer to the particular matching in the statement. -/
theorem matching_after_deletion {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Finset (Sym2 (Fin n))) (S : Finset (Fin n)) (f : S → Fin n)
    (inj : Function.Injective f) (partners : ∀ v, f v ∉ S ∧ G.Adj v.val (f v))
    (K : Finset (Fin n)) (cover : (G.deleteEdges ↑U).IsVertexCover (K : Set _)) :
    S.card ≤ K.card + ((matchingEdges S f) ∩ U).card := by
  classical
  let edge (v : S) := s(v.val, f v)
  let N : Finset S := Finset.univ.filter fun v => edge v ∈ U
  have nmem (v : S) : v ∈ N ↔ edge v ∈ U := by simp [N]
  have einj : Function.Injective edge := by
    intro v w same
    rcases Sym2.eq_iff.mp same with eq | eq
    · exact Subtype.ext eq.1
    · exact ((partners w).1 (eq.1 ▸ v.2)).elim
  have inter : N.image edge = (matchingEdges S f) ∩ U := by
    ext e
    constructor
    · rintro he
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp he
      exact Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩, (nmem v).mp hv⟩
    · intro m
      obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp m).1
      exact Finset.mem_image.mpr ⟨v,(nmem v).mpr (Finset.mem_inter.mp m).2,rfl⟩
  let L := K ∪ N.image Subtype.val
  let sel (v : S) := if v.val ∈ L then v.val else f v
  have hits (v : S) : sel v ∈ L := by
    dsimp [sel]
    split_ifs with m
    · exact m
    · have survive : edge v ∉ U := fun h => m (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨v, (nmem v).mpr h, rfl⟩))
      have covered := cover (SimpleGraph.deleteEdges_adj.mpr ⟨(partners v).2,survive⟩)
      exact Finset.mem_union_left _ (covered.resolve_left (fun h => m (Finset.mem_union_left _ h)))
  have unique : Function.Injective sel := by
    intro v w same
    dsimp [sel] at same
    split_ifs at same with hu hv hv
    · exact Subtype.ext same
    · exact ((partners w).1 (same ▸ v.property)).elim
    · exact ((partners v).1 (same.symm ▸ w.property)).elim
    · exact inj same
  have sub : Finset.univ.image sel ⊆ L := by
    intro x hx
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hx
    exact hits v
  have a := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  rw [Finset.card_image_of_injective _ unique,Finset.card_univ,Fintype.card_coe] at a
  have b := Finset.card_image_le (f := Subtype.val) (s := N)
  rw [←inter,Finset.card_image_of_injective _ einj]
  omega

/-- The actual repeated-read bound on the desk, with the chosen matching's size. -/
abbrev wireBound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (S : Finset (Fin n)) :=
  let uses := C.gates.flatMap Gate.inputs
  let inputs := uses.toFinset.filter fun w => w < n
  G.edgeFinset.card + S.card - inputs.card ≤ uses.length - uses.toFinset.card

/-- Every possible failure at three residual edges has exactly two dirty ANDs,
no centreless top, and exactly two eligible ORs. The matching in the failure
uses at least two of the three residual edges. -/
theorem remaining {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (four : NoFourCycle G) (edges : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (top : TopForm G C) (three : (Ustar G C).card = 3)
    (S : Finset (Fin n)) (f : S → Fin n) (inj : Function.Injective f)
    (partners : ∀ v, f v ∉ S ∧ G.Adj v.val (f v)) (failure : ¬ wireBound G C S) :
    (junk G C).card = 2 ∧ (centreless G C).card = 0 ∧ (orN G C \ lam G C).card = 2 ∧
      2 ≤ (matchingEdges S f ∩ Ustar G C).card := by
  classical
  have u : (Ustar G C).Nonempty := Finset.card_pos.mp (by omega)
  have has : (junk G C).Nonempty := by
    obtain ⟨e,he⟩ := u
    induction e using Sym2.ind with
    | h a b =>
      obtain ⟨_,_,_,j,hj,_⟩ := PEqualNP.Outside.L_meta_8005.residualTrace least top he
      exact ⟨j,hj⟩
  have jpos := Finset.card_pos.mpr has
  obtain ⟨j,mem⟩ := has
  have inside : j < C.size := (junkData mem).1
  have count := (PEqualNP.Outside.L_meta_1491 n G C four edges least top).1
  have unpaid : C.size + 1 < G.edgeFinset.card + S.card := by
    by_contra! enough
    exact failure (ResidualDegree.repeat_of_size G C least.1 (by omega) _ enough)
  have jtwo : 2 ≤ (junk G C).card := by
    by_contra! one
    obtain ⟨K,cover,paid⟩ := PEqualNP.Outside.L_meta_8103 n G C four edges least top u (by omega)
    have matchBound := ResidualDegree.matched_le_cover G S f inj partners K (fun _ _ h => cover _ _ h)
    omega
  obtain ⟨K,kc⟩ := ResidualDegree.min_cover_exists (G.deleteEdges ↑(Ustar G C))
  have old := (PEqualNP.Outside.L_meta_1491 n G C four edges least top).2 K kc
  let M := matchingEdges S f ∩ Ustar G C
  have m := matching_after_deletion G (Ustar G C) S f inj partners K kc.1
  change S.card ≤ K.card + M.card at m
  obtain h | ⟨_,cases⟩ := possible_obstructions four least top three jtwo M Finset.inter_subset_right
    (show (junk G C).card + 2*(centreless G C).card + (orN G C \ lam G C).card <
      (Ustar G C).card + M.card by omega)
  · exact h
  rcases cases with two | threeDirty | oneCentre
  · exact (failure (ResidualDegree.repeated_reads_three G C four edges least top
      (Finset.card_eq_zero.mp two.2.1) three (.inl ⟨two.1,two.2.2⟩) S f inj partners)).elim
  · exact (failure (ResidualDegree.repeated_reads_three G C four edges least top
      (Finset.card_eq_zero.mp threeDirty.2.1) three (.inr ⟨threeDirty.1,threeDirty.2.2⟩) S f inj partners)).elim
  · change (junk G C).card = 2 ∧ (centreless G C).card = 1 ∧ (orN G C \ lam G C).card = 1 at oneCentre
    exact (failure (CentreSeparation.repeat_charge four edges least top (Finset.card_pos.mp (by omega))
      (by omega) (by omega) inj partners)).elim

/-- In the surviving configuration, any failure uses all the slack in the
gate-count inequality and in the best graph cover. This also applies when the
matching contains all three residual edges. -/
theorem tight_if_failed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (four : NoFourCycle G) (edges : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (top : TopForm G C) (three : (Ustar G C).card = 3)
    (S : Finset (Fin n)) (f : S → Fin n) (inj : Function.Injective f)
    (partners : ∀ v, f v ∉ S ∧ G.Adj v.val (f v)) (failure : ¬ wireBound G C S) :
    S.card = (tops G C).card + 2 ∧
      C.size = G.edgeFinset.card + (tops G C).card ∧
      ∃ K : Finset (Fin n), PEqualNP.MetaComplexity.NestedCover.IsMinCover G K ∧ K.card = S.card := by
  classical
  obtain ⟨two,zero,ors,_⟩ := remaining G C four edges least top three S f inj partners failure
  have empty := Finset.card_eq_zero.mp zero
  obtain ⟨j,hj⟩ := Finset.card_pos.mp (show 0 < (junk G C).card by omega)
  have inside : j < C.size := (junkData hj).1
  have low : C.size + 1 < G.edgeFinset.card + S.card := by
    by_contra! h
    exact failure (ResidualDegree.repeat_of_size G C least.1 (by omega) _ h)
  have cnt := (PEqualNP.Outside.L_meta_1491 n G C four edges least top).1
  rw [empty,Finset.sdiff_empty,Finset.card_empty] at cnt
  obtain ⟨K,cover,small⟩ := ProtectedResiduals.cover_saves_one four least top empty (.inl (by omega))
  have matched := ResidualDegree.matched_le_cover G S f inj partners K cover
  have eq : K.card = S.card := by omega
  refine ⟨by omega,by omega,K,⟨cover,?_⟩,eq⟩
  intro K' covers'
  exact eq ▸ ResidualDegree.matched_le_cover G S f inj partners K' covers'

#print axioms tight_if_failed

#print axioms matching_after_deletion
#print axioms remaining
end GeneralThree
