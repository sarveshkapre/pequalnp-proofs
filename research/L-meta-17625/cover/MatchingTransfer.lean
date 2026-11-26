import RepeatCharge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

namespace ResidualDegree

/-- Distinct disjoint pairs require distinct slots in every vertex cover. -/
theorem matched_le_cover {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (f : S → Fin n) (inj : Function.Injective f)
    (partners : ∀ v, f v ∉ S ∧ G.Adj v.val (f v)) (K : Finset (Fin n))
    (cover : G.IsVertexCover (K : Set _)) : S.card ≤ K.card := by
  classical
  let choose (v : S) := if v.val ∈ K then v.val else f v
  have hits (v : S) : choose v ∈ K := by
    dsimp [choose]; split_ifs with h
    · exact h
    · exact (cover (partners v).2).resolve_left h
  have unique : Function.Injective choose := by
    intro u v eq
    dsimp [choose] at eq
    split_ifs at eq with hu hv hv
    · exact Subtype.ext eq
    · exact ((partners v).1 (eq ▸ u.property)).elim
    · exact ((partners u).1 (eq.symm ▸ v.property)).elim
    · exact inj eq
  have sub : Finset.univ.image choose ⊆ K := by
    intro x hx; obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hx; exact hits u
  have count := Finset.card_le_card sub
  simpa only [Finset.card_image_of_injective _ unique, Finset.card_univ,
    Fintype.card_coe] using count

/-- Transfer any structural obstruction to an extremal vertex cover into the exact wire inequality.
Here the resource sum is at least twice the residual-edge count minus one. -/
theorem transfer_extremal {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (four : NoFourCycle G) (edges : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (top : TopForm G C) (noCentreless : centreless G C = ∅)
    (cost : 2*(Ustar G C).card ≤ (junk G C).card + (orN G C \ lam G C).card + 1)
    (cannot : (∀ K : Finset (Fin n), G.IsVertexCover (K : Set _) →
      (tops G C).card + (Ustar G C).card ≤ K.card) → False)
    (positive : 0 < C.size)
    (S : Finset (Fin n)) (f : S → Fin n) (inj : Function.Injective f)
    (partners : ∀ v, f v ∉ S ∧ G.Adj v.val (f v)) :
    let uses := C.gates.flatMap Gate.inputs
    let inputs := uses.toFinset.filter fun w => w < n
    G.edgeFinset.card + S.card - inputs.card ≤ uses.length - uses.toFinset.card := by
  apply repeat_of_size G C least.1 positive
  have count := (PEqualNP.Outside.L_meta_1491 n G C four edges least top).1
  simp only [noCentreless, Finset.sdiff_empty, Finset.card_empty, Nat.mul_zero, Nat.add_zero] at count
  by_contra! failure
  apply cannot
  intro K cover
  have matchBound := matched_le_cover G S f inj partners K cover
  omega

/-- The two three-edge branches use the same transfer. The structural premise is
supplied by the graph-independent routing theorem in the companion file. -/
theorem transfer_three {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (four : NoFourCycle G) (edges : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (top : TopForm G C) (noCentreless : centreless G C = ∅)
    (three : (Ustar G C).card = 3)
    (cases : ((junk G C).card = 2 ∧ (orN G C \ lam G C).card = 3) ∨
      ((junk G C).card = 3 ∧ (orN G C \ lam G C).card = 2))
    (limits : (∀ K : Finset (Fin n), G.IsVertexCover (K : Set _) →
      (tops G C).card + (Ustar G C).card ≤ K.card) →
      (Ustar G C).card ≤ (junk G C).card ∧
        ((junk G C).card ≤ 3 → (orN G C \ lam G C).card ≤ 2 → (Ustar G C).card ≤ 2))
    (S : Finset (Fin n)) (f : S → Fin n) (inj : Function.Injective f)
    (partners : ∀ v, f v ∉ S ∧ G.Adj v.val (f v)) :
    let uses := C.gates.flatMap Gate.inputs
    let inputs := uses.toFinset.filter fun w => w < n
    G.edgeFinset.card + S.card - inputs.card ≤ uses.length - uses.toFinset.card := by
  have jbound : (junk G C).card ≤ C.size := Finset.card_le_card
    (show junk G C ⊆ Finset.range C.size from Finset.filter_subset _ _) |>.trans_eq (Finset.card_range _)
  apply transfer_extremal G C four edges least top noCentreless (by omega) _ (by omega) S f inj partners
  intro extreme
  obtain ⟨low, high⟩ := limits extreme
  rcases cases with h | h
  · omega
  · have := high (by omega) (by omega); omega

#print axioms ResidualDegree.transfer_three

end ResidualDegree
