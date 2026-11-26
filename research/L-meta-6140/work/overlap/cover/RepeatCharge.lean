import ResidualDegree

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

namespace ResidualDegree

/-- A matching specified by choosing a different partner outside S uses two vertices per edge. -/
lemma matching_card {n : ℕ} (S : Finset (Fin n)) (f : S → Fin n)
    (inj : Function.Injective f) (outside : ∀ v, f v ∉ S) : 2*S.card ≤ n := by
  classical
  let T := Finset.univ.image f
  have dis : Disjoint S T := by
    refine Finset.disjoint_left.mpr ?_
    intro v hv ht
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp ht
    exact outside u hv
  have total := Finset.card_le_univ (s := S ∪ T)
  rw [Finset.card_union_of_disjoint dis] at total
  have size : T.card = S.card := by simp [T, Finset.card_image_of_injective _ inj]
  rw [size, Fintype.card_fin] at total; omega

/-- The total-size lower bound implies the wire-read inequality in the desk statement. -/
theorem repeat_of_size {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (pos : 0 < C.size) (k : ℕ)
    (bound : G.edgeFinset.card + k ≤ C.size + 1) :
    let uses := C.gates.flatMap Gate.inputs
    let inputs := uses.toFinset.filter fun w => w < n
    G.edgeFinset.card + k - inputs.card ≤ uses.length - uses.toFinset.card := by
  classical
  let uses := C.gates.flatMap Gate.inputs
  let inputs := uses.toFinset.filter fun w => w < n
  let gates := uses.toFinset.filter fun w => ¬ w < n
  change G.edgeFinset.card + k - inputs.card ≤ uses.length - uses.toFinset.card
  have parts : inputs.card + gates.card = uses.toFinset.card := Finset.card_filter_add_card_filter_not _
  have lengths (gs : List Gate) (two : ∀ g ∈ gs, g.inputs.length = 2) :
      (gs.flatMap Gate.inputs).length = 2 * gs.length := by
    induction gs with
    | nil => simp
    | cons g gs ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [two _ (by simp), ih (fun x h => two x (by simp [h]))]
      omega
  have slots : uses.length = 2*C.size := lengths _ ao.2.2
  have inner : gates ⊆ Finset.Ico n (n + C.size - 1) := by
    intro w hw
    obtain ⟨inUses, high⟩ := Finset.mem_filter.mp hw
    obtain ⟨g, hg, member⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp inUses)
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
    have h := ao.2.1 i hi w (by unfold gateAt; rw [List.getD_eq_getElem _ _ hi]; exact member)
    have l : i < C.size := hi
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have internal := Finset.card_le_card inner
  rw [Nat.card_Ico] at internal
  omega

/-- L-meta-17625's exact repeated-read bound on the order-three plane for ≤3 residual edges. -/
theorem plane_repeat_three (C : Circuit) (least : IsLeastAO plane C) (top : TopForm plane C)
    (three : (Ustar plane C).card ≤ 3) (S : Finset (Fin 26)) (f : S → Fin 26)
    (inj : Function.Injective f) (partners : ∀ v, f v ∉ S ∧ plane.Adj v.val (f v)) :
    let uses := C.gates.flatMap Gate.inputs
    let inputs := uses.toFinset.filter fun w => w < 26
    plane.edgeFinset.card + S.card - inputs.card ≤ uses.length - uses.toFinset.card := by
  have size := plane_three C least top three
  have m := matching_card S f inj (fun v => (partners v).1)
  apply repeat_of_size plane C least.1 (by omega)
  rw [plane_edges]
  omega

#print axioms ResidualDegree.plane_repeat_three

end ResidualDegree
