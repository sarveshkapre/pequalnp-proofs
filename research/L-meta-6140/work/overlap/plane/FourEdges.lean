import RepeatCharge
import RoutingThree
import PEqualNP.Outside.L_meta_8567

namespace PlaneFour
open ResidualDegree PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

abbrev I := Fin 13
def pt (i : I) : Fin 26 := i.castAdd 13
def ln (i : I) : Fin 26 := Fin.natAdd 13 i
def edge (p l : I) : Sym2 (Fin 26) := s(pt p, ln l)
def diff : Fin 4 → I := ![0, 1, 3, 9]
def incident (p l : I) := p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
instance (p l : I) : Decidable (incident p l) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

private theorem adj_test : ∀ p l, incident p l ↔ plane.Adj (pt p) (ln l) := by decide
private theorem color_test : ∀ u v, plane.Adj u v → (u.val < 13 ↔ ¬v.val < 13) := by decide

theorem plane_bipartite : plane.IsBipartite := by
  apply SimpleGraph.IsBipartiteWith.isBipartite (s := {u | u.val < 13}) (t := {u | ¬ u.val < 13})
  constructor
  · exact Set.disjoint_left.mpr (fun _ hu hv => hv hu)
  · intro u v h
    have c := color_test u v h
    by_cases a : u.val < 13
    · exact Or.inl ⟨a,c.mp a⟩
    · exact Or.inr ⟨a,by_contra fun b => a (c.mpr b)⟩

private theorem edge_inj {p l q m : I} (h : edge p l = edge q m) : p = q ∧ l = m := by
  rcases Sym2.eq_iff.mp h with h | h
  · exact ⟨Fin.ext (congrArg (fun x : Fin 26 => x.val) h.1), Fin.ext (by have := congrArg Fin.val h.2; simp [ln] at this; omega)⟩
  · have hh := congrArg Fin.val h.1
    simp [pt,ln] at hh
    omega

/-- Five matchings, before cyclic relabeling. Coordinates are point and line labels 0–12. -/
def bank : Fin 5 → I → I := ![
  ![4,0,2,3,1,5,6,7,8,9,10,11,12],
  ![10,1,2,3,4,5,6,7,8,0,9,11,12],
  ![12,1,2,0,4,5,6,7,8,9,10,11,3],
  ![4,1,2,0,3,5,6,7,8,9,10,11,12],
  ![10,0,1,2,3,4,5,11,12,6,7,8,9]]

private theorem bank_inj : ∀ j, Function.Injective (bank j) := by
  change ∀ j a b, bank j a = bank j b → a = b
  decide
private theorem bank_valid : ∀ j p t, incident (p+t) (bank j p+t) := by decide
private theorem base_valid : ∀ i p, incident p (p-diff i) := by decide
private theorem diff_inj : Function.Injective diff := by decide +revert

/-- In normalized coordinates the two exceptions are a star around point zero or line zero. -/
private theorem escapes : ∀ a b c : I,
    (a = 0 ∧ b = 0 ∧ c = 0) ∨ (a = 1 ∧ b = 3 ∧ c = 9) ∨
    ∃ j, bank j 0 ≠ 0 ∧ bank j a ≠ a-1 ∧ bank j b ≠ b-3 ∧ bank j c ≠ c-9 := by decide

private theorem cov_of_matching (U : Finset (Sym2 (Fin 26))) (K : Finset (Fin 26))
    (cov : (plane.deleteEdges ↑U).IsVertexCover (K : Set _))
    (f : I → I) (inj : Function.Injective f) (ok : ∀ i, incident i (f i))
    (avoid : ∀ i, edge i (f i) ∉ U) : 13 ≤ K.card := by
  classical
  let sel (i : I) : Fin 26 := if pt i ∈ K then pt i else ln (f i)
  have mem (i : I) : sel i ∈ K := by
    have hit := cov (SimpleGraph.deleteEdges_adj.mpr ⟨(adj_test i _).mp (ok i),avoid i⟩)
    simp only [sel, apply_ite (· ∈ K)]
    split <;> rename_i cond
    · exact cond
    · exact hit.resolve_left cond
  let pick (i : I) : K := ⟨sel i, mem i⟩
  have single : Function.Injective pick := by
    intro a b eq
    have h : sel a = sel b := congrArg Subtype.val eq
    simp only [sel] at h
    split at h <;> split at h
    · exact Fin.ext (congrArg (fun x : Fin 26 => x.val) h)
    · have := congrArg Fin.val h; simp [pt, ln] at this; omega
    · have := congrArg Fin.val h; simp [pt, ln] at this; omega
    · apply inj
      apply Fin.ext
      have := congrArg Fin.val h; simp [ln] at this; omega
  simpa using Fintype.card_le_of_injective pick single

/-- Four incidences can destroy every perfect matching only if all four contain one vertex. -/
theorem four_cover (U : Finset (Sym2 (Fin 26))) (size : U.card ≤ 4)
    (nonstar : ¬ ∃ v : Fin 26, ∀ e ∈ U, v ∈ e)
    (K : Finset (Fin 26)) (cov : (plane.deleteEdges ↑U).IsVertexCover (K : Set _)) : 13 ≤ K.card := by
  classical
  by_contra! short
  have blocked (i : Fin 4) : ∃ p, edge p (p-diff i) ∈ U := by
    by_contra! avoid
    exact (Nat.not_le_of_lt short) (cov_of_matching U K cov (· - diff i)
      (fun _ _ h => sub_left_inj.mp h) (base_valid i) avoid)
  choose p hp using blocked
  let e (i : Fin 4) := edge (p i) (p i - diff i)
  have inject : Function.Injective e := by
    intro i j h
    obtain ⟨same, other⟩ := edge_inj h
    rw [same] at other
    exact diff_inj (sub_right_inj.mp other)
  have hsub : Finset.univ.image e ⊆ U := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact hp i
  have heq : U = Finset.univ.image e := (Finset.eq_of_subset_of_card_le hsub (by
    simpa [Finset.card_image_of_injective _ inject] using size)).symm
  let t := p 0
  rcases escapes (p 1-t) (p 2-t) (p 3-t) with same | same | ⟨j,h0,h1,h2,h3⟩
  · apply nonstar
    refine ⟨pt t, ?_⟩
    intro v hv
    rw [heq] at hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    have all : ∀ i, p i = t := by
      intro i; fin_cases i
      · rfl
      · exact sub_eq_zero.mp same.1
      · exact sub_eq_zero.mp same.2.1
      · exact sub_eq_zero.mp same.2.2
    dsimp [e,edge]; rw [all i]; exact Sym2.mem_mk_left _ _
  · apply nonstar
    refine ⟨ln t, ?_⟩
    intro v hv
    rw [heq] at hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    have all : ∀ i, p i - diff i = t := by
      intro i; fin_cases i
      · simp [diff,t]
      · change p 1-1=t; rw [sub_eq_iff_eq_add.mp same.1]; abel
      · change p 2-3=t; rw [sub_eq_iff_eq_add.mp same.2.1]; abel
      · change p 3-9=t; rw [sub_eq_iff_eq_add.mp same.2.2]; abel
    dsimp [e,edge]; rw [all i]; exact Sym2.mem_mk_right _ _
  · let f (x : I) := bank j (x-t)+t
    apply (Nat.not_le_of_lt short) (cov_of_matching U K cov f ?_ ?_ ?_)
    · intro x y h
      exact sub_left_inj.mp (bank_inj j (add_right_cancel h))
    · intro x
      simpa [f] using bank_valid j (x-t) t
    · intro x h
      rw [heq] at h
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp h
      obtain ⟨rfl,he⟩ := edge_inj hi
      have bad : bank j (p i-t) = p i-t-diff i := by
        dsimp [f] at he
        have ha := congrArg (fun (w : I) => w-t) he
        simp only [add_sub_cancel_right] at ha
        calc
          _ = p i - diff i - t := ha.symm
          _ = _ := by abel
      fin_cases i
      · exact h0 (by simpa [diff,t] using bad)
      · exact h1 bad
      · exact h2 bad
      · exact h3 bad

/-- A minimum top-form circuit with four residual incidences spread over more than
one star needs at least 64 gates, for every wiring of its ANDs and ORs. -/
theorem four_nonstar_size (C : Circuit) (least : IsLeastAO plane C) (top : TopForm plane C)
    (four : (Ustar plane C).card = 4) (nonstar : ¬ ∃ v : Fin 26, ∀ e ∈ Ustar plane C, v ∈ e) :
    64 ≤ C.size := by
  classical
  have edges : plane.edgeFinset.Nonempty := Finset.card_pos.mp (by rw [plane_edges]; decide)
  have u : (Ustar plane C).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨count,small⟩ := PEqualNP.Outside.L_meta_1491 26 plane C plane_four edges least top
  rw [plane_edges] at count
  by_cases singleton : (junk plane C).card = 1
  · obtain ⟨K,c,paid⟩ := PEqualNP.Outside.L_meta_8103 26 plane C plane_four edges least top u singleton
    have cover : (plane.deleteEdges ↑(Ustar plane C)).IsVertexCover (K : Set _) :=
      fun _ _ h => c _ _ (SimpleGraph.deleteEdges_adj.mp h).1
    have := four_cover _ four.le nonstar K cover
    omega
  · obtain ⟨K,kc⟩ := min_cover_exists (plane.deleteEdges ↑(Ustar plane C))
    have := four_cover _ four.le nonstar K kc.1
    have := small K kc
    have pos : (junk plane C).Nonempty := by
      obtain ⟨e,he⟩ := u
      induction e using Sym2.ind with
      | h a b =>
        obtain ⟨_,_,_,j,hj,_⟩ := PEqualNP.Outside.L_meta_8005.residualTrace least top he
        exact ⟨j,hj⟩
    have j := Finset.card_pos.mpr pos
    have := ResidualRouting.two_edges_require_four C plane_bipartite plane_four edges least top
      (by omega) (by omega)
    omega

/-- Any exact-fan-in-two circuit of at most 63 gates for the whole plane would
yield a least top-form circuit with a full four-edge star or five or more residual edges. -/
theorem small_plane_obstruction (C : Circuit) (ao : IsAO2 26 C)
    (computes : circuitFun 26 C = graphFun plane ∅) (size : C.size ≤ 63) :
    ∃ D, IsLeastAO plane D ∧ TopForm plane D ∧ D.size ≤ C.size ∧
      (5 ≤ (Ustar plane D).card ∨
        ((Ustar plane D).card = 4 ∧ ∃ v : Fin 26, ∀ e ∈ Ustar plane D, v ∈ e)) := by
  classical
  have edges : plane.edgeFinset.Nonempty := Finset.card_pos.mp (by rw [plane_edges]; decide)
  obtain ⟨D,least,top,bound⟩ := PEqualNP.Outside.L_meta_8567 26 plane C edges ao computes
  refine ⟨D,least,top,bound,?_⟩
  by_cases five : 5 ≤ (Ustar plane D).card
  · exact Or.inl five
  right
  have four : (Ustar plane D).card = 4 := by
    by_contra! n
    have := plane_three D least top (by omega)
    omega
  refine ⟨four,?_⟩
  by_contra no
  have := four_nonstar_size D least top four no
  omega

#print axioms four_cover
#print axioms small_plane_obstruction
end PlaneFour
