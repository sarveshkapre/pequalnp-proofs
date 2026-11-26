import PathConclusion

namespace PathRemainder
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- In a hypothetical three-edge failure, no residual edge meets both members
of any vertex-disjoint pair of residual edges. This also applies to the two
disjoint matching edges whose existence is forced by the earlier counting bound. -/
theorem no_bridge (four : NoFourCycle G) (bip : G.IsBipartite)
    (least : IsLeastAO G C) (top : TopForm G C) (three : (Ustar G C).card = 3)
    (S : Finset (Fin n)) (f : S → Fin n) (inj : Function.Injective f)
    (partners : ∀ v, f v ∉ S ∧ G.Adj v.val (f v)) (failure : ¬ GeneralThree.wireBound G C S)
    {p q r : Sym2 (Fin n)} (pm : p ∈ Ustar G C) (qm : q ∈ Ustar G C) (rm : r ∈ Ustar G C)
    (disjoint : ∀ v : Fin n, v ∈ p → v ∉ q) :
    ¬ ((∃ b : Fin n, b ∈ p ∧ b ∈ r) ∧ ∃ c : Fin n, c ∈ q ∧ c ∈ r) := by
  classical
  rintro ⟨⟨b,bp,br⟩,c,cq,cr⟩
  obtain ⟨a,rfl⟩ := Sym2.mem_iff_exists.mp bp
  obtain ⟨d,rfl⟩ := Sym2.mem_iff_exists.mp cq
  have bc : b ≠ c := fun eq => disjoint b (Sym2.mem_mk_left _ _) (eq ▸ Sym2.mem_mk_left _ _)
  have bd : b ≠ d := fun eq => disjoint b (Sym2.mem_mk_left _ _) (eq ▸ Sym2.mem_mk_right _ _)
  have ac : a ≠ c := fun eq => disjoint a (Sym2.mem_mk_right _ _) (eq ▸ Sym2.mem_mk_left _ _)
  have ad : a ≠ d := fun eq => disjoint a (Sym2.mem_mk_right _ _) (eq ▸ Sym2.mem_mk_right _ _)
  have ba : b ≠ a := (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp pm).1).ne
  have cd : c ≠ d := (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp qm).1).ne
  obtain rfl := (Sym2.mem_and_mem_iff bc).mp ⟨br,cr⟩
  let e : Fin 4 → Fin n := ![a,b,c,d]
  have ei : Function.Injective e := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [e]
  have ab : s(a,b) ∈ Ustar G C := (Sym2.eq_swap ▸ pm)
  let Q := ({s(a,b),s(b,c),s(c,d)} : Finset (Sym2 (Fin n)))
  have sub : Q ⊆ Ustar G C := by
    intro u m
    simp only [Q,Finset.mem_insert,Finset.mem_singleton] at m
    rcases m with rfl|rfl|rfl <;> assumption
  have neq1 : s(a,b) ≠ s(b,c) := by simp [ba.symm,ac]
  have neq2 : s(a,b) ≠ s(c,d) := by simp [ac,ad]
  have neq3 : s(b,c) ≠ s(c,d) := by simp [bc,bd]
  have count : Q.card = 3 := by simp [Q,neq1,neq2,neq3]
  have eq : Q = Ustar G C := Finset.eq_of_subset_of_card_le sub (le_of_eq (three.trans count.symm))
  have pth : PathGeometry.pathEdges e = Q := by
    ext u
    simp only [PathGeometry.pathEdges,Finset.mem_image,Finset.mem_univ,true_and,Q,
      Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨j,rfl⟩; fin_cases j <;> simp [e]
    · rintro (rfl|rfl|rfl)
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
      · exact ⟨2,rfl⟩
  exact failure (PathConclusion.path_bound four bip least top e ei (eq.symm.trans pth.symm) S f inj partners)

/-- Every failure with exactly three residual edges has an edge sharing no
vertex with either of the other two. Thus every connected three-edge case
satisfies the matching bound. -/
theorem isolated_edge (four : NoFourCycle G) (bip : G.IsBipartite)
    (least : IsLeastAO G C) (top : TopForm G C) (three : (Ustar G C).card = 3)
    (S : Finset (Fin n)) (f : S → Fin n) (inj : Function.Injective f)
    (partners : ∀ v, f v ∉ S ∧ G.Adj v.val (f v)) (failure : ¬ GeneralThree.wireBound G C S) :
    ∃ p ∈ Ustar G C, ∀ q ∈ Ustar G C, q ≠ p → ∀ v : Fin n, v ∈ p → v ∉ q := by
  classical
  have edges : G.edgeFinset.Nonempty := by
    obtain ⟨e,m⟩ := Finset.card_pos.mp (show 0 < (Ustar G C).card by omega)
    exact ⟨e,(Finset.mem_sdiff.mp m).1⟩
  have size := (GeneralThree.remaining G C four edges least top three S f inj partners failure).2.2.2
  obtain ⟨p,pm,q,qm,pq⟩ := Finset.one_lt_card.mp size
  obtain ⟨mp,pu⟩ := Finset.mem_inter.mp pm
  obtain ⟨mq,qu⟩ := Finset.mem_inter.mp qm
  have disj : ∀ v : Fin n, v ∈ p → v ∉ q := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp mp
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp mq
    have ij : i ≠ j := fun h => pq (h ▸ rfl)
    intro v vi vj
    rcases Sym2.mem_iff.mp vi with rfl|rfl <;> rcases Sym2.mem_iff.mp vj with eq|eq
    · exact ij (Subtype.ext eq)
    · exact (partners j).1 (eq ▸ i.2)
    · exact (partners i).1 (eq.symm ▸ j.2)
    · exact ij (inj eq)
  have small : ({p,q} : Finset _).card < (Ustar G C).card := by simp [pq,three]
  obtain ⟨r,ru,apart⟩ := Finset.exists_mem_notMem_of_card_lt_card small
  have rp : r ≠ p := fun h => apart (by simp [h])
  have rq : r ≠ q := fun h => apart (by simp [h])
  have sub : ({p,q,r} : Finset _) ⊆ Ustar G C := by
    intro x mx
    simp only [Finset.mem_insert,Finset.mem_singleton] at mx
    rcases mx with rfl|rfl|rfl <;> assumption
  have cover : Ustar G C = {p,q,r} := (Finset.eq_of_subset_of_card_le sub
    (by simp [three,pq,rp.symm,rq.symm])).symm
  have stop := no_bridge four bip least top three S f inj partners failure pu qu ru disj
  by_cases overlap : ∃ v : Fin n, v ∈ p ∧ v ∈ r
  · refine ⟨q,qu,?_⟩
    intro x xm xq v vq vx
    rw [cover] at xm
    rcases (show x=p ∨ x=q ∨ x=r by simpa only [Finset.mem_insert,Finset.mem_singleton] using xm) with rfl|rfl|rfl
    · exact disj v vx vq
    · exact xq rfl
    · exact stop ⟨overlap,v,vq,vx⟩
  · refine ⟨p,pu,?_⟩
    intro x xm xp v vp vx
    rw [cover] at xm
    rcases (show x=p ∨ x=q ∨ x=r by simpa only [Finset.mem_insert,Finset.mem_singleton] using xm) with rfl|rfl|rfl
    · exact xp rfl
    · exact disj v vp vx
    · exact overlap ⟨v,vp,vx⟩

/-- The matching bound holds whenever each of the three residual edges
shares a vertex with another residual edge. -/
theorem bound_without_isolated_edge (four : NoFourCycle G) (bip : G.IsBipartite)
    (least : IsLeastAO G C) (top : TopForm G C) (three : (Ustar G C).card = 3)
    (touches : ∀ p ∈ Ustar G C, ∃ q ∈ Ustar G C, q ≠ p ∧ ∃ v : Fin n, v ∈ p ∧ v ∈ q)
    (S : Finset (Fin n)) (f : S → Fin n) (inj : Function.Injective f)
    (partners : ∀ v, f v ∉ S ∧ G.Adj v.val (f v)) : GeneralThree.wireBound G C S := by
  by_contra fail
  obtain ⟨p,pm,alone⟩ := isolated_edge four bip least top three S f inj partners fail
  obtain ⟨q,qm,qp,v,vp,vq⟩ := touches p pm
  exact alone q qm qp v vp vq

#print axioms bound_without_isolated_edge
#print axioms no_bridge
#print axioms isolated_edge
end PathRemainder
