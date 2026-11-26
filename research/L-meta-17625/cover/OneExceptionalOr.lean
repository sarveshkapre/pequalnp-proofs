import RoutingThree

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_5869

namespace OneExceptionalOr
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- The routing argument of L-meta-5869 depends only on the existence of a unique
exceptional OR and the absence of centreless tops. There is no limit on dirty ANDs. -/
theorem routes (least : IsLeastAO G C) (top : TopForm G C)
    (empty : centreless G C = ∅) (one : (orN G C \ lam G C).card = 1)
    (nonempty : ∃ u v : Fin n, s(u, v) ∈ Ustar G C) :
    ∃ t : Fin n, ∀ u v : Fin n, s(u, v) ∈ Ustar G C →
      ∃ w : Fin n, (w = u ∨ w = v) ∧ (G.deleteEdges ↑(Ustar G C)).Adj t w ∧
        ∀ x : Fin n → Bool, x w = true → graphFun G ∅ x = false →
          ∃ S : Finset (Fin n), (S.card ≤ 1 ∨
            ∃ z : Fin n, ∀ y ∈ S, (G.deleteEdges ↑(Ustar G C)).Adj y z) ∧
            (∀ p q : Fin n, s(p, q) ∈ Ustar G C → p ∈ S ∨ q ∈ S) ∧
            ∀ y ∈ S, x y = false := by
  obtain ⟨u, v, he⟩ := nonempty
  obtain ⟨a, ha, b, j, hj, _, hr, _⟩ := residualTrace least top he
  obtain ⟨m, hm, hin, path⟩ := residualPath least.1 empty ha hj hr
  have only : orN G C \ lam G C = {m} := Finset.eq_singleton_iff_unique_mem.mpr
    ⟨hm, fun x hx => Finset.card_le_one.mp (by omega) x hx m hm⟩
  obtain ⟨t, ht⟩ := mixingRaw least.1 empty only hm ha path
  refine ⟨t, ?_⟩
  have hml := (orData hm).1
  have hmo := (orData hm).2.1
  have hlt := least.1.2.1 m hml _ hin
  have uniform (p q : Fin n) (hpq : s(p, q) ∈ Ustar G C) :
      gateVal n C j (pairInput p q) = true := by
    obtain ⟨a', ha', b', k, hk, _, hr', hv⟩ := residualTrace least top hpq
    obtain ⟨l, hl, hkin, _⟩ := residualPath least.1 empty ha' hk hr'
    rw [only, Finset.mem_singleton] at hl
    subst l
    have heq := singleJunkInput least.1 hm ⟨t, ht⟩ hj hk hin hkin
    rwa [heq]
  intro p q hpq
  obtain ⟨a', ha', b', k, hk, hav, hr', _⟩ := residualTrace least top hpq
  obtain ⟨l, hl, _, hp⟩ := residualPath least.1 empty ha' hk hr'
  rw [only, Finset.mem_singleton] at hl
  subst l
  obtain ⟨w, hw, hend⟩ := oppositeEndpoint least top empty only hm ha' hav hp
  have ht' : t ∈ side C a' b' :=
    reach_mem_orIn t (hp.trans (mem_orIn_reach t ht))
  refine ⟨w, hend, cleanAdj least.1 ha' b' ht' hw, ?_⟩
  intro x hx hf
  have hjx : gateVal n C j x = false := by
    apply Bool.eq_false_iff.mpr
    intro htrue
    have hmx : gateVal n C m x = true :=
      (val_or (n := n) (by simp) hml hmo).mpr ⟨_, hin, hlt, htrue⟩
    exact Bool.false_ne_true (hf.symm.trans (firingTop least.1 ha' hp hw x hmx hx))
  exact falseJunkCover least.1 top only hm x j (by omega) hj uniform hjx

/-- One exceptional OR and no centreless top allow at most one residual edge,
even with an unrestricted number of dirty AND gates. -/
theorem only_one_residual (bip : G.IsBipartite) (four : NoFourCycle G)
    (least : IsLeastAO G C) (top : TopForm G C) (empty : centreless G C = ∅)
    (one : (orN G C \ lam G C).card = 1) : (Ustar G C).card ≤ 1 := by
  apply ResidualRouting.card_le_one_from_routes bip four Finset.sdiff_subset
  rintro ⟨e, he⟩
  induction e using Sym2.inductionOn with | _ a b =>
  exact routes least top empty one ⟨a,b,he⟩

#print axioms OneExceptionalOr.only_one_residual
end OneExceptionalOr
