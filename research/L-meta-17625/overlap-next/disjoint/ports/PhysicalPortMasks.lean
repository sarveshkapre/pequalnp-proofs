import P4Ports

namespace PhysicalPortMasks
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
attribute [local instance] gateOpDecEq

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- Canonical nonempty exceptional ORs reaching this operand through ORs.
The same set is used on every input. It may have multiple members. -/
noncomputable def sources (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (g : ℕ) (p : Fin 2) : Finset ℕ := by
  classical exact (orN G C \ lam G C).filter (fun k =>
    (orIn n C (n+k)).Nonempty ∧ OrReaches n C (opnd C g p) k)

theorem source_data {g k : ℕ} {p : Fin 2} (m : k ∈ sources G C g p) :
    k ∈ orN G C \ lam G C ∧ (orIn n C (n+k)).Nonempty ∧
    OrReaches n C (opnd C g p) k ∧ orIn n C (n+k) ⊆ side (n := n) C g p := by
  classical
  obtain ⟨mem,raw,path⟩ := Finset.mem_filter.mp m
  exact ⟨mem,raw,path,fun t ht => reach_mem_orIn t
    ((orReaches_reach k _ path).1.trans (mem_orIn_reach t ht))⟩

theorem source_active (ao : IsAO2 n C) {g k : ℕ} {p : Fin 2}
    (len : g < C.gates.length) (under : SwitchCore.belowAnd n C (opnd C g p))
    (mem : k ∈ sources G C g p) : k ∈ P4Ports.active G C ∧ k < g := by
  classical
  obtain ⟨a,la,hand,b,context⟩ := under
  obtain ⟨exc,_,reaches,_⟩ := source_data mem
  have path := (orReaches_reach k _ reaches).1
  have le := orStep_le path
  have bound := opndBound ao len p
  exact ⟨Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨exc,a,la,hand,b,context.trans path⟩),by omega⟩

/-- Fixed decomposition of a real nonempty top operand. A raw-input union
and every eligible exceptional OR reaching the operand suffice on all inputs. -/
theorem port_value (ao : IsAO2 n C) {g : ℕ} (len : g < C.gates.length) (p : Fin 2)
    (raw : (side (n := n) C g p).Nonempty) (x : Fin n → Bool) :
    val C (List.ofFn x) (opnd C g p) = true ↔
      (∃ u ∈ side (n := n) C g p, x u = true) ∨
        ∃ k ∈ sources G C g p, gateVal n C k x = true := by
  have bound := opndBound ao len p
  exact nonemptyPortValue (G := G) ao x _ (by omega) raw

theorem center_source (g : tops G C) (p : Fin 2) (z : Fin n)
    (center : side (n := n) C g p = {z}) {k : ℕ} (mem : k ∈ sources G C g p) :
    orIn n C (n+k) = {z} := by
  obtain ⟨_,ne,_,sub⟩ := source_data mem
  rw [center] at sub
  exact Finset.eq_of_subset_of_card_le sub (by simpa using Finset.card_pos.mpr ne)

/-- A source can promote at most one chosen center. -/
theorem center_owner (p : tops G C → Fin 2) (z : tops G C → Fin n) (inj : Function.Injective z)
    (centers : ∀ g : tops G C, side (n := n) C g (p g) = {z g})
    {a b : tops G C} {k : ℕ} (ka : k ∈ sources G C a (p a)) (kb : k ∈ sources G C b (p b)) :
    a = b := by
  apply inj
  exact Finset.singleton_inj.mp ((center_source a _ _ (centers a) ka).symm.trans
    (center_source b _ _ (centers b) kb))

/-- A globally nonempty exceptional OR cannot be used on opposite ports of
the same clean top, even if both of its projections have empty raw support. -/
theorem disjoint_sources (ao : IsAO2 n C) (g : tops G C) (p : Fin 2) :
    Disjoint (sources G C g p) (sources G C g (1-p)) := by
  apply Finset.disjoint_left.mpr
  intro k hk ht
  obtain ⟨_,⟨w,hw⟩,_,left⟩ := source_data hk
  obtain ⟨_,_,_,right⟩ := source_data ht
  exact (cleanAdj ao g.2 p (left hw) (right hw)).ne rfl

/-- General charged-port decomposition. The predicate can test the image of
a raw support on any selected vertices. Knowing it for literal wires and
ordinary ORs suffices. Direct charged sources and nonlinear data are retained. -/
theorem port_law (ao : IsAO2 n C) (top : TopForm G C) (P : Finset (Fin n) → Prop)
    (literal : ∀ v, P {v}) (ordinary : ∀ k ∈ lam G C, P (orIn n C (n+k)))
    {g : ℕ} (hg : g ∈ P4Ports.active G C) (p : Fin 2) :
    (∃ k ∈ P4Ports.active G C, k < g ∧ opnd C g p = n+k) ∨
      (side (n := n) C g p).Nonempty ∧ P (side (n := n) C g p) ∧
      (∀ k ∈ sources G C g p, k ∈ P4Ports.active G C ∧ k < g ∧ k ∈ orN G C \ lam G C ∧
        (orIn n C (n+k)).Nonempty ∧ orIn n C (n+k) ⊆ side (n := n) C g p) ∧
      ∀ x : Fin n → Bool, val C (List.ofFn x) (opnd C g p) = true ↔
        (∃ u ∈ side (n := n) C g p, x u = true) ∨
          ∃ k ∈ sources G C g p, gateVal n C k x = true := by
  classical
  have len := P4Ports.active_length hg
  have under := P4Ports.under_port ao hg p
  have bound := opndBound ao len p
  by_cases direct : ∃ k ∈ P4Ports.active G C, k < g ∧ opnd C g p = n+k
  · exact .inl direct
  rcases P4Ports.port_law ao top ∅ (by simp) hg p with already|⟨raw,_,_⟩
  · exact (direct already).elim
  right
  refine ⟨raw,?_,?_,port_value ao len p raw⟩
  · let w := opnd C g p
    by_cases input : w < n
    · let v : Fin n := ⟨w,input⟩
      have eq : side (n := n) C g p = {v} := by
        apply Finset.eq_of_subset_of_card_le _ (by simpa using Finset.card_pos.mpr raw)
        intro u hu
        apply Finset.mem_singleton.mpr
        rcases Relation.ReflTransGen.cases_head (mem_orIn_reach u hu) with same|⟨j,step,_⟩
        · exact Fin.ext same.symm
        · obtain ⟨k,_,same,_,_,_⟩ := step
          change w = n+k at same
          omega
      exact eq ▸ literal v
    · obtain ⟨k,wire⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
      have small : k < C.gates.length := by dsimp [w] at wire; omega
      have ne : (orIn n C (n+k)).Nonempty := by rw [← wire]; exact raw
      have reg : k ∈ lam G C := by
        by_contra outside
        obtain ⟨t,mt⟩ := ne
        have hop : (gateAt C k).op = GateOp.or := by
          rcases ao.1 _ (gateAt_mem small) with h|h
          · rw [andRawEmpty h] at mt; exact ((Finset.notMem_empty _) mt).elim
          · exact h
        have dirty : ¬ BelowF G C k := by
          intro below
          have on := reach_var_val (pairInput t t) _ t (mem_orIn_reach t mt) (pairInput_left t t)
          exact G.irrefl ((graphFun_pair G t t).mp (below _ on))
        have exc : k ∈ orN G C \ lam G C := Finset.mem_sdiff.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr small,hop,dirty⟩,outside⟩
        obtain ⟨a,la,hand,b,context⟩ := under
        have act : k ∈ P4Ports.active G C := Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨exc,a,la,hand,b,wire ▸ context⟩)
        exact direct ⟨k,act,(by dsimp [w] at wire; omega),wire⟩
      change P (orIn n C w)
      rw [wire]; exact ordinary _ reg
  · intro k mem
    obtain ⟨active,lt⟩ := source_active ao len under mem
    obtain ⟨exc,ne,_,sub⟩ := source_data mem
    exact ⟨active,lt,exc,ne,sub⟩

#print axioms port_law
#print axioms center_owner
#print axioms disjoint_sources
end PhysicalPortMasks
