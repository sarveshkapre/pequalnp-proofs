import SwitchCore

/-! Project a circuit onto a fixed set of vertices. A charged gate reads either an
earlier charged wire, or a raw literal and some earlier charged OR outputs.
The literal may vanish under the projection. -/
namespace P4Ports
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
attribute [local instance] gateOpDecEq

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- All dirty ANDs and every exceptional OR in the OR cone of a real AND operand. -/
noncomputable def active (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) : Finset ℕ := by
  classical
  exact junk G C ∪ (orN G C \ lam G C).filter fun h => SwitchCore.belowAnd n C (n+h)

theorem active_length {g : ℕ} (m : g ∈ active G C) : g < C.gates.length := by
  classical
  rcases Finset.mem_union.mp m with j | ex
  · exact (junkData j).1
  · exact (orData (Finset.mem_filter.mp ex).1).1

theorem under_port (ao : IsAO2 n C) {g : ℕ} (m : g ∈ active G C) (i : Fin 2) :
    SwitchCore.belowAnd n C (opnd C g i) := by
  classical
  rcases Finset.mem_union.mp m with j | ex
  · exact ⟨g,(junkData j).1,(junkData j).2.1,i,.refl⟩
  · obtain ⟨elig,a,len,hand,b,path⟩ := Finset.mem_filter.mp ex
    have hop : OrStep n C (n+g) (opnd C g i) := ⟨g,(orData elig).1,rfl,(orData elig).2.1,
      opndMem ao (orData elig).1 i,opndBound ao (orData elig).1 i⟩
    exact ⟨a,len,hand,b,path.tail hop⟩

/-- Every globally raw-nonempty internal wire is an OR outside the target function.
If it is not exceptional, it belongs to Lambda. -/
private theorem raw_or {g : ℕ} (ao : IsAO2 n C) (len : g < C.gates.length)
    (raw : (orIn n C (n+g)).Nonempty) : g ∈ orN G C := by
  rcases raw with ⟨t,mt⟩
  have hop : (gateAt C g).op = GateOp.or := by
    rcases ao.1 _ (gateAt_mem len) with hand | hor
    · rw [andRawEmpty hand] at mt; exact ((Finset.notMem_empty _) mt).elim
    · exact hor
  have outside : ¬ BelowF G C g := by
    intro below
    have on := reach_var_val (pairInput t t) _ t (mem_orIn_reach t mt) (pairInput_left t t)
    exact G.irrefl ((graphFun_pair G t t).mp (below _ on))
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr len,hop,outside⟩

/-- Each physical operand of a charged gate is an earlier charged wire, or a
globally nonempty raw port with at most one projected literal plus a fixed set
of earlier nonempty exceptional ORs. Their raw supports stay inside the port
and the same choices of wires work on all inputs. -/
theorem port_law (ao : IsAO2 n C) (top : TopForm G C) (V : Finset (Fin n))
    (thin : ∀ k ∈ lam G C, ((orIn n C (n+k)) ∩ V).card ≤ 1)
    {g : ℕ} (hg : g ∈ active G C) (i : Fin 2) :
    (∃ k ∈ active G C, k < g ∧ opnd C g i = n+k) ∨
      (side (n := n) C g i).Nonempty ∧ ((side (n := n) C g i) ∩ V).card ≤ 1 ∧
      ∃ K : Finset ℕ, (∀ k ∈ K, k ∈ active G C ∧ k < g ∧ k ∈ orN G C \ lam G C ∧
        (orIn n C (n+k)).Nonempty ∧ orIn n C (n+k) ⊆ side C g i) ∧
      ∀ x : Fin n → Bool, val C (List.ofFn x) (opnd C g i) = true ↔
        (∃ u ∈ side (n := n) C g i, x u = true) ∨ ∃ k ∈ K, gateVal n C k x = true := by
  classical
  have gl := active_length hg
  have bound := opndBound ao gl i
  obtain ⟨a,la,hand,b,context⟩ := under_port ao hg i
  let w := opnd C g i
  have ac (k : ℕ) (ex : k ∈ orN G C \ lam G C)
      (kd : Relation.ReflTransGen (OrStep n C) w (n+k)) : k ∈ active G C :=
    Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ex,a,la,hand,b,context.trans kd⟩)
  by_cases direct : ∃ k ∈ active G C, k < g ∧ opnd C g i = n+k
  · exact .inl direct
  right
  have raw : (side (n := n) C g i).Nonempty := by
    by_contra z
    obtain ⟨k,wire,j | e⟩ := emptyPortSource ao top la hand context
      (Finset.not_nonempty_iff_eq_empty.mp z)
    · exact direct ⟨k,Finset.mem_union_left _ j,by omega,wire⟩
    · exact direct ⟨k,ac k e (wire ▸ Relation.ReflTransGen.refl),by omega,wire⟩
  have little : ((side (n := n) C g i) ∩ V).card ≤ 1 := by
    by_cases inp : w < n
    · apply Finset.card_le_one.mpr
      intro u hu v hv
      have num (t : Fin n) (m : t ∈ side (n := n) C g i) : t.val = w := by
        rcases Relation.ReflTransGen.cases_head (mem_orIn_reach t m) with eq | ⟨q,step,_⟩
        · exact eq.symm
        · obtain ⟨j,_,eq,_,_,_⟩ := step; change w = n+j at eq; omega
      exact Fin.ext ((num u (Finset.mem_inter.mp hu).1).trans (num v (Finset.mem_inter.mp hv).1).symm)
    · obtain ⟨k,wire⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
      have len : k < C.gates.length := by dsimp [w] at wire; omega
      have raw' : (orIn n C (n+k)).Nonempty := by rw [← wire]; exact raw
      have regular : k ∈ lam G C := by
        by_contra h
        have act := ac k (Finset.mem_sdiff.mpr ⟨raw_or ao len raw',h⟩) (wire ▸ Relation.ReflTransGen.refl)
        exact direct ⟨k,act,(by dsimp [w] at wire; omega),wire⟩
      change (orIn n C w ∩ V).card ≤ 1
      rw [wire]; exact thin _ regular
  refine ⟨raw,little,(orN G C \ lam G C).filter (fun k =>
    (orIn n C (n+k)).Nonempty ∧ OrReaches n C w k),?_,?_⟩
  · intro k m
    obtain ⟨elig,rawK,reaches⟩ := Finset.mem_filter.mp m
    have path := (orReaches_reach k w reaches).1
    have le := orStep_le path
    refine ⟨ac k elig path,(by dsimp [w] at le; omega),elig,rawK,fun t mt => ?_⟩
    exact reach_mem_orIn t (path.trans (mem_orIn_reach t mt))
  · intro x
    exact nonemptyPortValue (G := G) ao x w (by dsimp [w]; omega) raw

#print axioms port_law
end P4Ports
