import GeneralThree

namespace RawBudget
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_1491
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing

attribute [local instance] gateOpDecEq

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- One earlier input already contains the gate's entire raw support. This need
not make the circuit gate redundant, since the other input can carry dirty ANDs. -/
def bypass (n : ℕ) (C : Circuit) (k : ℕ) :=
  ∃ w ∈ (gateAt C k).inputs, orIn n C (n+k) = orIn n C w

noncomputable section
local instance (k : ℕ) : Decidable (bypass n C k) := Classical.propDecidable _

/-- For counting raw incidences only, delete the second read wherever the first
already covers the entire raw support. Keep the original wire names. -/
private noncomputable def rawGate (n : ℕ) (C : Circuit) (k : ℕ) : Gate := by
  classical
  exact if h : bypass n C k then ⟨(gateAt C k).op, [h.choose]⟩ else gateAt C k

private theorem rawOp (k : ℕ) : (rawGate n C k).op = (gateAt C k).op := by
  classical
  unfold rawGate
  split <;> rfl

private theorem rawInput (k w : ℕ) (m : w ∈ (rawGate n C k).inputs) :
    w ∈ (gateAt C k).inputs := by
  classical
  by_cases h : bypass n C k
  · have eq : w = h.choose := by simpa [rawGate,h] using m
    exact eq ▸ h.choose_spec.1
  · simpa [rawGate,h] using m

private theorem rawUnion {k : ℕ} (hor : (rawGate n C k).op = GateOp.or)
    (back : ∀ k, ∀ i ∈ (gateAt C k).inputs, i < n+k) (u : Fin n) :
    u ∈ orIn n C (n+k) ↔ ∃ w ∈ (rawGate n C k).inputs, u ∈ orIn n C w := by
  classical
  by_cases h : bypass n C k
  · simp only [rawGate,dite_eq_left h,List.mem_singleton,exists_eq_left]
    exact Iff.of_eq (congrArg (fun t : Finset (Fin n) => u ∈ t) h.choose_spec.2)
  · rw [show rawGate n C k = gateAt C k by simp [rawGate,h],orIn_gate]
    refine ⟨fun ⟨_,_,w,m,_,hu⟩ => ⟨w,m,hu⟩,?_⟩
    rintro ⟨w,m,hu⟩
    have len : k < C.gates.length := by
      by_contra! notLen
      rw [gateAt_ge notLen] at m
      simp at m
    exact ⟨len,(rawOp k).symm.trans hor,w,m,back k w m,hu⟩

private theorem origPathOf {r k : ℕ}
    (path : Relation.ReflTransGen (fun j i => (rawGate n C j).op = GateOp.or ∧ n+i ∈ (rawGate n C j).inputs) r k) :
    Relation.ReflTransGen (fun j i => (gateAt C j).op = GateOp.or ∧ n+i ∈ (gateAt C j).inputs) r k := by
  induction path with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail ⟨(rawOp _).symm.trans step.1,rawInput _ _ step.2⟩

private theorem two_survives {k : ℕ} (two : TwoNe (rawGate n C) (orIn n C) k) :
    ¬bypass n C k := by
  classical
  intro h
  obtain ⟨w,hw,t,ht,ne,_,_⟩ := two
  simp only [rawGate,dite_eq_left h,List.mem_singleton] at hw ht
  exact ne (hw.trans ht.symm)

/-- Productive ordinary ORs accessible from the chosen group of tops. -/
noncomputable def reachable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (T : Finset ℕ) :=
  ((lam G C).filter (fun k => ¬bypass n C k)).filter (fun k => ∃ a ∈ T, ∃ b : Fin 2, OrReaches n C (opnd C a b) k)

private theorem raw_star_count (four : NoFourCycle G) (least : IsLeastAO G C)
    (T : Finset ℕ) (subset : T ⊆ tops G C) (E : Finset (Sym2 (Fin n)))
    (serves : ∀ e ∈ E, ∃ a ∈ T, ∃ u ∈ side (n := n) C a 0, ∃ v ∈ side C a 1, e = s(u,v)) :
    E.card ≤ T.card + (reachable G C T).card := by
  classical
  let g := rawGate n C
  obtain ⟨hAO,hRB,h2⟩ := least.1
  have hlen (k : ℕ) : (g k).inputs.length ≤ 2 := by
    by_cases h : bypass n C k
    · simp [g,rawGate,h]
    · simp only [g,rawGate,dite_eq_right h]
      by_cases len : k < C.gates.length
      · rw [h2 _ (S90.gateAt_mem len)]
      · rw [gateAt_ge (by omega)]; decide
  have hback (k i : ℕ) (m : i ∈ (gateAt C k).inputs) : i < n+k := by
    by_cases len : k < C.gates.length
    · exact hRB k len i m
    · rw [gateAt_ge (by omega)] at m; simp at m
  have hf3 (k : ℕ) (notOr : (g k).op ≠ GateOp.or) : (orIn n C (n + k)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha
    exact (notOr ((rawOp k).trans ((orIn_gate C k a).mp ha).2.1)).elim
  have h4' : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
    rintro a b c d hac hbd ⟨h1, h2', h3, h5⟩
    have hsub : ({b, d} : Finset (Fin n)) ⊆
        Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj c w) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hw with rfl | rfl
      · exact ⟨h1, h2'.symm⟩
      · exact ⟨h5.symm, h3⟩
    have := (Finset.card_le_card hsub).trans (four a c hac)
    rw [Finset.card_pair hbd] at this
    omega
  have hstar : ∀ a, a ∈ T →
      (∀ u, u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0) →
        ∀ v, v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1) → G.Adj u v) ∧
      ((PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0)).card ≤ 1 ∨
        (PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1)).card ≤ 1) := by
    intro a ha
    have hf := S90.top_facts G C four least a (subset ha)
    exact ⟨hf.2.1, hf.2.2⟩
  obtain ⟨⟨Z,hZ,hNZ⟩,_⟩ := assemble2 n G h4' g (fun k _ => hlen k)
    (fun k i m => hback k i (rawInput k i m)) (orIn n C) (fun w hw => orIn_input C w hw)
    (fun _ hop => rawUnion hop hback) hf3 ∅ (by simp)
    T (opnd C) hstar E serves
  have zgood : Z ⊆ reachable G C T := by
    intro k mk
    obtain ⟨_,hor,two,a,ha,b,above,path,_,opp⟩ := hZ k mk
    have origTwo : TwoNe (gateAt C) (orIn n C) k := by
      obtain ⟨u,mu,v,mv,ne,ru,rv⟩ := two
      exact ⟨u,rawInput k u mu,v,rawInput k v mv,ne,ru,rv⟩
    have origPath := origPathOf path
    have atop := subset ha
    have alen := (topData atop).1
    have bound := opnd_lt h2 hRB alen b
    obtain ⟨r,len⟩ := rtg_conv C hRB _ k origPath (by omega)
    rw [show n + (opnd C a b - n) = opnd C a b by omega] at r
    have origOr := (rawOp k).symm.trans hor
    obtain ⟨dirty,side0,side1⟩ := two_facts G C h2 hRB len origOr origTwo
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_,two_survives two⟩,a,ha,b,S90.reach_orReaches r k rfl len⟩
    simp only [lam,orN,gatesWhere,Finset.mem_filter,Finset.mem_range]
    exact ⟨⟨len,origOr,dirty⟩,side0,side1,a,atop,b,opp,S90.reach_orReaches r k rfl len⟩
  exact hNZ.trans (Nat.add_le_add_left (Finset.card_le_card zgood) _)

private theorem gate_partition (least : IsLeastAO G C) :
    (tops G C).card + (junk G C).card + (orT G C).card + (orN G C).card = C.size := by
  classical
  have hAO := least.1.1
  have splitOps (k : ℕ) (len : k < C.gates.length) :
      ((gateAt C k).op = GateOp.and ∧ (gateAt C k).op ≠ GateOp.or) ∨
      ((gateAt C k).op = GateOp.or ∧ (gateAt C k).op ≠ GateOp.and) := by
    rcases hAO _ (S90.gateAt_mem len) with h|h <;> simp [h]
  exact four_split C.gates.length _ _ (BelowF G C) splitOps (tops G C) (junk G C) (orT G C) (orN G C)
    (fun k => by simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range])
    (fun k => junk_iff G C k)
    (fun k => by simp only [orT,gatesWhere,Finset.mem_filter,Finset.mem_range])
    (fun k => by simp only [orN,gatesWhere,Finset.mem_filter,Finset.mem_range])

/-- The ordinary incidence count only needs ORs for which neither operand
already covers the raw support. Comparable operands at such an OR cost a full extra gate. -/
theorem charge (four : NoFourCycle G) (edges : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (top : TopForm G C) :
    G.edgeFinset.card + (tops G C \ centreless G C).card + 2*(centreless G C).card +
        (junk G C).card + (orN G C \ lam G C).card +
        ((lam G C).filter (bypass n C)).card
        ≤ C.size + (Ustar G C).card + 1 := by
  classical
  have hEs : ∀ e, e ∈ G.edgeFinset \ PEqualNP.TopForm.Ustar G C →
      ∃ a, a ∈ PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C ∧
        ∃ u, u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0) ∧
        ∃ v, v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1) ∧ e = s(u, v) := by
    intro e he
    have he' : e ∈ PEqualNP.TopForm.starEdges G C := by
      simp only [PEqualNP.TopForm.Ustar, Finset.mem_sdiff, not_and, not_not] at he
      exact he.2 he.1
    simp only [PEqualNP.TopForm.starEdges, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_product] at he'
    obtain ⟨a, ha, p, hp, hpe⟩ := he'
    refine ⟨a, ?_, p.1, hp.1, p.2, hp.2, hpe.symm⟩
    rw [Finset.mem_sdiff]
    refine ⟨ha, fun hc => ?_⟩
    simp only [PEqualNP.TopForm.centreless, Finset.mem_filter] at hc
    rcases hc.2 with h | h
    · have := hp.1
      rw [h] at this
      exact absurd this (Finset.notMem_empty _)
    · have := hp.2
      rw [h] at this
      exact absurd this (Finset.notMem_empty _)
  have count := raw_star_count four least (tops G C \ centreless G C)
    Finset.sdiff_subset (G.edgeFinset \ Ustar G C) hEs
  have countGood := Finset.card_le_card (show reachable G C (tops G C \ centreless G C) ⊆ (lam G C).filter (fun k => ¬bypass n C k) from Finset.filter_subset _ _)
  have split := gate_partition least
  have tree := (S98.main_real n G C edges least top).2.2
  have size : C.size = C.gates.length := rfl
  have u := Finset.card_sdiff_add_card_eq_card (show Ustar G C ⊆ G.edgeFinset from Finset.sdiff_subset)
  have t := Finset.card_sdiff_add_card_eq_card (show centreless G C ⊆ tops G C from Finset.filter_subset _ _)
  have l := Finset.card_sdiff_add_card_eq_card (show lam G C ⊆ orN G C from Finset.filter_subset _ _)
  have part := (lam G C).card_filter_add_card_filter_not (bypass n C)
  omega

/-- Ordinary incidences served at tops in T. -/
noncomputable def covered (n : ℕ) (C : Circuit) (T : Finset ℕ) :=
  T.biUnion fun a => (side (n := n) C a 0 ×ˢ side C a 1).image fun p => s(p.1,p.2)

theorem covered_count (four : NoFourCycle G) (least : IsLeastAO G C)
    (T : Finset ℕ) (sub : T ⊆ tops G C) :
    (covered n C T).card ≤ T.card + (reachable G C T).card := by
  apply raw_star_count four least T sub
  intro e he
  obtain ⟨a,ha,m⟩ := Finset.mem_biUnion.mp he
  obtain ⟨p,hp,eq⟩ := Finset.mem_image.mp m
  exact ⟨a,ha,p.1,(Finset.mem_product.mp hp).1,p.2,(Finset.mem_product.mp hp).2,eq.symm⟩

theorem covered_all (least : IsLeastAO G C) : covered n C (tops G C) = G.edgeFinset \ Ustar G C := by
  classical
  ext e
  change e ∈ starEdges G C ↔ e ∈ G.edgeFinset \ (G.edgeFinset \ starEdges G C)
  constructor
  · intro h
    refine Finset.mem_sdiff.mpr ⟨?_,fun x => (Finset.mem_sdiff.mp x).2 h⟩
    obtain ⟨a,ha,h'⟩ := Finset.mem_biUnion.mp h
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp h'
    exact SimpleGraph.mem_edgeFinset.mpr (topAdj least.1 ha (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hp).2)
  · intro h
    by_contra no
    exact (Finset.mem_sdiff.mp h).2 (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp h).1,no⟩)

theorem productive (four : NoFourCycle G) (edges : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (top : TopForm G C) (three : (Ustar G C).card = 3)
    (S : Finset (Fin n)) (f : S → Fin n) (inj : Function.Injective f)
    (partners : ∀ v, f v ∉ S ∧ G.Adj v.val (f v)) (fail : ¬GeneralThree.wireBound G C S) :
    (covered n C (tops G C)).card = (tops G C).card + (lam G C).card ∧
    ∀ h ∈ lam G C, ¬bypass n C h := by
  classical
  obtain ⟨two,zero,twoOr,_⟩ := GeneralThree.remaining G C four edges least top three S f inj partners fail
  obtain ⟨_,tight,_⟩ := GeneralThree.tight_if_failed G C four edges least top three S f inj partners fail
  have empty := Finset.card_eq_zero.mp zero
  have count := charge four edges least top
  have split := gate_partition least
  have tree := (S98.main_real n G C edges least top).2.2
  have u := Finset.card_sdiff_add_card_eq_card (show Ustar G C ⊆ G.edgeFinset from Finset.sdiff_subset)
  have part := Finset.card_sdiff_add_card_eq_card (show lam G C ⊆ orN G C from Finset.filter_subset _ _)
  rw [empty,Finset.sdiff_empty,Finset.card_empty] at count
  refine ⟨by rw [covered_all least]; omega,?_⟩
  intro h hm redundant
  have pos := Finset.card_pos.mpr (show ((lam G C).filter (bypass n C)).Nonempty from
    ⟨h,Finset.mem_filter.mpr ⟨hm,redundant⟩⟩)
  omega

private theorem singleton_gate {h : ℕ} {v : Fin n} (eq : orIn n C (n+h) = {v}) :
    bypass n C h := by
  classical
  have mem : v ∈ orIn n C (n+h) := by simp [eq]
  obtain ⟨len,op,w,read,lt,hw⟩ := (orIn_gate C h v).mp mem
  refine ⟨w,read,Finset.Subset.antisymm ?_ ?_⟩
  · rw [eq]; exact Finset.singleton_subset_iff.mpr hw
  · intro u hu
    exact (orIn_gate C h u).mpr ⟨len,op,w,read,lt,hu⟩

/-- Every singleton wire is its own raw input or one of the exceptional ORs. -/
theorem singleton_wire (productive : ∀ h ∈ lam G C, ¬bypass n C h)
    (w : ℕ) (v : Fin n) (raw : orIn n C w = {v}) :
    w = v.val ∨ ∃ h ∈ orN G C \ lam G C, w = n+h := by
  classical
  have mem : v ∈ orIn n C w := by simp [raw]
  by_cases small : w < n
  · left
    rcases Relation.ReflTransGen.cases_head (mem_orIn_reach v mem) with eq | ⟨j,step,_⟩
    · exact eq
    · obtain ⟨k,_,eq,_,_,_⟩ := step; omega
  · right
    obtain ⟨h,rfl⟩ : ∃ h, w = n+h := ⟨w-n,by omega⟩
    obtain ⟨len,op,_⟩ := (orIn_gate C h v).mp mem
    refine ⟨h,Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr len,op,?_⟩,
      fun hl => productive h hl (singleton_gate raw)⟩,rfl⟩
    intro below
    have yes := reach_var_val (pairInput v v) _ v (mem_orIn_reach v mem) (pairInput_left v v)
    exact G.irrefl ((graphFun_pair G v v).mp (below _ yes))

/-- In a sharp circuit, each ordinary edge served in both parts of a partition
requires a distinct additional productive OR that can be reached in both parts. -/
theorem overlap_count (four : NoFourCycle G) (least : IsLeastAO G C)
    (sharp : (covered n C (tops G C)).card = (tops G C).card + (lam G C).card)
    (P Q : Finset ℕ) (parts : P ∪ Q = tops G C) (separate : Disjoint P Q) :
    ((covered n C P) ∩ (covered n C Q)).card ≤
      ((reachable G C P) ∩ (reachable G C Q)).card := by
  classical
  have psub : P ⊆ tops G C := parts ▸ Finset.subset_union_left
  have qsub : Q ⊆ tops G C := parts ▸ Finset.subset_union_right
  have p := covered_count four least P psub
  have q := covered_count four least Q qsub
  have eq : covered n C P ∪ covered n C Q = covered n C (tops G C) := by
    simp only [←parts,covered,Finset.union_biUnion]
  have e := Finset.card_union_add_card_inter (covered n C P) (covered n C Q)
  have r := Finset.card_union_add_card_inter (reachable G C P) (reachable G C Q)
  have nr := Finset.card_le_card (show reachable G C P ∪ reachable G C Q ⊆ lam G C from
    Finset.union_subset ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
      ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _)))
  have t := Finset.card_union_of_disjoint separate
  rw [eq,sharp] at e
  rw [parts] at t
  omega

#print axioms charge
#print axioms productive
#print axioms singleton_wire
#print axioms overlap_count
end
end RawBudget
