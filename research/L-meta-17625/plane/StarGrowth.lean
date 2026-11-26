import PEqualNP.Outside.L_meta_7465

namespace StarGrowth
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing

attribute [local instance] gateOpDecEq

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- On fixing vertex v, each new singleton line must appear for the first time
at a dirty gate. Distinct new lines require distinct gates if each raw port
contains at most one of them. Sharing and the number of OR paths are unrestricted. -/
theorem first_changes (ao : IsAO2 n C) (top : TopForm G C) (v : Fin n) (L : Finset (Fin n))
    (sparse : ∀ j ∈ junk G C, ∀ b : Fin 2, ((side (n := n) C j b) ∩ L).card ≤ 1)
    (changes : ∀ l ∈ L, ∃ j ∈ junk G C, gateVal n C j (pairInput v v) = false ∧
      gateVal n C j (pairInput v l) = true) : L.card ≤ (junk G C).card := by
  classical
  let P (l : L) (j : ℕ) := j ∈ junk G C ∧ gateVal n C j (pairInput v v) = false ∧
    gateVal n C j (pairInput v l.val) = true
  have ex (l : L) : ∃ j, P l j := changes l l.2
  let first (l : L) := Nat.find (ex l)
  have spec (l : L) : P l (first l) := Nat.find_spec (ex l)
  have choosePort (j : ℕ) (hj : j ∈ junk G C) (off : gateVal n C j (pairInput v v) = false) :
      ∃ b : Fin 2, val C (List.ofFn (pairInput v v)) (opnd C j b) = false := by
    by_contra! no
    obtain ⟨len,hand,_⟩ := junkData hj
    have yes := (andValOperands ao len hand _).mpr (fun b => by simpa using no b)
    simp [off] at yes
  have hit (l : L) (b : Fin 2)
      (off : val C (List.ofFn (pairInput v v)) (opnd C (first l) b) = false) :
      l.val ∈ side (n := n) C (first l) b := by
    obtain ⟨hj,_,on⟩ := spec l
    obtain ⟨len,hand,_⟩ := junkData hj
    have signal := (andValOperands ao len hand _).mp on b
    rcases operandSupport ao top len hand signal with ⟨w,hw,eq | eq⟩ | ⟨k,hk,path,active⟩
    · subst w
      have := sideVal hw (pairInput_left v v)
      simp [off] at this
    · exact eq ▸ hw
    · exfalso
      have route := (orReaches_reach k _ path).1
      have hle := orStep_le route
      have hlt := opndBound ao len b
      have before : k < first l := by omega
      apply Nat.find_min (ex l) before
      refine ⟨hk,?_,active⟩
      apply Bool.eq_false_iff.mpr
      intro yes
      have := orStep_up (n := n) (by simp) route (gateVal_eq_val n C k (pairInput v v) ▸ yes)
      simp [off] at this
  let pick (l : L) : junk G C := ⟨first l,(spec l).1⟩
  have inject : Function.Injective pick := by
    intro x y eq
    have e : first x = first y := congrArg Subtype.val eq
    obtain ⟨b,hb⟩ := choosePort _ (spec x).1 (spec x).2.1
    have hx := Finset.mem_inter.mpr ⟨hit x b hb,x.2⟩
    have hy := hit y b (e ▸ hb)
    rw [←e] at hy
    exact Subtype.ext (Finset.card_le_one.mp (sparse _ (spec x).1 b) x hx y
      (Finset.mem_inter.mpr ⟨hy,y.2⟩))
  simpa using Fintype.card_le_of_injective pick inject

/-- Elementary monotonicity for a wire, including inputs. -/
lemma wire_mono (ao : IsAO2 n C) {x y : Fin n → Bool}
    (incl : ∀ i, x i = true → y i = true) {w : ℕ} (bd : w < n+C.gates.length)
    (on : val C (List.ofFn x) w = true) : val C (List.ofFn y) w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases input : w < n
    · let t : Fin n := ⟨w,input⟩
      exact (val_ofFn C y t).trans (incl t ((val_ofFn C x t).symm.trans on))
    obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n,by omega⟩
    have len : j < C.gates.length := by omega
    rcases ao.1 _ (gateAt_mem len) with hand | hor
    · apply (val_and (n := n) (by simp) len hand).mpr
      have h := (val_and (n := n) (by simp) len hand).mp on
      intro u hu
      obtain ⟨lt,yes⟩ := h u hu
      exact ⟨lt,ih u lt (by omega) yes⟩
    · apply (val_or (n := n) (by simp) len hor).mpr
      obtain ⟨u,hu,lt,yes⟩ := (val_or (n := n) (by simp) len hor).mp on
      exact ⟨u,hu,lt,ih u lt (by omega) yes⟩

/-- If each top has a different raw centre from v and its partners, and its
opposite port admits a non-neighbor of v, then every residual singleton must
switch on some previously inactive dirty AND. -/
theorem centre_changes (least : IsLeastAO G C) (top : TopForm G C)
    (v : Fin n) (L : Finset (Fin n)) (positive : ∀ l ∈ L, G.Adj v l)
    (b : tops G C → Fin 2) (z : tops G C → Fin n)
    (raw : ∀ a : tops G C, side (n := n) C a (b a) = {z a})
    (other : ∀ a, z a ≠ v ∧ z a ∉ L)
    (guard : ∀ a : tops G C, ∃ w ∈ side (n := n) C a (1-b a), ¬G.Adj v w) :
    ∀ l ∈ L, ∃ j ∈ junk G C, gateVal n C j (pairInput v v) = false ∧
      gateVal n C j (pairInput v l) = true := by
  intro l hl
  obtain ⟨a,ha,yes⟩ := acceptedTop least (positive l hl)
  let A : tops G C := ⟨a,ha⟩
  obtain ⟨len,hand,below⟩ := topData ha
  have off : val C (List.ofFn (pairInput v v)) (opnd C a (b A)) = false := by
    apply Bool.eq_false_iff.mpr
    intro active
    obtain ⟨w,hw,noedge⟩ := guard A
    have incl (i : Fin n) (on : pairInput v v i = true) : pairInput v w i = true := by
      rcases (pairInput_true _ _ _).mp on with eq | eq <;> subst i <;> exact pairInput_left _ _
    have bd := opndBound least.1 len (b A)
    have left := wire_mono least.1 incl (by omega : opnd C a (b A) < n+C.gates.length) active
    have right := sideVal hw (pairInput_right v w)
    apply noedge ((graphFun_pair G v w).mp (below _ ((andValOperands least.1 len hand _).mpr ?_)))
    intro c
    rcases opposite (b A) c with rfl | rfl
    · exact left
    · exact right
  have on := (andValOperands least.1 len hand _).mp yes (b A)
  rcases operandSupport least.1 top len hand on with ⟨t,h,eq | eq⟩ | ⟨j,hj,path,active⟩
  · have hz : t = z A := Finset.mem_singleton.mp ((raw A) ▸ h)
    exact False.elim ((other A).1 (hz.symm.trans eq))
  · have hz : t = z A := Finset.mem_singleton.mp ((raw A) ▸ h)
    exact False.elim ((other A).2 ((hz.symm.trans eq) ▸ hl))
  · refine ⟨j,hj,?_,active⟩
    apply Bool.eq_false_iff.mpr
    intro firing
    have route := (orReaches_reach j _ path).1
    have := orStep_up (n := n) (by simp) route (gateVal_eq_val n C j (pairInput v v) ▸ firing)
    simp [off] at this

/-- Every raw-rich OR outside the exceptional set lies under a top port by
the definition of Lambda. Thus sparsity there and at tops gives sparsity at all ports. -/
theorem all_raw_sparse (ao : IsAO2 n C) (L : Finset (Fin n))
    (topsThin : ∀ a ∈ tops G C, ∀ b : Fin 2, ((side (n := n) C a b) ∩ L).card ≤ 1)
    (otherThin : ∀ h ∈ orN G C \ lam G C, ((orIn n C (n+h)) ∩ L).card ≤ 1)
    (w : ℕ) (bd : w < n+C.gates.length) : ((orIn n C w) ∩ L).card ≤ 1 := by
  classical
  by_cases input : w < n
  · apply Finset.card_le_one.mpr
    intro a ha b hb
    have atInput (i : Fin n) (mem : i ∈ orIn n C w) : i.val = w := by
      rcases Relation.ReflTransGen.cases_head (mem_orIn_reach i mem) with eq | ⟨u,step,_⟩
      · exact eq.symm
      · obtain ⟨j,_,e,_,_,_⟩ := step; omega
    exact Fin.ext ((atInput a (Finset.mem_inter.mp ha).1).trans (atInput b (Finset.mem_inter.mp hb).1).symm)
  obtain ⟨h,rfl⟩ : ∃ h, w = n+h := ⟨w-n,by omega⟩
  have len : h < C.gates.length := by omega
  by_cases raw : (orIn n C (n+h)).Nonempty
  · obtain ⟨i,mem⟩ := raw
    have hor : (gateAt C h).op = GateOp.or := by
      rcases ao.1 _ (gateAt_mem len) with hand | out
      · rw [andRawEmpty hand] at mem; exact False.elim ((Finset.notMem_empty _) mem)
      · exact out
    have ordinary : h ∈ orN G C := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr len,hor,?_⟩
      intro below
      have yes := reach_var_val (pairInput i i) _ i (mem_orIn_reach i mem) (pairInput_left i i)
      exact G.irrefl ((graphFun_pair G i i).mp (below _ yes))
    by_cases lamGate : h ∈ lam G C
    · obtain ⟨_,_,_,a,ha,b,_,path⟩ := Finset.mem_filter.mp lamGate
      apply le_trans (Finset.card_le_card (t := side (n := n) C a b ∩ L) ?_) (topsThin a ha b)
      intro v hv
      obtain ⟨inRaw,inL⟩ := Finset.mem_inter.mp hv
      exact Finset.mem_inter.mpr ⟨reach_mem_orIn v (((orReaches_reach h _ path).1).trans (mem_orIn_reach v inRaw)),inL⟩
    · exact otherThin h (Finset.mem_sdiff.mpr ⟨ordinary,lamGate⟩)
  · rw [Finset.not_nonempty_iff_eq_empty.mp raw]; simp

#print axioms all_raw_sparse
#print axioms first_changes
#print axioms centre_changes
end StarGrowth
