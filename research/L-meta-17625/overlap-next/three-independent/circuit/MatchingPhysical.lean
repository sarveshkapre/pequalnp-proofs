import MatchingGateOrder
import MatchingRows
import MatchProjected

set_option maxHeartbeats 1800000

namespace MatchingPhysical
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

def physical (v : Fin 6 → Fin n) (C : Circuit) (w : ℕ) : MatchProjected.Wire :=
  ⟨MatchingRows.raw v (orIn n C w), decide (orIn n C w).Nonempty,
    fun r => val C (List.ofFn (MatchingRows.input v r)) w⟩

theorem literal (v : Fin 6 → Fin n) (R : Finset (Fin n)) (r : MatchProjected.Raw) :
    MatchProjected.hit (MatchingRows.raw v R) r = true ↔
      ∃ u ∈ R, MatchingRows.input v r u = true := by
  change ((MatchingRows.raw v R &&& r) != 0) = true ↔ _
  rw [bne_iff_ne]
  have zeroBit (i : Fin 6) : (0 : MatchProjected.Raw).getLsbD i = false := by simp
  constructor
  · intro h
    by_contra! none
    apply h
    apply PathBits.bit_ext
    intro i
    by_cases m : v i ∈ R
    · have off := none (v i) m
      have unused : r.getLsbD i = false := by
        apply Bool.eq_false_iff.mpr
        intro on
        have yes : MatchingRows.input v r (v i) = true := decide_eq_true ⟨i,rfl,on⟩
        simp_all
      rw [BitVec.getLsbD_and, unused, Bool.and_false, zeroBit i]
    · rw [BitVec.getLsbD_and,MatchingRows.raw_bit,decide_eq_false m,Bool.false_and,zeroBit i]
  · rintro ⟨u,mem,on⟩ no
    obtain ⟨i,rfl,yes⟩ := of_decide_eq_true on
    have e := congrArg (fun a : BitVec 6 => a.getLsbD i) no
    change (MatchingRows.raw v R &&& r).getLsbD i = (0 : BitVec 6).getLsbD i at e
    rw [BitVec.getLsbD_and,MatchingRows.raw_bit,decide_eq_true mem,yes,zeroBit i] at e
    contradiction

private theorem physical_gate (v : Fin 6 → Fin n) (ao : IsAO2 n C) {g : ℕ}
    (len : g < C.gates.length) :
    physical v C (n+g) = MatchProjected.gate (PathPhysical.kind C g)
      (physical v C (opnd C g 0)) (physical v C (opnd C g 1)) := by
  rcases ao.1 _ (gateAt_mem len) with op|op
  · have kind : PathPhysical.kind C g = false := by simp [PathPhysical.kind,op]
    have raw := andRawEmpty (n := n) op
    have yes (r) : val C (List.ofFn (MatchingRows.input v r)) (n+g) =
        (val C (List.ofFn (MatchingRows.input v r)) (opnd C g 0) &&
         val C (List.ofFn (MatchingRows.input v r)) (opnd C g 1)) := by
      apply Bool.eq_iff_iff.mpr
      rw [Bool.and_eq_true]
      exact andValBoth ao len op _
    simp [physical,MatchProjected.gate,kind,raw,MatchingRows.raw_empty,yes]
  · have kind : PathPhysical.kind C g = true := by simp [PathPhysical.kind,op]
    have raw := orRawUnion ao len op
    have yes (r) : val C (List.ofFn (MatchingRows.input v r)) (n+g) =
        (val C (List.ofFn (MatchingRows.input v r)) (opnd C g 0) ||
         val C (List.ofFn (MatchingRows.input v r)) (opnd C g 1)) := by
      apply Bool.eq_iff_iff.mpr
      rw [Bool.or_eq_true]
      exact PathPhysical.or_value ao len op _
    simp [physical,MatchProjected.gate,kind,raw,MatchingRows.raw_union,yes,Finset.union_nonempty,
      PEqualNP.TopForm.side]

/-- A fixed set of gates describes each nonempty physical port on every projected input. -/
private theorem source_side (v : Fin 6 → Fin n) (ao : IsAO2 n C) {g : ℕ}
    (len : g < C.gates.length) (p : Fin 2) (present : (side (n := n) C g p).Nonempty)
    (o : MatchingGateOrder.Ordered G C) (hist : Fin 4 → MatchProjected.Wire)
    (active : ∀ k ∈ PhysicalPortMasks.sources G C g p, k ∈ P4Ports.active G C)
    (known : ∀ i, o.ids i ∈ PhysicalPortMasks.sources G C g p → hist i = physical v C (n+o.ids i)) :
    ∃ take : BitVec 4, ∀ r, MatchProjected.side (MatchingRows.raw v (side (n := n) C g p)) take hist r =
      val C (List.ofFn (MatchingRows.input v r)) (opnd C g p) := by
  classical
  let K := PhysicalPortMasks.sources G C g p
  let m := MatchingRows.raw v (side (n := n) C g p)
  let take := PathBits.pack (fun i : Fin 4 => decide (o.ids i ∈ K))
  have inc (i : Fin 4) (r : BitVec 6) :
      MatchProjected.included m (take.getLsbD i.val) (hist i) r = true ↔
        o.ids i ∈ K ∧ gateVal n C (o.ids i) (MatchingRows.input v r) = true := by
    change MatchProjected.included m ((PathBits.pack _).getLsbD i.val) _ _ = true ↔ _
    rw [PathBits.get_pack]
    by_cases mi : o.ids i ∈ K
    · obtain ⟨_,nonempty,_,sub⟩ := PhysicalPortMasks.source_data mi
      have mask := MatchingRows.raw_sub v sub
      rw [known i mi]
      simp [MatchProjected.included,physical,mi,nonempty,m,MatchProjected.subset,mask,gateVal_eq_val]
    · simp [MatchProjected.included,mi]
  refine ⟨take,fun r => Bool.eq_iff_iff.mpr ?_⟩
  rw [PhysicalPortMasks.port_value (G := G) ao len p present]
  have exists_iff : (∃ i : Fin 4, o.ids i ∈ K ∧ gateVal n C (o.ids i) (MatchingRows.input v r) = true) ↔
      ∃ k ∈ K, gateVal n C k (MatchingRows.input v r) = true := by
    constructor
    · rintro ⟨i,mi,on⟩; exact ⟨_,mi,on⟩
    · rintro ⟨k,mk,on⟩; obtain ⟨i,eq⟩ := o.cover _ (active k mk); exact ⟨i,eq ▸ mk,eq ▸ on⟩
  rw [←exists_iff, ←literal]
  change MatchProjected.side m take hist r = true ↔ _
  simp only [MatchProjected.side,Bool.or_eq_true]
  constructor
  · rintro ((((hit|i0)|i1)|i2)|i3)
    · exact .inl hit
    · exact .inr ⟨0,(inc 0 r).mp i0⟩
    · exact .inr ⟨1,(inc 1 r).mp i1⟩
    · exact .inr ⟨2,(inc 2 r).mp i2⟩
    · exact .inr ⟨3,(inc 3 r).mp i3⟩
  · rintro (hit|⟨j,on⟩)
    · exact .inl (.inl (.inl (.inl hit)))
    · fin_cases j
      · exact .inl (.inl (.inl (.inr ((inc 0 r).mpr on))))
      · exact .inl (.inl (.inr ((inc 1 r).mpr on)))
      · exact .inl (.inr ((inc 2 r).mpr on))
      · exact .inr ((inc 3 r).mpr on)

/-- Ordinary operands are represented by a raw mask and all eligible earlier ORs.
A direct read of any earlier charged gate may instead pass its entire wire. -/
private theorem stage (v : Fin 6 → Fin n) (cross : MatchProjected.Cross)
    (ao : IsAO2 n C) (top : TopForm G C) (o : MatchingGateOrder.Ordered G C)
    (lit : ∀ u, MatchProjected.allowed cross (MatchingRows.raw v {u}) = true)
    (ordinary : ∀ k ∈ lam G C, MatchProjected.allowed cross (MatchingRows.raw v (orIn n C (n+k))) = true)
    (i : Fin 4) (p : Fin 2) :
    let hist (j : Fin 4) := if j < i then physical v C (n+o.ids j) else MatchProjected.zero
    ∃ s : MatchProjected.Selector, (s.direct = false → MatchProjected.allowed cross s.raw = true) ∧
      MatchProjected.port s hist = physical v C (opnd C (o.ids i) p) := by
  dsimp only
  let hist (j : Fin 4) := if j < i then physical v C (n+o.ids j) else MatchProjected.zero
  rcases PhysicalPortMasks.port_law ao top (fun R => MatchProjected.allowed cross (MatchingRows.raw v R) = true)
    lit ordinary (o.active i) p with ⟨k,act,lt,wire⟩|⟨present,admissible,keys,spec⟩
  · obtain ⟨j,eq⟩ := o.cover _ act
    have small : j < i := o.ids.lt_iff_lt.mp (by simpa [eq] using lt)
    exact ⟨⟨0,0,true,j⟩,(by simp),by simp [MatchProjected.port,small,eq,wire]⟩
  · have len := P4Ports.active_length (o.active i)
    have known (j : Fin 4) (m : o.ids j ∈ PhysicalPortMasks.sources G C (o.ids i) p) :
        hist j = physical v C (n+o.ids j) := by
      have lt := (keys _ m).2.1
      simp [hist,o.ids.lt_iff_lt.mp lt]
    obtain ⟨take,values⟩ := source_side v ao len p present o hist (fun k m => (keys k m).1) known
    refine ⟨⟨MatchingRows.raw v (side (n := n) C (o.ids i) p),take,false,0⟩,fun _ => admissible,?_⟩
    change MatchProjected.Wire.mk _ true _ = MatchProjected.Wire.mk _ _ _
    congr 1
    · exact (decide_eq_true present).symm
    · exact funext values

private theorem assemble {o : Fin 4 → Bool} {s t : Fin 4 → MatchProjected.Selector}
    (ws : Fin 4 → MatchProjected.Wire)
    (step : ∀ i, ws i = MatchProjected.extend (o i) (s i) (t i)
      (fun j => if j < i then ws j else MatchProjected.zero)) :
    MatchProjected.schedule o s t = ws := by
  let z := MatchProjected.zero
  have e0 : ws 0 = MatchProjected.extend (o 0) (s 0) (t 0) (fun _ => z) := by
    rw [step 0]
    congr 1
  have e1 : ws 1 = MatchProjected.extend (o 1) (s 1) (t 1) ![ws 0,z,z,z] := by
    conv_lhs => rw [step 1]
    congr 1
    funext j
    fin_cases j <;> rfl
  have e2 : ws 2 = MatchProjected.extend (o 2) (s 2) (t 2) ![ws 0,ws 1,z,z] := by
    conv_lhs => rw [step 2]
    congr 1
    funext j
    fin_cases j <;> rfl
  have e3 : ws 3 = MatchProjected.extend (o 3) (s 3) (t 3) ![ws 0,ws 1,ws 2,z] := by
    conv_lhs => rw [step 3]
    congr 1
    funext j
    fin_cases j <;> rfl
  unfold MatchProjected.schedule
  dsimp only
  rw [←e0,←e1,←e2,←e3]
  funext j
  fin_cases j <;> rfl

private theorem operation_count (o : Fin 4 → Bool) :
    (List.ofFn o).count true = (Finset.univ.filter fun j => o j = true).card := by
  have tab (a b c d : Bool) : (List.ofFn ![a,b,c,d]).count true =
      (Finset.univ.filter fun j => ![a,b,c,d] j = true).card := by
    cases a <;> cases b <;> cases c <;> cases d <;> decide
  have restore : ![o 0,o 1,o 2,o 3] = o := by funext i; fin_cases i <;> rfl
  simpa only [restore] using tab (o 0) (o 1) (o 2) (o 3)

/-- Sorted gates and fixed physical selectors realize all four stages. Each top
port has a single downstream selector valid on all sixty-four input subsets. -/
theorem encode (v : Fin 6 → Fin n) (cross : MatchProjected.Cross)
    (ao : IsAO2 n C) (top : TopForm G C) (twoAnd : (junk G C).card = 2)
    (twoOr : (orN G C \ lam G C).card = 2)
    (atTops : ActiveOr.atTops G C = orN G C \ lam G C)
    (lit : ∀ u, MatchProjected.allowed cross (MatchingRows.raw v {u}) = true)
    (ordinary : ∀ k ∈ lam G C, MatchProjected.allowed cross (MatchingRows.raw v (orIn n C (n+k))) = true) :
    ∃ (o : Fin 4 → Bool) (s t : Fin 4 → MatchProjected.Selector),
      (List.ofFn o).count true = 2 ∧
      (∀ i, (s i).direct = false → MatchProjected.allowed cross (s i).raw = true) ∧
      (∀ i, (t i).direct = false → MatchProjected.allowed cross (t i).raw = true) ∧
      ∀ a : tops G C, ∀ p : Fin 2, (side (n := n) C a p).Nonempty → ∃ take : BitVec 4,
        ∀ r, MatchProjected.side (MatchingRows.raw v (side (n := n) C a p)) take
          (MatchProjected.schedule o s t) r = val C (List.ofFn (MatchingRows.input v r)) (opnd C a p) := by
  classical
  obtain ⟨ord⟩ := MatchingGateOrder.ordered twoAnd twoOr atTops
  let op i := PathPhysical.kind C (ord.ids i)
  let ws i := physical v C (n+ord.ids i)
  choose keys eligible physicalPort using stage v cross ao top ord lit ordinary
  have steps (i : Fin 4) :
      ws i = MatchProjected.extend (op i) (keys i 0) (keys i 1)
        (fun j => if j < i then ws j else MatchProjected.zero) := by
    unfold MatchProjected.extend
    rw [physicalPort i 0, physicalPort i 1]
    exact physical_gate v ao (P4Ports.active_length (ord.active i))
  have whole := assemble ws steps
  refine ⟨op,fun i => keys i 0,fun i => keys i 1,(operation_count op).trans ord.twoOr,
    fun i => eligible i 0,fun i => eligible i 1,?_⟩
  intro a p present
  rw [whole]
  have len := (topData a.2).1
  exact source_side v ao len p present ord ws
    (fun k m => (PhysicalPortMasks.source_active ao len
      ⟨a,len,(topData a.2).2.1,p,.refl⟩ m).1) (fun _ _ => rfl)

#print axioms encode
end MatchingPhysical
