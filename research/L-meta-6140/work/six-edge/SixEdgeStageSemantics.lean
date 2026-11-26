import SixEdgeReplayPortClauses

namespace SixEdge.Plane

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open PlaneFour ResidualDegree Formula

set_option maxHeartbeats 3000000
noncomputable section

variable {C : Circuit} {S : Stars C} {count : (charged plane C).card = 5} {P : OrderedPorts S count}

theorem scheduled_dirty_bit (A : GateSchedule P) (i : Fin 5) :
    A.masks.1.getLsbD i = dirtyAt count (A.index.symm i) := by
  unfold GateSchedule.masks
  exact ofSlots_bit (fun j => dirtyAt count (A.index.symm j)) i

private theorem or_support (ao : IsAO2 26 C) {g : Nat} (bound : g < C.gates.length)
    (hop : (gateAt C g).op = GateOp.or) (x : Fin 26) :
    x ∈ orIn 26 C (26+g) ↔ ∃ b : Fin 2, x ∈ side (n := 26) C g b := by
  constructor
  · intro mem
    rcases Relation.ReflTransGen.cases_head (mem_orIn_reach x mem) with equal | ⟨w,head,tail⟩
    · have := x.isLt
      omega
    · obtain ⟨j,_,eq,_,reads,_⟩ := head
      have same : j = g := by omega
      subst j
      obtain ⟨b,hb⟩ := inputsAsOpnd ao bound reads
      refine ⟨b,?_⟩
      change x ∈ orIn 26 C (opnd C g b)
      rw [← hb]
      exact reach_mem_orIn x tail
  · rintro ⟨b,member⟩
    have step : OrStep 26 C (26+g) (opnd C g b) :=
      ⟨g,bound,rfl,hop,opndMem ao bound b,opndBound ao bound b⟩
    exact reach_mem_orIn x ((mem_orIn_reach x member).head step)

theorem scheduled_raw_combine (A : GateSchedule P) (ao : IsAO2 26 C) (r : Relabelling) (i : Fin 5) (j : Nat) :
    (if A.masks.1.getLsbD i then false
     else scheduledPortRaw A r i 0 j || scheduledPortRaw A r i 1 j) = scheduledRaw A r i j := by
  classical
  let q := A.index.symm i
  let g := (gateOrder count q).val
  let x := r.inverse.vertex (Fin.ofNat 26 j)
  let perm := (replayOperandOrder A i).trans (P.order q)
  have sides (b : Fin 2) : (replayPort A i b).raw count = side (n := 26) C g (perm b) :=
    P.raw q (replayOperandOrder A i b)
  have pair (b : Fin 2) : b = 0 ∨ b = 1 := by decide +revert
  rw [scheduled_dirty_bit]
  change (if dirtyAt count q then _ else _) = _
  rcases Finset.mem_union.mp (gateOrder count q).property with andMem | orMem
  · have on : dirtyAt count q = true := decide_eq_true andMem
    simp only [on,↓reduceIte]
    change false = decide (x ∈ orIn 26 C (26+g))
    rw [andRawEmpty (junkData andMem).2.1]
    simp
  · have off : dirtyAt count q = false := decide_eq_false
      (fun h => Finset.disjoint_left.mp disjoint_charged h orMem)
    simp only [off,Bool.false_eq_true,↓reduceIte]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true,scheduledPortRaw,scheduledRaw,decide_eq_true_eq,sides]
    change (x ∈ side C g (perm 0) ∨ x ∈ side C g (perm 1)) ↔ x ∈ orIn 26 C (26+g)
    rw [or_support ao (orData orMem).1 (orData orMem).2.1]
    constructor
    · rintro (h | h)
      · exact ⟨_,h⟩
      · exact ⟨_,h⟩
    · rintro ⟨b,h⟩
      rcases pair (perm.symm b) with left | right
      · exact Or.inl (by rwa [← left,Equiv.apply_symm_apply])
      · exact Or.inr (by rwa [← right,Equiv.apply_symm_apply])

def keptInput (p : Input → Bool) (k : Nat) : Bool :=
  let row := edgeRows[k]!
  p (.leaf row.2 row.1)

private theorem edge_rows_size : edgeRows.size = 52 := by decide +kernel

theorem retained_inputs_denote (p : Input → Bool) (v : Values) (one : v 1 = true)
    (leaves : Array Leaf) (bank : LeafBank p v leaves.toList) :
    ArrayDenotes v 52 (keptInput p) (retainedInputs leaves) := by
  refine ⟨by simp [retainedInputs,edge_rows_size],?_⟩
  intro k hk
  have bound : k < edgeRows.size := by rwa [edge_rows_size]
  have member : edgeRows[k]! ∈ edgeRows.toList := by
    rw [getElem!_pos edgeRows k bound]
    exact Array.getElem_mem_toList bound
  have read := bank_retained bank one edgeRows[k]! member
  have m : k < (retainedInputs leaves).size := by simpa [retainedInputs,edge_rows_size] using hk
  rw [getElem!_pos (retainedInputs leaves) _ m]
  unfold Denotes
  simpa only [retainedInputs, Array.getElem_map,Array.toArray_toList,keptInput,getElem!_pos edgeRows k bound] using read

private theorem row_bounds : ∀ k : Fin 52,
    let row := edgeRows[k.val]!
    row.1 < 13 ∧ 13 ≤ row.2 ∧ row.2 < 26 := by decide +kernel

private theorem kept_input_physical (r : Relabelling) (other : Input → Bool) (k : Fin 52) :
    let (p,l) := edgePairAt k.val
    keptInput (physicalLeaves S r other) k.val = true ↔ pt (r.inverse.point p) ∈ leaf S (r.inverse.line l) := by
  obtain ⟨pb,lo,hi⟩ := row_bounds k
  let point := (edgePairAt k.val).1
  let line := (edgePairAt k.val).2
  have pEq : point.val = edgeRows[k.val]!.1 := by
    change edgeRows[k.val]!.1 % 13 = _
    exact Nat.mod_eq_of_lt pb
  have lEq : 13+line.val = edgeRows[k.val]!.2 := by
    change 13+(edgeRows[k.val]!.2 - 13) % 13 = _
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  change physicalLeaves S r other (.leaf edgeRows[k.val]!.2 edgeRows[k.val]!.1) = true ↔
    pt (r.inverse.point point) ∈ leaf S (r.inverse.line line)
  rw [← pEq,← lEq]
  exact physicalLeaves_bit S r other point line

private theorem positive_pullback (r : Relabelling) (k : Fin 52) :
    let (p,l) := edgePairAt k.val
    sampleInput k.val ∘ r.vertex = pairInput (pt (r.inverse.point p)) (ln (r.inverse.line l)) := by
  obtain ⟨_,agree⟩ := positive_sample_exact k
  let p := (edgePairAt k.val).1
  let l := (edgePairAt k.val).2
  have pe : r.point (r.inverse.point p) = p := r.inverse.pointInjective (by rw [point_inverse])
  have le : r.line (r.inverse.line l) = l := r.inverse.lineInjective (by rw [line_inverse])
  change sampleInput k.val ∘ r.vertex = pairInput (pt (r.inverse.point p)) (ln (r.inverse.line l))
  have inputEq : sampleInput k.val = pairInput (pt p) (ln l) := funext agree
  calc
    sampleInput k.val ∘ r.vertex = pairInput (pt p) (ln l) ∘ r.vertex := by rw [inputEq]
    _ = pairInput (pt (r.inverse.point p)) (ln (r.inverse.line l)) := by
      conv_lhs => rw [← pe,← le]
      exact pair_pullback r _ _

def stageValues (A : GateSchedule P) (r : Relabelling) (mute : Option Nat) (n j k : Nat) : Bool :=
  evalSchedule (A.stage (sampleInput k ∘ r.vertex)) mute n j

def beforeStageActivity (A : GateSchedule P) (r : Relabelling) (mute : Option Nat) (i : Fin 5)
    (k : Nat) : Bool :=
  A.stage (sampleInput k ∘ r.vertex) i.val (fun j => stageValues A r mute i.val j k)

private theorem before_first_value (A : GateSchedule P) (ao : IsAO2 26 C) (r : Relabelling)
    (refinement : Refinement) (first : Fin 5) (k : Nat) :
    beforeStageActivity A r (replayMute refinement first) first k =
      gateVal 26 C (gateOrder count (A.index.symm first)).val (sampleInput k ∘ r.vertex) := by
  unfold beforeStageActivity stageValues
  unfold replayMute
  split
  · rw [mute_below _ _ _ (Nat.le_refl _),replay_stage_value A ao]
  · exact replay_stage_value A ao _ first

private theorem positive_lookup (u w : Fin 13) (inc : incident u w) :
    ∃ k : Fin 52, edgePairAt k.val = (u,w) := by
  have yes : (u,w) ∈ positives := Finset.mem_filter.mpr ⟨Finset.mem_univ _,inc⟩
  rw [← edge_pairs_exact.1] at yes
  obtain ⟨k,hk,eq⟩ := List.mem_map.mp (List.mem_toFinset.mp yes)
  exact ⟨⟨k,List.mem_range.mp hk⟩,eq⟩

theorem physical_first_activity (A : GateSchedule P) (ao : IsAO2 26 C) (first : Fin 5)
    (centre : Option (Fin 13)) (noneMask : centre = none ↔ A.masks.2 = 0)
    (choice : ReplayChoice S A.masks (gateOrder count (A.index.symm first)).val centre)
    (active : Bool) (selected : (mode choice.refinement).1 = some active) :
    let r := choice.coordinates
    FirstActivity active A.masks.2 (keptInput (physicalLeaves S r (replayInputs A r)))
      (beforeStageActivity A r (replayMute choice.refinement first) first) := by
  let r := choice.coordinates
  let p := physicalLeaves S r (replayInputs A r)
  let on := beforeStageActivity A r (replayMute choice.refinement first) first
  let gate := (gateOrder count (A.index.symm first)).val
  have witness (xp xl : Fin 13) (h : residualOn S gate xp xl)
      (k : Fin 52) (matchRow : edgePairAt k.val = (r.point xp,r.line xl)) :
      (!keptInput p k.val && on k.val) = true := by
    apply Bool.and_eq_true_iff.mpr
    have matchesInput := positive_pullback r k
    rw [matchRow] at matchesInput
    change sampleInput k.val ∘ r.vertex =
      pairInput (pt (r.inverse.point (r.point xp))) (ln (r.inverse.line (r.line xl))) at matchesInput
    rw [point_inverse,line_inverse] at matchesInput
    refine ⟨?_,?_⟩
    · have kept := kept_input_physical (S := S) r (replayInputs A r) k
      rw [matchRow] at kept
      change keptInput p k.val = true ↔
        pt (r.inverse.point (r.point xp)) ∈ leaf S (r.inverse.line (r.line xl)) at kept
      rw [point_inverse,line_inverse] at kept
      have off : keptInput p k.val = false := Bool.eq_false_iff.mpr (fun yes => h.2.1 (kept.mp yes))
      rw [off,Bool.not_false]
    · change beforeStageActivity A r (replayMute choice.refinement first) first k.val = true
      rw [before_first_value A ao,matchesInput]
      exact h.2.2
  cases active with
  | true =>
    obtain ⟨xp,xl,res,specified⟩ := choice.active selected
    change if A.masks.2 = 0 then on 0 = true else ∃ k < 52, (!keptInput p k && on k) = true
    split
    · rename_i zero
      have anchor := specified (noneMask.mpr zero)
      have firstRow : edgePairAt 0 = (0,0) := by decide +kernel
      have fire := witness xp xl res (0 : Fin 52) (by
        change edgePairAt 0 = _
        rw [firstRow,anchor.1,anchor.2])
      exact (Bool.and_eq_true_iff.mp fire).2
    · obtain ⟨k,hk⟩ := positive_lookup _ _ ((r.incidence xp xl).mpr res.1)
      exact ⟨k.val,k.isLt,witness xp xl res k hk⟩
  | false =>
    change ∀ k < 52, (!keptInput p k && on k) = false
    intro n hn
    apply Bool.eq_false_iff.mpr
    intro fire
    let k : Fin 52 := ⟨n,hn⟩
    let xp := r.inverse.point (edgePairAt n).1
    let xl := r.inverse.line (edgePairAt n).2
    have inc : incident xp xl := (r.inverse.incidence _ _).mpr (positive_sample_exact k).1
    have missing : pt xp ∉ leaf S xl := fun mem => by
      have kept : keptInput p n = true := (kept_input_physical r (replayInputs A r) k).mpr mem
      have notKept := (Bool.and_eq_true_iff.mp fire).1
      rw [kept] at notKept
      contradiction
    have onGate := (Bool.and_eq_true_iff.mp fire).2
    change beforeStageActivity A r (replayMute choice.refinement first) first n = true at onGate
    rw [before_first_value A ao,positive_pullback r k] at onGate
    exact choice.quiet selected xp xl ⟨inc,missing,onGate⟩

end
end SixEdge.Plane
