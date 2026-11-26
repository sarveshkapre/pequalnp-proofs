import SixEdgeReplayInputs

namespace SixEdge.Plane

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open PlaneFour ResidualDegree Formula

variable {C : Circuit} {S : Stars C} {count : (charged plane C).card = 5} {P : OrderedPorts S count}

def replayTopOn (A : GateSchedule P) (l : Fin 13) (x : Fin 26 → Bool) (past : Nat → Bool) : Prop :=
  (x (ln l) = true ∨ ∃ j, replayRoute A l (S.center (S.index l)) j ∧ past (A.index j).val = true) ∧
  ((∃ v ∈ leaf S l, x v = true) ∨ ∃ j, replayRoute A l (1-S.center (S.index l)) j ∧ past (A.index j).val = true)

theorem replayTop_mono (A : GateSchedule P) (l : Fin 13) (x : Fin 26 → Bool)
    {f g : Nat → Bool} (inc : f ≤ g) : replayTopOn A l x f → replayTopOn A l x g := by
  have carry (p : Prop) (route : Fin 5 → Prop) :
      (p ∨ ∃ j, route j ∧ f (A.index j).val = true) → p ∨ ∃ j, route j ∧ g (A.index j).val = true := by
    rintro (raw | ⟨j,w,on⟩)
    · exact Or.inl raw
    · exact Or.inr ⟨j,w,Bool.le_iff_imp.mp (inc _) on⟩
  exact fun h => ⟨carry _ _ h.1,carry _ _ h.2⟩

theorem replayTop_unmuted (least : IsLeastAO plane C) (top : TopForm plane C)
    (empty : centreless plane C = ∅) (l : Fin 13) (x : Fin 26 → Bool) :
    let A := GateSchedule.rawFirst P least
    replayTopOn A l x (evalSchedule (A.stage x) none 5) ↔ gateVal 26 C (S.index l).val x = true := by
  let A := GateSchedule.rawFirst P least
  let b := S.center (S.index l)
  have data := topData (S.index l).property
  have sides : (∀ c : Fin 2, val C (List.ofFn x) (opnd C (S.index l).val c) = true) ↔
      (val C (List.ofFn x) (opnd C (S.index l).val b) = true ∧
        val C (List.ofFn x) (opnd C (S.index l).val (1-b)) = true) := by
    have pair : ∀ t c : Fin 2, c = t ∨ c = 1-t := by decide
    exact ⟨fun h => ⟨h _,h _⟩, fun h c => (pair b c).elim (fun e => e.symm ▸ h.1) (fun e => e.symm ▸ h.2)⟩
  change replayTopOn A l x (evalSchedule (A.stage x) none 5) ↔ _
  rw [andValOperands least.1 data.1 data.2.1, sides,
    GateSchedule.rawFirst_top_port (P := P) least top empty l b x,
    GateSchedule.rawFirst_top_port (P := P) least top empty l (1-b) x]
  unfold replayTopOn replayRoute
  simp only [A.evaluation least.1 x 5 _ (Fin.isLt _), b, S.singleton, Finset.mem_singleton, exists_eq_left, leaf, and_assoc]
  rfl

theorem replayTop_tests (least : IsLeastAO plane C) (top : TopForm plane C)
    (empty : centreless plane C = ∅) (mute : Option Nat)
    (quiet : ∀ m, mute = some m → ∀ p l : Fin 13, plane.Adj (pt p) (ln l) → pt p ∉ leaf S l →
      let A := GateSchedule.rawFirst P least
      let x := pairInput (pt p) (ln l)
      A.stage x m (evalSchedule (A.stage x) none m) = false) :
    let A := GateSchedule.rawFirst P least
    (∀ p l : Fin 13, plane.Adj (pt p) (ln l) → let x := pairInput (pt p) (ln l)
      ∃ j, replayTopOn A j x (evalSchedule (A.stage x) mute 5)) ∧
    (∀ x, graphFun plane ∅ x = false → ∀ l, ¬ replayTopOn A l x (evalSchedule (A.stage x) mute 5)) := by
  let A := GateSchedule.rawFirst P least
  constructor
  · intro p l adj
    let x := pairInput (pt p) (ln l)
    change ∃ j, replayTopOn A j x (evalSchedule (A.stage x) mute 5)
    by_cases retained : pt p ∈ leaf S l
    · exact ⟨l, Or.inl (pairInput_right _ _), Or.inl ⟨pt p,retained,pairInput_left _ _⟩⟩
    obtain ⟨j,on⟩ := (test_obligations S least).1 p l adj
    have before := (replayTop_unmuted (P := P) least top empty j x).mpr on
    cases mute with
    | none => exact ⟨j,before⟩
    | some m =>
      refine ⟨j,?_⟩
      rw [mute_when_off _ (quiet m rfl p l adj retained)]
      exact before
  · intro x off l on
    have monotone : evalSchedule (A.stage x) mute 5 ≤ evalSchedule (A.stage x) none 5 := by
      cases mute with
      | none => exact le_rfl
      | some m => exact mute_monotone _ (A.stage_monotone x) m 5
    have h := (replayTop_unmuted (P := P) least top empty l x).mp (replayTop_mono A l x monotone on)
    exact Bool.false_ne_true (off.symm.trans ((topData (S.index l).property).2.2 x h))

theorem pair_pullback (r : Relabelling) (p l : Fin 13) :
    pairInput (pt (r.point p)) (ln (r.line l)) ∘ r.vertex = pairInput (pt p) (ln l) := by
  funext v
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, pairInput_true, ← point_vertex r p, ← line_vertex r l]
  exact or_congr ⟨fun h => r.vertex_injective h,congrArg _⟩ ⟨fun h => r.vertex_injective h,congrArg _⟩

theorem replay_stage_value (A : GateSchedule P) (ao : IsAO2 26 C) (x : Fin 26 → Bool) (i : Fin 5) :
    A.stage x i.val (evalSchedule (A.stage x) none i.val) = gateVal 26 C (gateOrder count (A.index.symm i)).val x := by
  have val := A.evaluation ao x (i.val+1) (A.index.symm i) (by simp)
  simpa [evalSchedule] using val

def replayMute (refinement : Refinement) (i : Fin 5) : Option Nat :=
  if (mode refinement).1 = some false then some i.val else none

theorem sample_count : samples.size = 132 := by decide +kernel

/-- All 132 exact input rows are correct for the relabelled physical model
    with the restricted top routes and the selected mute, when any. -/
theorem replay_sample_tests (least : IsLeastAO plane C) (top : TopForm plane C)
    (empty : centreless plane C = ∅) (i : Fin 5) (centre : Option (Fin 13))
    (choice : ReplayChoice S (GateSchedule.rawFirst P least).masks
      (gateOrder count ((GateSchedule.rawFirst P least).index.symm i)).val centre) :
    let A := GateSchedule.rawFirst P least
    let mute := replayMute choice.refinement i
    (∀ k < 52, let x := sampleInput k ∘ choice.coordinates.vertex
      ∃ l, replayTopOn A l x (evalSchedule (A.stage x) mute 5)) ∧
    (∀ k, 52 ≤ k → k < samples.size → let x := sampleInput k ∘ choice.coordinates.vertex
      ∀ l, ¬ replayTopOn A l x (evalSchedule (A.stage x) mute 5)) := by
  let A := GateSchedule.rawFirst P least
  let r := choice.coordinates
  let mute := replayMute choice.refinement i
  have quiet m (when : mute = some m) (p l : Fin 13) (inc : plane.Adj (pt p) (ln l))
      (miss : pt p ∉ leaf S l) :
      let x := pairInput (pt p) (ln l)
      A.stage x m (evalSchedule (A.stage x) none m) = false := by
    unfold mute replayMute at when
    split at when
    · rename_i silent
      have eq := Option.some.inj when
      subst m
      dsimp only
      rw [replay_stage_value A least.1]
      apply Bool.eq_false_iff.mpr
      intro yes
      exact choice.quiet silent p l ⟨(adj_coordinates _ _).mpr inc,miss,yes⟩
    · contradiction
  have tests := replayTop_tests (P := P) least top empty mute quiet
  constructor
  · intro k bound
    let r := choice.coordinates
    obtain ⟨inc,val⟩ := positive_sample_exact ⟨k,bound⟩
    let p := r.inverse.point (edgePairAt k).1
    let l := r.inverse.line (edgePairAt k).2
    have pe : r.point p = (edgePairAt k).1 := r.inverse.pointInjective (by rw [point_inverse])
    have le : r.line l = (edgePairAt k).2 := r.inverse.lineInjective (by rw [line_inverse])
    have adj : plane.Adj (pt p) (ln l) := (adj_coordinates p l).mp ((r.inverse.incidence _ _).mpr inc)
    have norm : sampleInput k ∘ r.vertex = pairInput (pt p) (ln l) := by
      rw [show sampleInput k = pairInput (pt (edgePairAt k).1) (ln (edgePairAt k).2) from funext val,
        ← pe,← le, pair_pullback]
    rw [norm]
    exact tests.1 p l adj
  · intro k lo hi
    have hk : k - 52 < 80 := by rw [sample_count] at hi; omega
    have neg := negative_sample_edge_free ⟨k-52,hk⟩
    have sum : k-52+52 = k := by omega
    change graphFun plane ∅ (sampleInput (k-52+52)) = false at neg
    rw [sum] at neg
    exact tests.2 _ ((r.preserves_tests _).trans neg)

#print axioms replay_sample_tests

end SixEdge.Plane
