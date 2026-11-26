import SixEdgeSchedule

namespace SixEdge.Plane

set_option maxHeartbeats 2200000

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_7465_aux
open PEqualNP.EdgeOwnership
open ResidualDegree PlaneFour

variable {C : Circuit}

def residualOn (S : Stars C) (gate : Nat) (p l : Fin 13) : Prop :=
  incident p l ∧ pt p ∉ leaf S l ∧ gateVal 26 C gate (pairInput (pt p) (ln l)) = true

def CoordinateAnchor (S : Stars C) (centre : Option (Fin 13)) (r : Relabelling) : Prop :=
  match centre with
  | none => pt (r.inverse.point 0) ∉ leaf S (r.inverse.line 0)
  | some l => r.line l = 0

def linePortShape (C : Circuit) (gate : Nat) (r : Relabelling) (n : Fin 13) : Prop :=
  ∃ b : Fin 2, ∃ l : Fin 13, r.line l = n ∧ side (n := 26) C gate b = {ln l} ∧
    (∀ v ∈ side (n := 26) C gate (1-b), v.val < 13) ∧
    ∃ v ∈ side (n := 26) C gate (1-b), ¬ plane.Adj v (ln l)

structure ReplayChoice (S : Stars C) (k : Case) (gate : Nat) (centre : Option (Fin 13)) where
  refinement : Refinement
  coordinates : Relabelling
  member : (k, refinement) ∈ keys
  anchor : CoordinateAnchor S centre coordinates
  active : (Formula.mode refinement).1 = some true →
    ∃ p l, residualOn S gate p l ∧ (centre = none → coordinates.point p = 0 ∧ coordinates.line l = 0)
  quiet : (Formula.mode refinement).1 = some false → ∀ p l, ¬ residualOn S gate p l
  shape : match refinement with
    | .points => ∀ b v, v ∈ side (n := 26) C gate b → v.val < 13
    | .centreLine => linePortShape C gate coordinates 0
    | .otherLine => linePortShape C gate coordinates 1
    | _ => True

private theorem key_at (k : Case) (hk : k ∈ cases) {r : Refinement}
    (hr : r ∈ refinements k) : (k,r) ∈ keys :=
  List.mem_flatMap.mpr ⟨k,hk,List.mem_map.mpr ⟨r,hr,rfl⟩⟩

private theorem first_from_mask : ∀ n : Fin 32, n ≠ 0 →
    let k : BitVec 5 := ⟨n⟩
    Formula.firstBit k < 5 ∧ k.getLsbD (Formula.firstBit k) = true := by decide +kernel

private theorem dirty_mask_facts : ∀ p q : Fin 32, let k : Case := (⟨p⟩,⟨q⟩);
    k ∈ cases → (p ≠ 0 ∧ (k ∉ unrefined → k.1 ≠ 6 → Formula.firstBit k.1 = 0)) := by
  decide +kernel

theorem first_dirty_facts (k : Case) (hk : k ∈ cases) :
    Formula.firstBit k.1 < 5 ∧ k.1.getLsbD (Formula.firstBit k.1) = true ∧
      (k ∉ unrefined → k.1 ≠ 6 → Formula.firstBit k.1 = 0) := by
  rcases k with ⟨⟨p⟩,⟨q⟩⟩
  obtain ⟨nz,front⟩ := dirty_mask_facts p q hk
  obtain ⟨bound,bit⟩ := first_from_mask p nz
  exact ⟨bound,bit,front⟩

private theorem first_centre_facts (k : BitVec 5) (hk : k ≠ 0) :
    Formula.firstBit k < 5 ∧ k.getLsbD (Formula.firstBit k) = true := by
  obtain ⟨q⟩ := k
  exact first_from_mask q (fun h => hk (congrArg BitVec.ofFin h))

private theorem anchor_for_pair (S : Stars C) (centre : Option (Fin 13))
    {p l : Fin 13} (h : incident p l) (off : pt p ∉ leaf S l) :
    ∃ r, CoordinateAnchor S centre r ∧ (centre = none → r.point p = 0 ∧ r.line l = 0) := by
  cases centre with
  | none =>
    obtain ⟨r,hp,hl⟩ := anchor_incidence p l h
    refine ⟨r, ?_, fun _ => ⟨hp,hl⟩⟩
    change pt (r.inverse.point 0) ∉ leaf S (r.inverse.line 0)
    have p' : r.inverse.point 0 = p := by rw [← hp,point_inverse]
    have l' : r.inverse.line 0 = l := by rw [← hl,line_inverse]
    rwa [p',l']
  | some line => exact ⟨translate (-line), by simp [CoordinateAnchor,translate], by simp⟩

/-- Choose a listed refinement from the first dirty AND's behaviour. The
    coordinates fix the earliest selected centre line, or a residual incidence
    in the no-centre case. -/
theorem select_replay_refinement (S : Stars C) (least : IsLeastAO plane C) (top : TopForm plane C)
    (six : (Ustar plane C).card = 6) (k : Case) (hk : k ∈ cases)
    (g : Nat) (dirty : g ∈ junk plane C)
    (first : k ∉ unrefined → k.1 ≠ 6 → ∀ j ∈ charged plane C, ¬ j < g)
    (centre : Option (Fin 13)) (ncn : centre = none ↔ k.2 = 0) :
    Nonempty (ReplayChoice S k g centre) := by
  classical
  have nonempty : (residualPairs S).Nonempty := Finset.card_pos.mp (by
    rw [residual_card S least.1, six]; decide)
  obtain ⟨⟨p₀,l₀⟩, h₀⟩ := nonempty
  obtain ⟨edge₀,miss₀⟩ := Finset.mem_filter.mp h₀
  obtain ⟨baseR,baseAnchor,_⟩ := anchor_for_pair S centre (Finset.mem_filter.mp edge₀).2 miss₀
  by_cases base : k ∈ unrefined
  · exact ⟨⟨.base,baseR,key_at k hk (by simp [refinements,base]),baseAnchor,
      by simp [Formula.mode],by simp [Formula.mode],trivial⟩⟩
  by_cases on : ∃ p l, residualOn S g p l
  · obtain ⟨p,l,edge,miss,fire⟩ := on
    by_cases secondSlot : k.1 = 6
    · obtain ⟨r,a,row⟩ := anchor_for_pair S centre edge miss
      exact ⟨⟨.active,r,key_at k hk (by simp [refinements,base,secondSlot]),a,
        fun _ => ⟨p,l,⟨edge,miss,fire⟩,row⟩,by simp [Formula.mode],trivial⟩⟩
    · obtain ⟨r,anchor,shape⟩ := active_first_coordinates S least top dirty (first base secondSlot) edge fire centre
      have noCentre : centre = none → r.point p = 0 ∧ r.line l = 0 := by
        rintro rfl; exact anchor
      have anchored : CoordinateAnchor S centre r := by
        cases centre with
        | none =>
          obtain ⟨a,b⟩ := anchor
          change pt (r.inverse.point 0) ∉ leaf S (r.inverse.line 0)
          have p' : r.inverse.point 0 = p := by rw [← a,point_inverse]
          have l' : r.inverse.line 0 = l := by rw [← b,line_inverse]
          rwa [p',l']
        | some _ => exact anchor
      rcases shape with pts | ⟨b,ls,ps,n,zero | one⟩
      · exact ⟨⟨.points,r,key_at k hk (by rw [refinements,ite_eq_right base,ite_eq_right secondSlot]; simp),anchored,
          fun _ => ⟨p,l,⟨edge,miss,fire⟩,noCentre⟩,by simp [Formula.mode],pts⟩⟩
      · exact ⟨⟨.centreLine,r,key_at k hk (by rw [refinements,ite_eq_right base,ite_eq_right secondSlot]; simp),anchored,
          fun _ => ⟨p,l,⟨edge,miss,fire⟩,noCentre⟩,by simp [Formula.mode],⟨b,l,zero,ls,ps,n⟩⟩⟩
      · have hasCentre : k.2 ≠ 0 := fun no => by
          have lineZero := (noCentre (ncn.mpr no)).2
          exact (by decide : (0 : Fin 13) ≠ 1) (lineZero.symm.trans one)
        exact ⟨⟨.otherLine,r,key_at k hk (by
          rw [refinements,ite_eq_right base,ite_eq_right secondSlot,ite_eq_right hasCentre]; simp),anchored,
          fun _ => ⟨p,l,⟨edge,miss,fire⟩,noCentre⟩,by simp [Formula.mode],⟨b,l,one,ls,ps,n⟩⟩⟩
  · have quiet : ∀ p l, ¬ residualOn S g p l := fun p l h => on ⟨p,l,h⟩
    by_cases firstPair : k.1 = 3
    · have neq : k.1 ≠ 6 := by rw [firstPair]; decide
      exact ⟨⟨.canonicalInactive,baseR,key_at k hk (by
        rw [refinements,ite_eq_right base,ite_eq_right neq,ite_eq_left firstPair]; simp),baseAnchor,
        by simp [Formula.mode],fun _ => quiet,trivial⟩⟩
    · have mem : .inactive ∈ refinements k := by
        rw [refinements,ite_eq_right base]
        by_cases second : k.1 = 6
        · rw [ite_eq_left second]; simp
        · rw [ite_eq_right second,ite_eq_right firstPair]; simp
      exact ⟨⟨.inactive,baseR,key_at k hk mem,baseAnchor,
        by simp [Formula.mode],fun _ => quiet,trivial⟩⟩

/-- Choose a key for the actual reordered schedule, and keep a witness for
    the centre-anchor clause when that clause is present. -/
theorem schedule_replay_choice (S : Stars C) (least : IsLeastAO plane C) (top : TopForm plane C)
    (empty : centreless plane C = ∅) (two : (junk plane C).card = 2)
    (count : (charged plane C).card = 5) (six : (Ustar plane C).card = 6)
    (P : OrderedPorts S count) (A : GateSchedule P) (order : A = GateSchedule.rawFirst P least) :
    ∃ i : Fin 5, i.val = Formula.firstBit A.masks.1 ∧ ∃ centre : Option (Fin 13),
      (centre = none ↔ A.masks.2 = 0) ∧
      (∀ l, centre = some l → ∃ j : Fin 5, j.val = Formula.firstBit A.masks.2 ∧
        A.afterDirty (A.index.symm j) ∧ topRoute S count l (S.center (S.index l)) (A.index.symm j)) ∧
      Nonempty (ReplayChoice S A.masks (gateOrder count (A.index.symm i)).val centre) := by
  classical
  have inCases := A.masks_covered least empty two
  obtain ⟨bound,on,head⟩ := first_dirty_facts A.masks inCases
  let i : Fin 5 := ⟨Formula.firstBit A.masks.1, bound⟩
  have dirtySlot : dirtyAt count (A.index.symm i) = true := by
    rw [← ofSlots_bit (fun j => dirtyAt count (A.index.symm j)) i]
    exact on
  have physicallyFirst (h : A.masks ∉ unrefined) (h6 : A.masks.1 ≠ 6) :
      ∀ j ∈ charged plane C, ¬ j < (gateOrder count (A.index.symm i)).val := by
    have eq : A.index (A.index.symm i) = 0 := by
      rw [Equiv.apply_symm_apply]
      exact Fin.ext (head h h6)
    have moved : (GateSchedule.rawFirst P least).index (A.index.symm i) = 0 := by
      rw [← order]
      exact eq
    exact GateSchedule.dirty_at_head_is_first (P := P) (i := A.index.symm i) least moved dirtySlot
  refine ⟨i,rfl,?_⟩
  have select (centre : Option (Fin 13)) (noneIff : centre = none ↔ A.masks.2 = 0) :=
    select_replay_refinement S least top six A.masks inCases _ (of_decide_eq_true dirtySlot) physicallyFirst centre noneIff
  by_cases noCentre : A.masks.2 = 0
  · have h : (none : Option (Fin 13)) = none ↔ A.masks.2 = 0 := by simp [noCentre]
    exact ⟨none,h,by simp,select none h⟩
  · let firstCentre := first_centre_facts A.masks.2 noCentre
    let j : Fin 5 := ⟨Formula.firstBit A.masks.2,firstCentre.1⟩
    have centreOn : (A.masks.2).getLsbD j = true := firstCentre.2
    have data : A.afterDirty (A.index.symm j) ∧ ∃ l, topRoute S count l (S.center (S.index l)) (A.index.symm j) := by
      simp only [GateSchedule.masks, ofSlots_bit] at centreOn
      exact of_decide_eq_true centreOn
    obtain ⟨after,l,route⟩ := data
    have h : some l = none ↔ A.masks.2 = 0 := by
      constructor
      · intro impossible
        cases impossible
      · intro e
        exact (noCentre e).elim
    refine ⟨some l,h,?_,select (some l) h⟩
    intro l' eq
    have same := Option.some.inj eq
    subst l'
    exact ⟨j,rfl,after,route⟩

#print axioms select_replay_refinement
#print axioms schedule_replay_choice

end SixEdge.Plane
