import PhysicalScheduleProjection

namespace PhysicalSchedule
open DisjointProjected
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
attribute [local instance] gateOpDecEq

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

structure Schedule (p : Projection G C) where
  ids : Fin 4 ↪o ℕ
  all : ∀ k, k ∈ P4Ports.active G C → ∃ i, ids i = k
  ws : Fin 4 → Wire
  matched : ∀ i, ids i ∈ P4Ports.active G C → ws i = p.physical (n+ids i)
  op : Fin 4 → Bool
  ps : Fin 4 → Fin 2 → P
  step : ∀ i, ws i = gate (op i)
    (port (ps i 0) (previous ws i 0) (previous ws i 1) (previous ws i 2))
    (port (ps i 1) (previous ws i 0) (previous ws i 1) (previous ws i 2))
  twoOr : (Finset.univ.filter fun i => op i = true).card = 2

theorem stage_port (p : Projection G C) (ao : IsAO2 n C) (top : TopForm G C)
    (ids : Fin 4 ↪o ℕ) (all : ∀ k, k ∈ P4Ports.active G C → ∃ i, ids i = k)
    (ws : Fin 4 → Wire) (matched : ∀ i, ids i ∈ P4Ports.active G C → ws i = p.physical (n+ids i))
    (i : Fin 4) (active : ids i ∈ P4Ports.active G C) (b : Fin 2) :
    ∃ s, port s (previous ws i 0) (previous ws i 1) (previous ws i 2) =
      p.physical (opnd C (ids i) b) := by
  classical
  let x := previous ws i
  have earlier (k : ℕ) (ac : k ∈ P4Ports.active G C) (lt : k < ids i) :
      ∃ j : Fin 3, j.castSucc < i ∧ ids j.castSucc = k := by
    obtain ⟨j,eq⟩ := all _ ac
    have earlier : j < i := ids.lt_iff_lt.mp (by simpa only [eq] using lt)
    have jsmall : j.val < 3 := by have := i.isLt; omega
    exact ⟨⟨j.val,jsmall⟩,earlier,eq⟩
  rcases PhysicalPortMasks.port_law ao top (fun r => ∃ tag, rawMask tag = p.mask r)
      p.tag_lit p.tag_lam active b with ⟨k,ac,lt,wire⟩|⟨raw,⟨tag,htag⟩,keys,spec⟩
  · obtain ⟨j,small,eq⟩ := earlier _ ac lt
    obtain ⟨s,port⟩ := directSel x j
    refine ⟨s,port.trans ?_⟩
    change previous ws i j = p.physical (opnd C (ids i) b)
    rw [previous,ite_eq_left small,matched _ (eq ▸ ac),eq,wire]
  let K := PhysicalPortMasks.sources G C (ids i) b
  let R0 := side (n := n) C (ids i) b
  let m := p.mask R0
  let keep (j : Fin 3) := decide (j.castSucc < i ∧ ids j.castSucc ∈ K)
  have saved (j : Fin 3) (yes : keep j = true) :
      x j = p.physical (n+ids j.castSucc) := by
    obtain ⟨small,mem⟩ := of_decide_eq_true yes
    exact (ite_eq_left small).trans (matched _ (keys _ mem).1)
  have eligible (j : Fin 3) (yes : keep j = true) :
      (x j).nz = true ∧ (x j).raw &&& ~~~m = 0 := by
    rw [saved _ yes]
    obtain ⟨_,_,_,ne,sub⟩ := keys _ (of_decide_eq_true yes).2
    exact ⟨decide_eq_true ne,p.raw_sub sub⟩
  have eqVal : (literal m ||| includeOr m (keep 0) (x 0) ||| includeOr m (keep 1) (x 1) |||
      includeOr m (keep 2) (x 2)) = (p.physical (opnd C (ids i) b)).val := by
    apply PathBits.bit_ext; intro row
    apply Bool.eq_iff_iff.mpr
    rw [merge_spec m keep x row eligible]
    change _ ↔ (PathBits.pack _).getLsbD row = true
    rw [PathBits.get_pack,spec]
    rw [show (literal m).getLsbD row = true ↔ _ from p.literal_spec R0 row]
    apply or_congr_right
    constructor
    · rintro ⟨j,kept,on⟩
      refine ⟨_,(of_decide_eq_true kept).2,?_⟩
      rw [saved _ kept] at on
      simpa only [Projection.physical,PathBits.get_pack,gateVal_eq_val] using on
    · rintro ⟨k,mem,on⟩
      obtain ⟨j,small,eq⟩ := earlier k (keys _ mem).1 (keys _ mem).2.1
      have yes : keep j = true := decide_eq_true ⟨small,eq ▸ mem⟩
      refine ⟨j,yes,?_⟩
      rw [saved _ yes,eq]
      simpa only [Projection.physical,PathBits.get_pack,gateVal_eq_val] using on
  refine ⟨baseSel tag (keep 0) (keep 1) (keep 2),?_⟩
  rw [baseSel_eq,htag]
  change Wire.mk _ m true = Wire.mk _ m _
  congr 1
  · exact (decide_eq_true raw).symm

theorem encode (p : Projection G C) (ao : IsAO2 n C) (top : TopForm G C)
    (twoAnd : (junk G C).card = 2) (twoOr : (orN G C \ lam G C).card = 2) :
    Nonempty (Schedule p) := by
  classical
  let A := junk G C
  let O := orN G C \ lam G C
  let allG := A ∪ O
  have separate : Disjoint A O := by
    apply Finset.disjoint_left.mpr
    intro h ma mo
    have ha := (junkData ma).2.1
    have ho := (orData mo).2.1
    rw [ha] at ho; contradiction
  have size : allG.card = 4 := by
    change (A ∪ O).card = 4
    rw [Finset.card_union_of_disjoint separate,twoAnd,twoOr]
  let ids := allG.orderEmbOfFin size
  have rangeIds : ∀ k ∈ allG, ∃ i, ids i = k := fun k m =>
    (allG.range_orderEmbOfFin size).ge m
  have all (k) (m : k ∈ P4Ports.active G C) : ∃ i, ids i = k := by
    apply rangeIds
    rcases Finset.mem_union.mp m with a|o
    · exact Finset.mem_union_left _ a
    · exact Finset.mem_union_right _ (Finset.mem_filter.mp o).1
  let op (i : Fin 4) := PathPhysical.kind C (ids i)
  have kind (i : Fin 4) : op i = true ↔ ids i ∈ O := by
    have m := allG.orderEmbOfFin_mem size i
    change ids i ∈ allG at m
    rcases Finset.mem_union.mp m with a|o
    · have k := (junkData a).2.1
      exact ⟨fun y => by simp [op,PathPhysical.kind,k] at y,
        fun mo => (Finset.disjoint_left.mp separate a mo).elim⟩
    · exact ⟨fun _ => o,fun _ => by simp [op,PathPhysical.kind,(orData o).2.1]⟩
  have two : (Finset.univ.filter fun i => op i = true).card = 2 := by
    let F := Finset.univ.filter (fun i : Fin 4 => op i = true)
    have eq : F.image ids = O := by
      ext k
      constructor
      · rintro m
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp m
        exact (kind i).mp (Finset.mem_filter.mp hi).2
      · intro m
        obtain ⟨i,rfl⟩ := rangeIds k (Finset.mem_union_right _ m)
        exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(kind i).mpr m⟩,rfl⟩
    have cnt := congrArg Finset.card eq
    rw [Finset.card_image_of_injective _ ids.injective,twoOr] at cnt
    exact cnt
  let dummy : Wire := ⟨0,0,true⟩
  let ws (i : Fin 4) := if ids i ∈ P4Ports.active G C then p.physical (n+ids i) else dummy
  have matched (i) (h : ids i ∈ P4Ports.active G C) : ws i = p.physical (n+ids i) := ite_eq_left h
  have make (i : Fin 4) : ∃ ps : Fin 2 → P, ws i = gate (op i)
      (port (ps 0) (previous ws i 0) (previous ws i 1) (previous ws i 2))
      (port (ps 1) (previous ws i 0) (previous ws i 1) (previous ws i 2)) := by
    by_cases act : ids i ∈ P4Ports.active G C
    · choose ps h using stage_port p ao top ids all ws matched i act
      exact ⟨ps,by rw [h 0,h 1,matched i act]; exact p.gate_eq ao (P4Ports.active_length act)⟩
    · have isOr : op i = true := by
        apply (kind i).mpr
        have m := allG.orderEmbOfFin_mem size i
        exact (Finset.mem_union.mp m).resolve_left (fun a => act (Finset.mem_union_left _ a))
      refine ⟨fun _ => 0,?_⟩
      rw [isOr]
      simp [ws,act,dummy,port,mux,includeOr,rawMask,literal,gate]
  choose ps step using make
  exact ⟨⟨ids,all,ws,matched,op,ps,step,two⟩⟩

/-- Evaluate the Boolean verifier on the actual physical schedule. -/
theorem Schedule.realizes_eq {p : Projection G C} (s : Schedule p) (inside cross : Bool)
    (left right : BitVec 12) (center : BitVec 9) :
    realizes inside cross (s.op 0) (s.op 1) (s.op 2) (s.op 3)
      (s.ps 0 0) (s.ps 0 1) (s.ps 1 0) (s.ps 1 1) (s.ps 2 0) (s.ps 2 1)
      (s.ps 3 0) (s.ps 3 1) left right center =
      (let neg : T := if cross then 880 else 1016
       let pos : T := if cross then 15 else 7
       let out := outsideTop inside neg left (s.ws 0) (s.ws 1) (s.ws 2) (s.ws 3) |||
         outsideTop inside neg right (s.ws 0) (s.ws 1) (s.ws 2) (s.ws 3) |||
         (if inside then centerTop cross center (s.ws 0) (s.ws 1) (s.ws 2) (s.ws 3) else 0)
       out &&& neg == 0 && out &&& pos == pos) := by
  have first : s.ws 0 = gate (s.op 0) (port (s.ps 0 0) zero zero zero)
    (port (s.ps 0 1) zero zero zero) := s.step 0
  have second : s.ws 1 = gate (s.op 1) (port (s.ps 1 0) (s.ws 0) zero zero)
    (port (s.ps 1 1) (s.ws 0) zero zero) := s.step 1
  have third : s.ws 2 = gate (s.op 2) (port (s.ps 2 0) (s.ws 0) (s.ws 1) zero)
    (port (s.ps 2 1) (s.ws 0) (s.ws 1) zero) := s.step 2
  have fourth : s.ws 3 = gate (s.op 3) (port (s.ps 3 0) (s.ws 0) (s.ws 1) (s.ws 2))
    (port (s.ps 3 1) (s.ws 0) (s.ws 1) (s.ws 2)) := s.step 3
  unfold realizes
  dsimp only
  rw [← first,← second,← third,← fourth]

#print axioms encode
end PhysicalSchedule
