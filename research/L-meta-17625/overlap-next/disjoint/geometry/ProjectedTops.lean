import PrivateMatching
import PhysicalPortMasks
import ProjectedSchedule

namespace ProjectedTops
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open DisjointProjected

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- Two option slots represent any family of at most two objects, including the empty family. -/
private theorem two_slots {α : Type*} (K : Finset α) (bound : K.card ≤ 2) :
    ∃ l r : Option α, ∀ t, t ∈ K ↔ l = some t ∨ r = some t := by
  classical
  by_cases ht : K.card = 2
  · obtain ⟨p,q,_,rfl⟩ := Finset.card_eq_two.mp ht
    exact ⟨some p,some q,by simp [eq_comm]⟩
  by_cases ho : K.card = 1
  · obtain ⟨p,rfl⟩ := Finset.card_eq_one.mp ho
    exact ⟨some p,none,by simp [eq_comm]⟩
  have empty := Finset.card_eq_zero.mp (show K.card = 0 by omega)
  exact ⟨none,none,by simp [empty]⟩

private theorem graph_tops (least : IsLeastAO G C) (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ t : tops G C, gateVal n C t x = true := by
  constructor
  · intro yes
    simp [graphFun] at yes
    obtain ⟨u,v,adj,hu,hv⟩ := yes
    obtain ⟨t,mt,on⟩ := acceptedTop least adj
    refine ⟨⟨t,mt⟩,?_⟩
    rw [gateVal_eq_val] at on ⊢
    apply StarGrowth.wire_mono least.1 _ _ on
    · intro w hit
      rcases (pairInput_true _ _ _).mp hit with rfl|rfl <;> assumption
    · have len := (topData mt).1; omega
  · rintro ⟨t,on⟩; exact (topData t.2).2.2 x on

theorem zero_outside (inside : Bool) (neg : T) (g h i j : Wire) :
    outsideTop inside neg 0 g h i j = 0 := by
  simp [outsideTop,DisjointProjected.side,literal,includeOr]

theorem zero_center (cross : Bool) (g h i j : Wire) : centerTop cross 0 g h i j = 0 := by
  simp [centerTop,DisjointProjected.side,literal,includeOr]

/-- At most two outside centers can contribute on a projected input family.
A globally nonempty exceptional OR feeding a given singleton center has
exactly that center as its raw support, so it can belong to only one top. -/
theorem select {a b c d e : Fin n} (R : PrivateMatching.Guards G C a b c d e)
    (least : IsLeastAO G C) (budget : (orN G C \ lam G C).card ≤ 2)
    (x : Fin 10 → Fin n → Bool) (inside cross : Bool) (neg : T) (g h i j : Wire)
    (outsideOff : ∀ t : tops G C, ¬ (inside = true ∧ R.center t = c) →
      ∀ k, x k (R.center t) = false)
    (outsideCode : ∀ t : tops G C, ¬ (inside = true ∧ R.center t = c) →
      ∃ sel, ∀ k : Fin 10, (outsideTop inside neg sel g h i j).getLsbD k.val = gateVal n C t (x k))
    (centerCode : ∀ t : tops G C, inside = true → R.center t = c →
      ∃ sel, ∀ k : Fin 10, (centerTop cross sel g h i j).getLsbD k.val = gateVal n C t (x k)) :
    ∃ l r m, ∀ k : Fin 10,
      ((outsideTop inside neg l g h i j ||| outsideTop inside neg r g h i j |||
       (if inside then centerTop cross m g h i j else 0)).getLsbD k.val) = graphFun G ∅ (x k) := by
  classical
  let special (t : tops G C) := inside = true ∧ R.center t = c
  let K := Finset.univ.filter (fun t : tops G C =>
    ¬ special t ∧ (PhysicalPortMasks.sources G C t (R.port t)).Nonempty)
  have km (t : tops G C) : t ∈ K ↔ ¬ special t ∧ (PhysicalPortMasks.sources G C t (R.port t)).Nonempty := by
    simp [K]
  let pick (t : K) := ((km t.val).mp t.2).2.choose
  have spec (t : K) : pick t ∈ PhysicalPortMasks.sources G C t.val (R.port t.val) :=
    ((km t.val).mp t.2).2.choose_spec
  have sub : Finset.univ.image pick ⊆ orN G C \ lam G C := by
    intro h mem; obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp mem
    exact (PhysicalPortMasks.source_data (spec t)).1
  have pinj : Function.Injective pick := by
    intro u v eq
    apply Subtype.ext
    apply PhysicalPortMasks.center_owner R.port R.center R.distinctCenters R.raw (spec u)
    simpa only [eq] using spec v
  have size := (Finset.card_le_card sub).trans budget
  rw [Finset.card_image_of_injective _ pinj,Finset.card_univ,Fintype.card_coe] at size
  obtain ⟨o₀,o₁,slots⟩ := two_slots K size
  let selO (t : tops G C) : BitVec 12 := if ho : ¬special t then (outsideCode t ho).choose else 0
  have selO_eq (t : tops G C) (ho : ¬special t) (k : Fin 10) :
      (outsideTop inside neg (selO t) g h i j).getLsbD k.val = gateVal n C t (x k) := by
    simp only [selO,dite_eq_left ho]; exact (outsideCode t ho).choose_spec k
  let repr (o : Option (tops G C)) := o.elim 0 selO
  have outSpec (o : Option (tops G C)) (good : ∀ t, o = some t → t ∈ K) (k : Fin 10) :
      (outsideTop inside neg (repr o) g h i j).getLsbD k.val = true ↔
      ∃ t, o = some t ∧ gateVal n C t (x k) = true := by
    cases o with
    | none =>
      change (outsideTop inside neg 0 g h i j).getLsbD k.val = true ↔ _
      rw [zero_outside]; simp
    | some t =>
      change (outsideTop inside neg (selO t) g h i j).getLsbD k.val = true ↔ _
      rw [selO_eq t ((km t).mp (good t rfl)).1 k]; simp
  let owns := ∃ t, special t
  let m : BitVec 9 := if ownsH : owns then
      (centerCode ownsH.choose ownsH.choose_spec.1 ownsH.choose_spec.2).choose else 0
  have cSpec (k : Fin 10) : (if inside then centerTop cross m g h i j else (0 : T)).getLsbD k.val = true ↔
      ∃ t, special t ∧ gateVal n C t (x k) = true := by
    by_cases owned : owns
    · have owner := owned.choose_spec
      have hi := owner.1
      have val := (centerCode owned.choose hi owner.2).choose_spec k
      simp only [hi,ite_true,m,dite_eq_left owned,val]
      constructor
      · intro on; exact ⟨owned.choose,owner,on⟩
      · rintro ⟨t,sp,on⟩
        have eq := R.distinctCenters (sp.2.trans owner.2.symm)
        exact eq ▸ on
    · have none : ¬ ∃ t, special t ∧ gateVal n C t (x k) = true := fun ⟨t,sp,_⟩ => owned ⟨t,sp⟩
      have mz : m = 0 := by simp [m,owned]
      rw [mz,zero_center,ite_self]; simp [none]
  refine ⟨repr o₀, repr o₁,m,?_⟩
  intro k
  apply Bool.eq_iff_iff.mpr
  rw [BitVec.getLsbD_or,BitVec.getLsbD_or,Bool.or_eq_true,Bool.or_eq_true,
    outSpec o₀ (fun t h => (slots t).mpr (.inl h)),outSpec o₁ (fun t h => (slots t).mpr (.inr h)),
    cSpec,graph_tops least]
  constructor
  · rintro ((⟨t,_,on⟩ | ⟨t,_,on⟩) | ⟨t,_,on⟩) <;> exact ⟨t,on⟩
  · rintro ⟨t,on⟩
    by_cases sp : special t
    · exact Or.inr ⟨t,sp,on⟩
    have val := (andValOperands least.1 (topData t.2).1 (topData t.2).2.1 _).mp on (R.port t)
    have raw : (PEqualNP.TopForm.side (n := n) C t (R.port t)).Nonempty := by rw [R.raw]; simp
    have source : (PhysicalPortMasks.sources G C t (R.port t)).Nonempty := by
      rcases (PhysicalPortMasks.port_value (G := G) least.1 (topData t.2).1 (R.port t) raw (x k)).mp val with ⟨v,mv,hv⟩|⟨h,mh,_⟩
      · rw [R.raw,Finset.mem_singleton] at mv
        exact (Bool.false_ne_true ((outsideOff t sp k).symm.trans (mv ▸ hv))).elim
      · exact ⟨h,mh⟩
    rcases (slots t).mp ((km t).mpr ⟨sp,source⟩) with hl|hr
    · exact Or.inl (Or.inl ⟨t,hl,on⟩)
    · exact Or.inl (Or.inr ⟨t,hr,on⟩)

#print axioms select
end ProjectedTops
