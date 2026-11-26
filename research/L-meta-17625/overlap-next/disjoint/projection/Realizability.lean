import FiveSchedule
import PhysicalTopSelectors
import ProjectedTops
import NormalizeTips

namespace DisjointEdgeBound
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open FiveRows FiveFacts DisjointProjected

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
variable {v : Fin 5 → Fin n}

private theorem top_val (ao : IsAO2 n C) (t : tops G C) (p : Fin 2) (x : Fin n → Bool) :
    (val C (List.ofFn x) (opnd C t p) && val C (List.ofFn x) (opnd C t (1-p))) =
      gateVal n C t x := by
  apply Bool.eq_iff_iff.mpr
  rw [Bool.and_eq_true,andValOperands ao (topData t.2).1 (topData t.2).2.1]
  constructor
  · rintro ⟨l,r⟩ j
    rcases opposite p j with eq|eq
    · exact eq ▸ l
    · exact eq ▸ r
  · intro h; exact ⟨h _,h _⟩

/-- Any counterexample would pass the concrete ten-row Boolean test with
one fixed selector for each gate input and each terminal. -/
theorem realizes_in_situation (D : Situation G C v) (four : NoFourCycle G)
    (least : IsLeastAO G C) (top : TopForm G C)
    (twoAnd : (junk G C).card = 2) (twoOr : (orN G C \ lam G C).card = 2) :
    ∃ (op : Fin 4 → Bool) (p : Fin 4 → Fin 2 → P)
        (l r : BitVec 12) (c : BitVec 9),
      (Finset.univ.filter fun i => op i = true).card = 2 ∧
      realizes (inside D) (cross G v) (op 0) (op 1) (op 2) (op 3)
        (p 0 0) (p 0 1) (p 1 0) (p 1 1) (p 2 0) (p 2 1) (p 3 0) (p 3 1) l r c = true := by
  classical
  obtain ⟨s⟩ := FiveSchedule.exists_schedule D four least.1 top twoAnd twoOr
  let R := D.guards
  let ins := inside D
  let cr := cross G v
  let ng := negative cr
  let o (t : tops G C) (p : Fin 2) := PEqualNP.TopForm.side (n := n) C t p
  let w := s.ws
  have ports (t : tops G C) (p : Fin 2) (present : (o t p).Nonempty) :
      ∃ k : BitVec 4, DisjointProjected.side (raw v (o t p)) k (w 0) (w 1) (w 2) (w 3) =
        signal v C (opnd C t p) :=
    PhysicalTopSelectors.encode_side least.1 v s.ids w s.all
      (fun k h => (s.matched k h).trans (FiveSchedule.physical ..)) t p present
  have outsideOff (t : tops G C) (out : ¬ (ins = true ∧ R.center t = v 2)) (k : Fin 10) :
      input v k (R.center t) = false := by
    apply Bool.eq_false_iff.mpr; intro yes
    obtain ⟨i,eq,_⟩ := of_decide_eq_true yes
    exact off_vertex D t out i eq
  have portPos (t : tops G C) : (o t (R.port t)).Nonempty := by simp [o,R,R.raw]
  have leafPos (t : tops G C) : (o t (1-R.port t)).Nonempty := ⟨_,R.member t⟩
  have outsideCode (t : tops G C) (out : ¬ (ins = true ∧ R.center t = v 2)) :
      ∃ sel, ∀ k : Fin 10, (outsideTop ins ng sel (w 0) (w 1) (w 2) (w 3)).getLsbD k =
        gateVal n C t (input v k) := by
    obtain ⟨u,hu⟩ := ports t _ (portPos t)
    obtain ⟨s',hs⟩ := ports t _ (leafPos t)
    have raw0 : raw v (o t (R.port t)) = 0 := by
      change raw v (PEqualNP.TopForm.side (n := n) C t (R.port t)) = 0
      rw [R.raw]; exact raw_outside v _ (off_vertex D t out)
    rw [raw0] at hu
    obtain ⟨tag,htag⟩ := allowed_tag v D.inj (o t (1-R.port t)) (top_allowed D four least.1 t _)
    obtain ⟨sel,eq⟩ := PhysicalTopSelectors.outside_selectors ins ng tag u s' (w 0) (w 1) (w 2) (w 3) (by
      rw [hu]
      cases hi : ins with
      | true => exact inside_guard D least.1 hi t
      | false => rw [htag]; exact outside_guard D least.1 four hi t)
    refine ⟨sel,fun k => ?_⟩
    rw [eq,htag,hu,hs,BitVec.getLsbD_and,signal_bit,signal_bit]
    exact top_val least.1 t _ _
  have centerCode (t : tops G C) (_ : ins = true) (eq : R.center t = v 2) :
      ∃ sel, ∀ k : Fin 10, (centerTop cr sel (w 0) (w 1) (w 2) (w 3)).getLsbD k =
        gateVal n C t (input v k) := by
    obtain ⟨u,hu⟩ := ports t _ (portPos t)
    obtain ⟨s',hs⟩ := ports t _ (leafPos t)
    have raw4 : raw v (o t (R.port t)) = 4 := by
      change raw v (PEqualNP.TopForm.side (n := n) C t (R.port t)) = 4
      rw [R.raw,eq]; exact raw_middle_tip D.inj
    rw [raw4] at hu
    have useE : ∃ flag : Bool, (if cr && flag then 16 else 0) = raw v (o t (1-R.port t)) := by
      rcases center_leaf D least.1 t eq with zero|⟨crossed,full⟩
      · exact ⟨false,by simpa only [Bool.and_false,Bool.false_eq_true,ite_false] using zero.symm⟩
      · exact ⟨true,by change (if cross G v && true then _ else _) = _; simp [crossed,full,o,R]⟩
    obtain ⟨hasE,rawE⟩ := useE
    obtain ⟨sel,formula⟩ := PhysicalTopSelectors.inside_selectors cr hasE u s' (w 0) (w 1) (w 2) (w 3)
    refine ⟨sel,fun k => ?_⟩
    rw [formula,rawE,hu,hs,BitVec.getLsbD_and,signal_bit,signal_bit]
    exact top_val least.1 t _ _
  obtain ⟨left,right,center,ok⟩ := ProjectedTops.select R least (Nat.le_of_eq twoOr) (input v)
    ins cr ng (w 0) (w 1) (w 2) (w 3) outsideOff outsideCode centerCode
  refine ⟨s.op,s.ps,left,right,center,s.twoOr,?_⟩
  rw [s.realizes_eq]
  let output := outsideTop ins ng left (w 0) (w 1) (w 2) (w 3) |||
    outsideTop ins ng right (w 0) (w 1) (w 2) (w 3) |||
    (if ins then centerTop cr center (w 0) (w 1) (w 2) (w 3) else 0)
  change (output &&& ng == 0 && output &&& positive cr == positive cr) = true
  rw [Bool.and_eq_true,beq_iff_eq,beq_iff_eq]
  refine ⟨and_zero (fun k m => (ok k).trans (row_negative D k m)),?_⟩
  apply PathBits.bit_ext; intro k; rw [BitVec.getLsbD_and]
  cases h : (positive cr).getLsbD k
  · simp
  · have on : output.getLsbD k = true := (ok k).trans (row_positive D k h)
    rw [on]; rfl

/-- The only independent finite obligation in the reduction. -/
def FiniteExclusion : Prop :=
  ∀ (i x : Bool), (x = true → i = true) → ∀ (op : Fin 4 → Bool),
    (Finset.univ.filter fun j => op j = true).card = 2 →
    ∀ (p : Fin 4 → Fin 2 → P) (l r : BitVec 12) (c : BitVec 9),
    realizes i x (op 0) (op 1) (op 2) (op 3)
      (p 0 0) (p 0 1) (p 1 0) (p 1 1) (p 2 0) (p 2 1) (p 3 0) (p 3 1) l r c = false

theorem bound_of_exclusion (finite : FiniteExclusion) (four : NoFourCycle G) (bip : G.IsBipartite)
    (edges : G.edgeFinset.Nonempty) (least : IsLeastAO G C) (top : TopForm G C)
    (S : Finset (Fin n)) (f : S → Fin n) (inj : Function.Injective f)
    (partners : ∀ i, f i ∉ S ∧ G.Adj i.val (f i))
    (v : Fin 5 → Fin n) (distinct : Function.Injective v)
    (shape : Ustar G C = PrivateMatching.shape (v 0) (v 1) (v 2) (v 3) (v 4)) :
    GeneralThree.wireBound G C S := by
  classical
  have three : (Ustar G C).card = 3 := by
    rw [shape]
    simp [PrivateMatching.shape,distinct.eq_iff]
  by_contra fail
  obtain ⟨both,_,ors,_⟩ := GeneralThree.remaining G C four edges least top three S f inj partners fail
  obtain ⟨u,⟨D⟩⟩ := NormalizeTips.normalize bip four edges least top three S f inj partners fail v distinct shape
  obtain ⟨op,p,l,r,c,size,yes⟩ := realizes_in_situation D four least top both ors
  exact Bool.noConfusion (yes.symm.trans (finite _ _ (cross_inside D) _ size p l r c))

#print axioms realizes_in_situation
#print axioms bound_of_exclusion
end DisjointEdgeBound
