import MatchingPorts
import SharedSwitch

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing

namespace GuardedPairs
variable {n k : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- One accepting top per pair is enough. On each independent input, one
chosen port of each such top must fire. Its opposite wire then stays off,
and those opposite wires distinguish every positive pair from every corner.
No condition is placed on the remaining tops. -/
theorem count (ao : IsAO2 n C) (top : TopForm G C)
    (e : Fin k → Bool → Fin n) (a : Fin k → tops G C) (guard : Fin k → Fin 2)
    (positive : ∀ i, gateVal n C (a i) (pairInput (e i false) (e i true)) = true)
    (neg : (Fin k → Bool) → Fin n → Bool)
    (contains : ∀ mask i, neg mask (e i (mask i)) = true)
    (noedge : ∀ mask, graphFun G ∅ (neg mask) = false)
    (hit : ∀ mask i, ∃ w ∈ side (n := n) C (a i) (guard i), neg mask w = true) :
    k ≤ (junk G C).card := by
  classical
  let output (i : Fin k) := opnd C (a i) (1 - guard i)
  let W : Set ℕ := Set.range output
  have under (w : ℕ) (hw : w ∈ W) : SharedSwitch.belowAnd n C w := by
    obtain ⟨i,rfl⟩ := hw
    exact ⟨a i,(topData (a i).2).1,(topData (a i).2).2.1,1-guard i,Relation.ReflTransGen.refl⟩
  have pos (i : Fin k) : ∃ w ∈ W, SharedSwitch.value C (pairInput (e i false) (e i true)) w = true := by
    obtain ⟨len,hand,_⟩ := topData (a i).2
    exact ⟨output i,⟨i,rfl⟩,(andValOperands ao len hand _).mp (positive i) (1-guard i)⟩
  have quiet (mask : Fin k → Bool) (w : ℕ) (hw : w ∈ W) :
      SharedSwitch.value C (neg mask) w = false := by
    obtain ⟨i,rfl⟩ := hw
    obtain ⟨x,hx,on⟩ := hit mask i
    have active := sideVal hx on
    obtain ⟨len,hand,clean⟩ := topData (a i).2
    apply Bool.eq_false_iff.mpr
    intro wrong
    have accepted := clean _ ((andValOperands ao len hand _).mpr (fun p => by
      rcases opposite (guard i) p with rfl|rfl
      · exact active
      · exact wrong))
    exact Bool.false_ne_true ((noedge mask).symm.trans accepted)
  simpa using SharedSwitch.matched_pairs_le_dirty ao top e neg W under contains pos quiet

/-- Given a cover Z of the retained edges avoiding k disjoint residual pairs,
one of those pairs has no accepting top with an always available raw port
when fewer than k dirty gates are present. For each accepting top and side,
its raw literals outside Z are confined to one choice of endpoints of the k pairs. -/
theorem small_guards (ao : IsAO2 n C) (top : TopForm G C)
    (e : Fin k → Bool → Fin n)
    (distinct : Function.Injective (fun p : Fin k × Bool => e p.1 p.2))
    (Z : Finset (Fin n)) (free : ∀ i b, e i b ∉ Z)
    (cover : ∀ u v, G.Adj u v → u ∈ Z ∨ v ∈ Z ∨ ∃ i, s(u,v) = s(e i false,e i true))
    (few : (junk G C).card < k) :
    ∃ i, ∀ a : tops G C, gateVal n C a (pairInput (e i false) (e i true)) = true →
      ∀ guard : Fin 2, ∃ mask : Fin k → Bool,
        side (n := n) C a guard \ Z ⊆ Finset.univ.image (fun j => e j (mask j)) := by
  classical
  let absent (mask : Fin k → Bool) := Finset.univ.image (fun j => e j (!(mask j)))
  let neg (mask : Fin k → Bool) (v : Fin n) := decide (v ∉ Z ∧ v ∉ absent mask)
  have inAbsent (mask : Fin k → Bool) (i : Fin k) : e i (!(mask i)) ∈ absent mask :=
    Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have contains (mask : Fin k → Bool) (i : Fin k) : neg mask (e i (mask i)) = true := by
    apply decide_eq_true
    refine ⟨free _ _,?_⟩
    rintro he
    obtain ⟨j,_,same⟩ := Finset.mem_image.mp he
    have eq := @distinct (j,!(mask j)) (i,mask i) same
    have ij := congrArg Prod.fst eq
    change j = i at ij; subst j
    have bad := congrArg Prod.snd eq
    change (!(mask i)) = mask i at bad
    cases b : mask i <;> simp [b] at bad
  have noedge (mask : Fin k → Bool) : graphFun G ∅ (neg mask) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    simp [graphFun] at h
    obtain ⟨u,v,adj,hu,hv⟩ := h
    obtain ⟨zu,ou⟩ := of_decide_eq_true hu
    obtain ⟨zv,ov⟩ := of_decide_eq_true hv
    rcases cover u v adj with uz | vz | ⟨i,eq⟩
    · exact zu uz
    · exact zv vz
    · have m := inAbsent mask i
      rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> cases b : mask i
      all_goals simp only [b,Bool.not_false,Bool.not_true] at m
      all_goals first | exact ou m | exact ov m
  by_contra! good
  choose a fired port never using good
  have leaves (mask : Fin k → Bool) (i : Fin k) :
      ∃ w ∈ side (n := n) C (a i) (port i), neg mask w = true := by
    obtain ⟨w,m,no⟩ := Finset.not_subset.mp (never i (fun j => !(mask j)))
    obtain ⟨leaf,out⟩ := Finset.mem_sdiff.mp m
    exact ⟨w,leaf,decide_eq_true ⟨out,no⟩⟩
  have exceeds := count ao top e a port fired neg contains noedge leaves
  omega

#print axioms small_guards
end GuardedPairs
