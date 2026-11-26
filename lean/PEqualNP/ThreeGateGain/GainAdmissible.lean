import PEqualNP.ThreeGateGain.GainFrameBridge
import PEqualNP.ThreeGateGain.GainForced

namespace GainFrameBridge
open Finset GainFinite GainSelection GainForced

theorem eligible_subsets (h : Host) (S : Finset WordType)
    (witness : ∀ i ∈ S, ∃ v, exclusive (fun i j => hostEdge h i j = true) S i v)
    (xs : Leaves) (sub : ∀ i ∈ xs, decide (i ∈ S) = true) : eligible h xs = true := by
  apply List.all_eq_true.mpr
  intro i hi
  obtain ⟨v,edge,unique⟩ := witness i (of_decide_eq_true (sub i hi))
  apply bne_iff_ne.mpr
  apply witness_nonzero _ v
  exact (private_bit h xs i v).mpr
    ⟨edge,fun k hk hkv => unique k (of_decide_eq_true (sub k hk)) hkv⟩

theorem physical_frame {P L : Type*} (h : Host) {r : P → WordType} {c : L → WordType}
    {A : Finset P} {B : Finset L}
    (s : Side (fun i j => hostEdge h i j = true) r c A B)
    (t : Side (fun j i => hostEdge h i j = true) c r B A) (checked : checkHost h = true) :
    testFrame h (fromSet t.leafTypes) (fromSet s.leafTypes) = true := by
  classical
  apply checkHost_sound _ _ _ _ _ _ checked
  · apply eligible_subsets
    intro i hi
    obtain ⟨v,rfl⟩ := t.leaf_mem_iff.mp hi
    exact ⟨_,real_partner t v⟩
  · apply eligible_subsets
    intro j hj
    obtain ⟨v,rfl⟩ := s.leaf_mem_iff.mp hj
    obtain ⟨he,un⟩ := real_partner s v
    refine ⟨r v.val,(edge_symm h _ _).trans he,?_⟩
    intro k hk e
    exact un k hk ((edge_symm h _ _).trans e)
  · intro j hj
    apply Bool.eq_false_iff.mpr
    intro edge
    obtain ⟨i,hi,he⟩ := (union_bit _ _ _).mp edge
    exact s.leaves_nonadjacent t ((fromSet_mem _ _).mp hi) (of_decide_eq_true hj) he

end GainFrameBridge
