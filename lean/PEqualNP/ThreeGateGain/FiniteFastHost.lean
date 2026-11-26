import PEqualNP.ThreeGateGain.FiniteQuick
import PEqualNP.ThreeGateGain.FiniteFastEligible
import PEqualNP.ThreeGateGain.FinitePop

namespace GainFinite

/-- Most frames are settled by the two available-type counts. Both neighbor
unions come from the verified incremental state. -/
def leafFrame (h : Host) (rl : Leaves) (rs : FastState) (cl : Leaves) (cs : FastState) : Bool :=
  let t := rl.length + cl.length
  let rem := fun mask => fastSize (activeMask h &&& ((2^27-1) ^^^ mask))
  (decide (t ≤ 10) && decide (17*t+3*(rem cs.neighbors + rem rs.neighbors) ≤ 158)) ||
    quickFrame h rl cl

def leafCols (h : Host) (rows : List (WordType × Nat)) (rl : Leaves) (rs : FastState) : Bool :=
  fastVisit (leafFrame h rl rs) [] ⟨0,[]⟩ (rows.filter (fun x => !(rs.neighbors.testBit x.1.val)))

def leafHost (h : Host) (rows : List (WordType × Nat)) : Bool :=
  fastVisit (leafCols h rows) [] ⟨0,[]⟩ rows

theorem leafFrame_correct (h : Host) (rl cl : Leaves) :
    leafFrame h rl (stateFor h rl) cl (stateFor h cl) = quickFrame h rl cl := by
  simp only [leafFrame, stateFor, fastSize_eq]
  change ((decide _ && decide (17*(rl.length+cl.length)+3*(remaining h cl+remaining h rl) ≤ 158))
    || quickFrame h rl cl) = quickFrame h rl cl
  by_cases a : rl.length+cl.length ≤ 10 <;>
    by_cases b : 17*(rl.length+cl.length)+3*(remaining h cl+remaining h rl) ≤ 158 <;>
    simp_all [quickFrame]


theorem leafCols_correct (h : Host) (rl : Leaves) :
    leafCols h (cached h allTypes) rl (stateFor h rl) = quickCols h rl := by
  unfold leafCols
  have cache : (cached h allTypes).filter (fun x => !((stateFor h rl).neighbors.testBit x.1.val)) =
      cached h (available h rl) := by simp [cached,available,stateFor,List.filter_map,Function.comp_def]
  rw [cache]
  change fastVisit (leafFrame h rl (stateFor h rl)) [] (stateFor h []) (cached h (available h rl)) = _
  rw [fastVisit_correct]
  · simp only [leafFrame_correct,quickCols]
  · exact (List.nodup_finRange _).filter _
  · simp

theorem leafHost_correct (h : Host) :
    leafHost h (cached h allTypes) = quickHost h := by
  change fastVisit (leafCols h (cached h allTypes)) [] (stateFor h []) (cached h allTypes) = _
  rw [fastVisit_correct]
  · simp only [leafCols_correct,quickHost]
  · exact List.nodup_finRange _
  · simp

def sparseRows (h : Host) := (cached h allTypes).filter (fun p => p.2 != 0)

theorem no_dead_rows (f : Leaves → FastState → Bool) (chosen : Leaves) (st : FastState)
    (todo : List (WordType × Nat)) :
    fastVisit f chosen st (todo.filter (fun p => p.2 != 0)) = fastVisit f chosen st todo := by
  induction todo generalizing chosen st with
  | nil => rfl
  | cons a tail ih =>
    obtain ⟨i,row⟩ := a
    by_cases zero : row = 0
    · subst row
      simpa [fastVisit,FastState.ok,nextState] using ih chosen st
    · simp [zero,fastVisit,ih]

theorem leafCols_sparse (h : Host) (rl : Leaves) (s : FastState) :
    leafCols h (sparseRows h) rl s = leafCols h (cached h allTypes) rl s := by
  unfold leafCols sparseRows
  rw [List.filter_comm]
  exact no_dead_rows _ _ _ _

theorem leafHost_sparse (h : Host) : leafHost h (sparseRows h) = quickHost h := by
  rw [← leafHost_correct]
  have eq : leafCols h (sparseRows h) = leafCols h (cached h allTypes) :=
    funext fun rl => funext fun st => leafCols_sparse h rl st
  unfold leafHost
  rw [eq]
  exact no_dead_rows _ _ _ _

#print axioms leafHost_sparse
#print axioms leafHost_correct
end GainFinite
