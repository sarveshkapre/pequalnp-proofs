import PEqualNP.ThreeGateGain.FiniteFastHost

namespace GainFinite

theorem join_live {f : Leaves → FastState → Bool} {chosen : Leaves} {s : FastState}
    {i : WordType} {r : Nat} {tail : List (WordType × Nat)}
    (hs : fastVisit f chosen s tail = true)
    (ht : fastVisit f (i::chosen) (nextState r s) tail = true) :
    fastVisit f chosen s ((i,r)::tail) = true := by simp [fastVisit, hs, ht]

theorem join_dead {f : Leaves → FastState → Bool} {chosen : Leaves} {s : FastState}
    {i : WordType} {r : Nat} {tail : List (WordType × Nat)}
    (hs : fastVisit f chosen s tail = true) (no : (nextState r s).ok = false) :
    fastVisit f chosen s ((i,r)::tail) = true := by simp [fastVisit, hs, no]

/-- On the final row-side branch, replace the filtered column bank by its checked literal
before matching the child theorem. This avoids reducing the whole column subtree in conversion. -/
theorem enterColumns (h : Host) (bank : List (WordType × Nat)) (r : Leaves) (rs : FastState)
    (tail cols : List (WordType × Nat)) (stop : tail = [])
    (pool : cols = bank.filter (fun x => !rs.neighbors.testBit x.1.val))
    (child : fastVisit (leafFrame h r rs) [] ⟨0,[]⟩ cols = true) :
    fastVisit (leafCols h bank) r rs tail = true := by
  subst tail
  subst cols
  exact child

end GainFinite
