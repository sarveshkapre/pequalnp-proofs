import SixEdgeAudit

namespace SixEdge.Formula

set_option maxHeartbeats 2000000

open SixEdge.CNFEncoding (threshold exact_count)

private def CounterRow (v : Values) (seen : List Bool) (row : List Lit) : Prop :=
  row.length = 8 ∧ ∀ i < 8, row[i]! ≠ 0 ∧ literalValue v row[i]! = threshold seen i

private theorem audit_counter_next (primary : Input → Bool) (v : Values) (seen : List Bool)
    (row : List Lit) (x : Lit) :
    Audited primary v (v 1 = true ∧ x ≠ 0 ∧ CounterRow v seen row) (counterNext row x)
      (CounterRow v (literalValue v x :: seen)) := by
  unfold counterNext
  let r (i : Nat) (t : Lit) := t ≠ 0 ∧ literalValue v t = threshold (literalValue v x :: seen) (i+1)
  let pre := v 1 = true ∧ x ≠ 0 ∧ CounterRow v seen row
  apply Audited.bind (Audited.mapM (r := r) (pre := pre) _ ?_)
  · intro tail
    apply Audited.pure
    rintro ⟨⟨hOne,_⟩, steps⟩
    have size : tail.length = 7 := by simpa using steps.length_eq.symm
    constructor
    · simp [size]
    · intro i hi
      cases i with
      | zero => simp [threshold, literalValue, hOne]
      | succ j =>
        have hj : j < 7 := by omega
        have rel := steps.get (i := j) (by simpa using hj) (by simpa [size] using hj)
        rw [List.getElem!_cons_succ, getElem!_pos tail j (by omega)]
        simpa [r] using rel
  · intro i
    apply Audited.bind ((audit_and primary v [x,row[i]!]).mono ?_ (fun _ _ h => h))
    · intro t
      apply (audit_or primary v [row[i+1]!,t]).mono
      · rintro ⟨⟨⟨hOne,_,_,rowOk⟩,idx⟩, nz,_⟩
        have hi : i < 7 := List.mem_range.mp idx
        refine ⟨hOne,?_⟩
        intro term mem
        rcases List.mem_cons.mp mem with rfl | tail
        · exact (rowOk (i+1) (by omega)).1
        · rwa [List.mem_singleton.mp tail]
      · rintro ⟨⟨⟨_,_,_,rowOk⟩,idx⟩, _, tValue⟩ out ⟨outNZ,outVal⟩
        have hi : i < 7 := List.mem_range.mp idx
        refine ⟨outNZ, ?_⟩
        simp only [List.any_cons,List.any_nil,Bool.or_false] at outVal
        simp only [List.all_cons,List.all_nil,Bool.and_true] at tValue
        rw [outVal, tValue, (rowOk i (by omega)).2, (rowOk (i+1) (by omega)).2]
        rfl
    · rintro ⟨⟨one,xNZ,_,rowOk⟩,idx⟩
      have hi : i < 7 := List.mem_range.mp idx
      refine ⟨one,?_⟩
      intro term mem
      rcases List.mem_cons.mp mem with rfl | tail
      · exact xNZ
      · rw [List.mem_singleton.mp tail]
        exact (rowOk i (by omega)).1

private theorem audit_counter_fold (primary : Input → Bool) (v : Values)
    (xs : List Lit) (row : List Lit) (seen : List Bool) :
    Audited primary v (v 1 = true ∧ (∀ t ∈ xs, t ≠ 0) ∧ CounterRow v seen row)
      (xs.foldlM counterNext row) (CounterRow v ((xs.map (literalValue v)).reverse ++ seen)) := by
  let inv (prefixFlags : List Lit) := CounterRow v (prefixFlags.map (literalValue v) ++ seen)
  have step (done : List Lit) (r : List Lit) (t : Lit) :
      Audited primary v (v 1 = true ∧ t ≠ 0 ∧ inv done r) (counterNext r t) (inv (t::done)) :=
    audit_counter_next primary v _ r t
  have audit := Audited.foldlM counterNext inv (· ≠ 0) (v 1 = true) step xs row []
  simpa only [inv, List.map_nil,List.nil_append,List.append_nil,List.map_reverse] using audit

private theorem initial_counter_row (v : Values) (one : v 1 = true) :
    CounterRow v [] [1,-1,-1,-1,-1,-1,-1,-1] := by
  have short : ∀ i : Fin 8, ([1,-1,-1,-1,-1,-1,-1,(-1 : Int)])[i.val]! = (if i.val = 0 then 1 else -1) := by
    decide +kernel
  refine ⟨rfl, fun i hi => ?_⟩
  rw [short ⟨i,hi⟩]
  cases i <;> simp [threshold, literalValue, one]

/-- The two emitted unit clauses hold exactly when the input flags have the
    required count. This proves the forward direction used by translation. -/
theorem audit_exact_six (primary : Input → Bool) (v : Values) (xs : List Lit) :
    Audited primary v
      (v 1 = true ∧ (∀ t ∈ xs, t ≠ 0) ∧ (xs.map (literalValue v)).count true = 6)
      (exactSix xs) (fun _ => True) := by
  unfold exactSix
  apply Audited.bind ((audit_counter_fold primary v xs _ []).mono ?_ (fun _ _ h => h))
  · intro row
    apply Audited.bind ((audit_require primary v .residualCount [row[6]!]).mono ?_ (fun _ _ h => h))
    · intro _
      apply (audit_require primary v .residualCount [-row[7]!]).mono ?_ (fun _ _ h => h)
      rintro ⟨⟨⟨_,_,count⟩, _,rowOK⟩,_⟩
      have countRev : (xs.map (literalValue v)).reverse.count true = 6 := by simpa using count
      have h := (exact_count _ 6).mpr countRev
      refine ⟨_, List.mem_cons_self, ?_⟩
      rw [literal_neg_of_ne _ (rowOK 7 (by decide)).1, (rowOK 7 (by decide)).2]
      simpa using h.2
    · rintro ⟨⟨_,_,count⟩, _,rowOK⟩
      have countRev : (xs.map (literalValue v)).reverse.count true = 6 := by simpa using count
      have h := (exact_count _ 6).mpr countRev
      refine ⟨_, List.mem_cons_self, ?_⟩
      rw [(rowOK 6 (by decide)).2]
      simpa using h.1
  · rintro ⟨one,nz,_⟩
    exact ⟨one,nz,initial_counter_row v one⟩

#print axioms audit_exact_six

end SixEdge.Formula
