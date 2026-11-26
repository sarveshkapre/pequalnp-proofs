import PEqualNP.SharingRank.Upper
import PEqualNP.SharingRank.Count

namespace SharingRank
open Set
open scoped Classical

private def port (b : Box m n) (s : Set Nat := ∅) : Port m n := (b,s)
private def unitBox (m n : Nat) : Box m n := (univ,univ)

/-- In each new gate the second input reuses the original shared gate. -/
private def make (a b : Box m n) : List (Box m n × Box m n) → Program m n
  | [] => [(port a,port b)]
  | (c,e)::l => (port c,port e {l.length}) :: make a b l

@[simp] private theorem make_length (a b : Box m n) (l : List (Box m n × Box m n)) :
    (make a b l).length = l.length+1 := by induction l with
  | nil => rfl
  | cons p l ih => obtain ⟨c,e⟩ := p; simp [make,ih]

private theorem make_eval (a b : Box m n) (l : List (Box m n × Box m n)) (v : Cell m n) :
    (v ∈ wires (make a b l) l.length ↔ v ∈ raw (port a) ∪ raw (port b)) ∧
    ((∀ j, j < l.length → v ∈ wires (make a b l) j) ↔
      ∀ p ∈ l, v ∈ raw (port p.1) ∨ (v ∈ raw (port p.2) ∧ v ∈ raw (port a) ∪ raw (port b))) := by
  induction l with
  | nil => simp [make,wires,run,raw,port]
  | cons p l ih =>
    obtain ⟨c,e⟩ := p
    constructor
    · exact ih.1
    · have split (w : Nat → Region m n) : (∀ j, j < l.length+1 → v ∈ w j) ↔
          v ∈ w 0 ∧ ∀ j, j < l.length → v ∈ w (j+1) := by
        constructor
        · exact fun h => ⟨h 0 (by omega), fun j hj => h (j+1) (by omega)⟩
        · rintro ⟨h,t⟩ (_|j) hj
          · exact h
          · exact t j (by omega)
      simp only [List.length_cons,split,List.forall_mem_cons]
      change (v ∈ run (wires (make a b l)) (port c) ∪ run (wires (make a b l)) (port e {l.length}) ∧
        (∀ j, j < l.length → v ∈ wires (make a b l) j)) ↔ _
      rw [ih.2]
      simp only [Set.mem_union,run,Set.mem_inter_iff,Set.mem_setOf_eq,port,Set.mem_empty_iff_false,
        false_implies,implies_true,and_true,Set.mem_singleton_iff,forall_eq,ih.1]
      rfl

namespace Family
open SharingRank
private def atDigit : (d : Nat) → Words d → Fin d → Four
  | 0, _, j => Fin.elim0 j
  | n+1, w, j => Fin.cases w.1 (fun i => atDigit n w.2 i) j

private theorem digit_test (f : Four → Four → Bool) (d : Nat) (x y : Words d) :
    allPairs f d x y = true ↔ ∀ j, f (atDigit d x j) (atDigit d y j) = true := by
  induction d with
  | zero => simp [allPairs]
  | succ n ih => rw [Fin.forall_fin_succ]; simp [allPairs,atDigit,ih]

abbrev Side (d : Nat) := Four × Words d
noncomputable def numbering (d : Nat) := Fintype.equivFin (Side d)
noncomputable def graphZero (d : Nat) : Region (Fintype.card (Side d)) (Fintype.card (Side d)) :=
  {p | cell d ((numbering d).symm p.1) ((numbering d).symm p.2) = true}

theorem graph_rank (d : Nat) : (indicator (graphZero d)).rank + 2 = 3^(d+1) := by
  have reindex : indicator (graphZero d) = (mat d).reindex (numbering d) (numbering d) := by
    ext i j
    by_cases h : cell d ((numbering d).symm i) ((numbering d).symm j) = true <;>
      simp [indicator,graphZero,mat,Matrix.reindex_apply,Matrix.submatrix,h]
  rw [reindex,Matrix.rank_reindex,exact_rank]

private theorem distribute {I : Type} (a b : I → Prop) (s : Prop) :
    (∀ j, a j ∨ b j ∧ s) ↔ (∀ j, a j) ∨ (s ∧ ∀ j, a j ∨ b j) := by
  by_cases h : s
  · simp only [h,and_true,true_and]
    constructor
    · exact Or.inr
    · rintro (all | either)
      · exact fun i => Or.inl (all i)
      · exact either
  · simp [h]

theorem circuit_upper (d : Nat) : ∃ (p : Program (Fintype.card (Side d)) (Fintype.card (Side d))) (q : Port (Fintype.card (Side d)) (Fintype.card (Side d))),
    p.length = d+1 ∧ run (wires p) q = graphZero d := by
  let bit (f : Side d → Four) (i : Nat) : Box (Fintype.card (Side d)) (Fintype.card (Side d)) :=
    let s := {v | (f ((numbering d).symm v)).val.testBit i = true}
    (s,s)
  let a := bit Prod.fst 0
  let b := bit Prod.fst 1
  let cd := fun (j : Fin d) => bit (fun v => atDigit d v.2 j) 0
  let ed := fun (j : Fin d) => bit (fun v => atDigit d v.2 j) 1
  let l := List.ofFn (fun j : Fin d => (cd j,ed j))
  refine ⟨make a b l,port (unitBox _ _) (Set.Iio l.length),by simp [l],?_⟩
  ext v
  obtain ⟨x,y⟩ := v
  have h := (make_eval a b l (x,y)).2
  simp only [run,port,raw,unitBox,Set.mem_prod,Set.mem_univ,true_and,Set.mem_setOf_eq,
    Set.mem_inter_iff,Set.mem_Iio,h]
  simp only [l,List.forall_mem_ofFn_iff]
  change _ ↔ cell d ((numbering d).symm x) ((numbering d).symm y) = true
  simp only [cell,Bool.or_eq_true,Bool.and_eq_true,digit_test]
  simp only [Set.mem_union,raw,port,a,b,cd,ed,bit,Set.mem_prod,Set.mem_ofPred_eq]
  simp only [← Bool.and_eq_true]
  simp only [someBit,Bool.or_eq_true,firstBit,otherBit]
  exact distribute _ _ _
end Family
end SharingRank
