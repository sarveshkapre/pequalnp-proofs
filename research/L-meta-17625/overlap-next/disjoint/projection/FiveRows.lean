import ProjectionGeometry
import ProjectedSchedule
import PathBits

namespace FiveRows
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open DisjointProjected

variable {n : ℕ}

/-- Columns a,b,c,d,e are the bits 0,1,2,3,4. -/
def row : Fin 10 → BitVec 5 := ![3,6,24,20,10,13,18,21,9,17]

def raw (v : Fin 5 → Fin n) (s : Finset (Fin n)) : R :=
  PathBits.pack fun i => decide (v i ∈ s)

def input (v : Fin 5 → Fin n) (r : Fin 10) (u : Fin n) : Bool :=
  decide (∃ i : Fin 5, v i = u ∧ (row r).getLsbD i = true)

def signal (v : Fin 5 → Fin n) (C : Circuit) (w : ℕ) : T :=
  PathBits.pack fun r => val C (List.ofFn (input v r)) w

def physical (v : Fin 5 → Fin n) (C : Circuit) (w : ℕ) : DisjointProjected.Wire :=
  ⟨signal v C w,raw v (orIn n C w),decide (orIn n C w).Nonempty⟩

theorem literal_table : ∀ (m : R) (r : Fin 10), (literal m).getLsbD r = true ↔
    ∃ i : Fin 5, m.getLsbD i = true ∧ (row r).getLsbD i = true := by decide

theorem literal_spec (v : Fin 5 → Fin n) (s : Finset (Fin n)) (r : Fin 10) :
    (literal (raw v s)).getLsbD r = true ↔ ∃ u ∈ s, input v r u = true := by
  rw [literal_table]; simp only [raw,PathBits.get_pack,decide_eq_true_eq,input]
  grind

@[simp] theorem signal_bit (v : Fin 5 → Fin n) (C : Circuit) (w : ℕ) (r : Fin 10) :
    (signal v C w).getLsbD r = val C (List.ofFn (input v r)) w := PathBits.get_pack .. 

@[simp] theorem at_vertex {v : Fin 5 → Fin n} (inj : Function.Injective v) (r : Fin 10) (i : Fin 5) :
    input v r (v i) = (row r).getLsbD i := by
  apply Bool.eq_iff_iff.mpr; simp [input,inj.eq_iff]

theorem raw_sub (v : Fin 5 → Fin n) {s t : Finset (Fin n)} (h : s ⊆ t) :
    raw v s &&& ~~~raw v t = 0 := by
  apply PathBits.bit_ext; intro j
  simp only [BitVec.getLsbD_and,BitVec.getLsbD_not,raw,PathBits.get_pack,j.isLt,decide_true,Bool.true_and]
  by_cases hs : v j ∈ s
  · simp [hs,h hs]
  · simp [hs]

theorem raw_union (v : Fin 5 → Fin n) (s t : Finset (Fin n)) :
    raw v (s ∪ t) = raw v s ||| raw v t := by
  apply PathBits.bit_ext; intro j; simp only [raw,BitVec.getLsbD_or,PathBits.get_pack]; simp

theorem raw_empty (v : Fin 5 → Fin n) : raw v ∅ = 0 := by
  apply PathBits.bit_ext; intro j; simp only [raw,PathBits.get_pack]; simp

theorem five_subsets : ∀ m : R, (m &&& ~~~9 = 0 ∨ m &&& ~~~12 = 0 ∨ m &&& ~~~18 = 0) →
    ∃ t : BitVec 4, rawMask t = m := by decide

theorem allowed_tag (v : Fin 5 → Fin n) (inj : Function.Injective v) (s : Finset (Fin n))
    (h : ProjectionGeometry.allowed (v 0) (v 1) (v 2) (v 3) (v 4) s) :
    ∃ t : BitVec 4, rawMask t = raw v s := by
  have all (i : Fin 5) : v i ∈ ({v 0,v 1,v 2,v 3,v 4} : Finset _) := by fin_cases i <;> simp
  have pair (x y : Fin 5) (m : R) (bits : ∀ i : Fin 5, m.getLsbD i = true ↔ i = x ∨ i = y)
      (sub : s ∩ {v 0,v 1,v 2,v 3,v 4} ⊆ {v x,v y}) : raw v s &&& ~~~m = 0 := by
    apply PathBits.bit_ext; intro i
    simp only [BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,Bool.true_and,raw,PathBits.get_pack]
    by_cases hx : v i ∈ s
    · have p := sub (Finset.mem_inter.mpr ⟨hx,all i⟩)
      simp only [Finset.mem_insert,Finset.mem_singleton,inj.eq_iff] at p
      simp [(bits i).mpr p]
    · simp [hx]
  apply five_subsets
  rcases h with h|h|h
  · exact Or.inl (pair 0 3 9 (by decide) h)
  · exact Or.inr (Or.inl (pair 2 3 12 (by decide) h))
  · exact Or.inr (Or.inr (pair 1 4 18 (by decide) h))

theorem raw_single (v : Fin 5 → Fin n) (u : Fin n) (inj : Function.Injective v) :
    ∃ tag : BitVec 4, rawMask tag = raw v {u} := by
  by_cases h : ∃ i, v i = u
  · obtain ⟨i,rfl⟩ := h
    have eq : raw v {v i} = PathBits.pack (fun j : Fin 5 => decide (j = i)) := by
      apply PathBits.bit_ext; intro j; simp [raw,inj.eq_iff]
    rw [eq]; fin_cases i <;> decide
  · have eq : raw v {u} = 0 := by
      apply PathBits.bit_ext; intro i; simp only [raw,PathBits.get_pack,Finset.mem_singleton]; simp [show v i ≠ u from fun e => h ⟨i,e⟩]
    exact ⟨0,eq.symm⟩

theorem raw_outside (v : Fin 5 → Fin n) (u : Fin n) (out : ∀ i, v i ≠ u) : raw v {u} = 0 := by
  apply PathBits.bit_ext; intro j; simp only [raw,PathBits.get_pack,Finset.mem_singleton]; simp [out]

theorem raw_middle_tip {v : Fin 5 → Fin n} (inj : Function.Injective v) : raw v {v 2} = 4 := by
  apply PathBits.bit_ext; intro j; simp only [raw,PathBits.get_pack,Finset.mem_singleton,inj.eq_iff]
  fin_cases j <;> decide

end FiveRows
