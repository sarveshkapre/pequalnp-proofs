import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-! Rank rigidity for normalized acyclic star circuits, in zero-cell coordinates.
Wires are indexed newest first. A port meets a raw rectangle with any selection
of earlier wires. Unused indices evaluate to the universe. -/
namespace SharingRank
open Set
open scoped Classical
abbrev Cell (m n : Nat) := Fin m × Fin n
abbrev Region (m n : Nat) := Set (Cell m n)
abbrev Box (m n : Nat) := Set (Fin m) × Set (Fin n)
abbrev Port (m n : Nat) := Box m n × Set Nat
abbrev Program (m n : Nat) := List (Port m n × Port m n)

def raw (q : Port m n) : Region m n := q.1.1 ×ˢ q.1.2
def run (w : Nat → Region m n) (q : Port m n) : Region m n :=
  raw q ∩ {x | ∀ i, i ∈ q.2 → x ∈ w i}

def wires : Program m n → Nat → Region m n
  | [] => fun _ => univ
  | (a,b)::p => fun i => Nat.casesOn i (run (wires p) a ∪ run (wires p) b) (wires p)

private theorem newest (p : Program m n) (a b : Port m n) :
    wires ((a,b)::p) 0 = run (wires p) a ∪ run (wires p) b := rfl

private theorem older (p : Program m n) (a b : Port m n) (i : Nat) :
    wires ((a,b)::p) (i+1) = wires p i := rfl

def flat : Program m n → Region m n
  | [] => univ
  | (a,b)::p => (raw a ∪ raw b) ∩ flat p

noncomputable def indicator (z : Region m n) : Matrix (Fin m) (Fin n) ℝ := by
  classical
  exact fun i j => if (i,j) ∈ z then 1 else 0

private theorem rectRank (q : Port m n) : (indicator (raw q)).rank ≤ 1 := by
  classical
  let v : Fin m → ℝ := fun i => if i ∈ q.1.1 then 1 else 0
  let w : Fin n → ℝ := fun j => if j ∈ q.1.2 then 1 else 0
  have h : indicator (raw q) = Matrix.vecMulVec v w := by
    ext i j
    by_cases hi : i ∈ q.1.1 <;> by_cases hj : j ∈ q.1.2 <;>
      simp [indicator,raw,Matrix.vecMulVec,v,w,hi,hj]
  rw [h]
  exact Matrix.rank_vecMulVec_le _ _

private theorem unionRank (a b : Region m n) : (indicator (a ∪ b)).rank ≤
    (indicator a).rank + (indicator b).rank + (indicator (a ∩ b)).rank := by
  classical
  let A := indicator a
  let B := indicator b
  let C := indicator (a ∩ b)
  have eq : indicator (a ∪ b) = A + B - C := by
    ext i j
    by_cases ha : (i,j) ∈ a <;> by_cases hb : (i,j) ∈ b <;>
      simp [A,B,C,indicator,ha,hb,Matrix.sub_apply,Matrix.add_apply]
  rw [eq]
  change Module.finrank ℝ (LinearMap.range (A+B-C).mulVecLin) ≤
    Module.finrank ℝ (LinearMap.range A.mulVecLin) +
    Module.finrank ℝ (LinearMap.range B.mulVecLin) +
    Module.finrank ℝ (LinearMap.range C.mulVecLin)
  have incl : LinearMap.range (A+B-C).mulVecLin ≤
      (LinearMap.range A.mulVecLin + LinearMap.range B.mulVecLin) + LinearMap.range C.mulVecLin := by
    rintro _ ⟨x,rfl⟩
    apply Submodule.mem_sup.mpr
    refine ⟨A.mulVec x + B.mulVec x, Submodule.mem_sup.mpr ⟨_,⟨x,rfl⟩,_,⟨x,rfl⟩,rfl⟩,
      C.mulVec (-x),⟨-x,rfl⟩,?_⟩
    simp [Matrix.mulVecLin_apply,Matrix.sub_mulVec,Matrix.add_mulVec,Matrix.mulVec_neg,sub_eq_add_neg]
  have h := Submodule.finrank_mono incl
  have i := Submodule.finrank_add_le_finrank_add_finrank
    (LinearMap.range A.mulVecLin + LinearMap.range B.mulVecLin) (LinearMap.range C.mulVecLin)
  have j := Submodule.finrank_add_le_finrank_add_finrank (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin)
  exact h.trans (i.trans (Nat.add_le_add_right j _))

def meetPort (a b : Port m n) : Port m n :=
  ((a.1.1 ∩ b.1.1, a.1.2 ∩ b.1.2), a.2 ∪ b.2)
def tailPort (q : Port m n) : Port m n := (q.1, Nat.succ ⁻¹' q.2)

private theorem raw_meet (a b : Port m n) : raw (meetPort a b) = raw a ∩ raw b := by
  ext x
  simp only [raw,meetPort,Set.mem_prod,Set.mem_inter_iff]
  tauto

private theorem run_meet (w : Nat → Region m n) (a b : Port m n) :
    run w (meetPort a b) = run w a ∩ run w b := by
  ext x
  simp only [run,raw_meet,Set.mem_inter_iff,Set.mem_ofPred_eq]
  change ((_ ∧ _) ∧ ∀ i, i ∈ a.2 ∪ b.2 → x ∈ w i) ↔ _
  simp only [Set.mem_union,or_imp,forall_and]
  tauto

private theorem allNat {P : Nat → Prop} : (∀ i, P i) ↔ P 0 ∧ ∀ i, P (i+1) :=
  ⟨fun h => ⟨h 0, fun i => h (i+1)⟩, fun h i => by cases i with | zero => exact h.1 | succ j => exact h.2 j⟩

private theorem eval_step (p : Program m n) (a b q : Port m n) :
    run (wires ((a,b)::p)) q = if 0 ∈ q.2 then
      run (wires p) (meetPort (tailPort q) a) ∪ run (wires p) (meetPort (tailPort q) b)
    else run (wires p) (tailPort q) := by
  classical
  by_cases h : 0 ∈ q.2
  · rw [if_pos h,run_meet,run_meet]
    ext x
    simp only [run,Set.mem_inter_iff,Set.mem_union,Set.mem_ofPred_eq]
    rw [allNat]
    simp only [newest,older,Set.mem_union,h,true_implies,
      tailPort,Set.mem_preimage,raw,run,Set.mem_inter_iff,Set.mem_ofPred_eq]
    tauto
  · rw [if_neg h]
    ext x
    simp only [run,Set.mem_inter_iff,Set.mem_ofPred_eq]
    rw [allNat]
    simp [newest,older,tailPort,raw,h]

/-- A non-flat output loses at least two units from the circuit rank ceiling. -/
theorem rigidity (p : Program m n) (q : Port m n) :
    (indicator (run (wires p) q)).rank ≤ 3 ^ p.length ∧
    (run (wires p) q ≠ raw q ∩ flat p →
      (indicator (run (wires p) q)).rank + 2 ≤ 3 ^ p.length) := by
  classical
  induction p generalizing q with
  | nil =>
    have eq : run (wires []) q = raw q := by ext; simp [run,wires]
    simp [eq,flat,rectRank]
  | cons ab p ih =>
    obtain ⟨a,b⟩ := ab
    let x := meetPort (tailPort q) a
    let y := meetPort (tailPort q) b
    let z := meetPort x y
    have X := ih x
    have Y := ih y
    have Z := (ih z).1
    have eqz : run (wires p) z = run (wires p) x ∩ run (wires p) y := run_meet _ _ _
    rw [eqz] at Z
    have sub := unionRank (run (wires p) x) (run (wires p) y)
    rw [eval_step]
    simp only [List.length_cons,pow_succ]
    split_ifs with uses
    · change (indicator (run (wires p) x ∪ run (wires p) y)).rank ≤ _ ∧
        (run (wires p) x ∪ run (wires p) y ≠ _ → (indicator (run (wires p) x ∪ run (wires p) y)).rank + 2 ≤ _)
      constructor
      · omega
      · intro ne
        by_cases hx : run (wires p) x = raw x ∩ flat p
        · have hy : run (wires p) y ≠ raw y ∩ flat p := by
            intro hy
            apply ne
            rw [hx,hy]
            simp only [x,y,raw_meet,flat]
            change (raw q ∩ raw a ∩ flat p) ∪ (raw q ∩ raw b ∩ flat p) = _
            ext t
            simp only [Set.mem_union,Set.mem_inter_iff]
            tauto
          have smaller := Y.2 hy
          omega
        · have smaller := X.2 hx
          omega
    · have bound := (ih (tailPort q)).1
      have pos : 0 < 3 ^ p.length := pow_pos (by decide) _
      constructor <;> intros <;> omega
end SharingRank
