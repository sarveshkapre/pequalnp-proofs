/-
L-meta-8277. Which internal AND gates must fire in a passing 28-gate grid?

GridSideWitness.kinds_required applies to every candidate in the stated model.
GridSideWitness.posted_kinds binds the result to the original reduction.
GridPublishedRepair.clean and GridPublishedRepair.singleton_outputs check the
one-gate edit proposed by Amritpal-Nijjar in discussion 21642, comment 19907634.
Original grid28.txt, commit 57390b5251bba2f7382843c0d8d0fdb61f2f3e2c,
SHA-256 684c2730618452cd15968afe9e43fe0aba16a9b85dc108b42c6a6e3c924f6b1c.
Replay with Lean 4.36.0 on upstream commit e6bfe1a56efc768d244627b78f175b18de1acd6f.
-/
import PEqualNP.Defs
import Mathlib
import PEqualNP.Outside.L_meta_6973
import PEqualNP.Outside.L_meta_8029
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Logic.Relation
import Mathlib.Tactic
import PEqualNP.Outside.R_meta_4893_629

/-!
Control case and necessary condition for L-meta-8277 on the six-point grid.

GridResult.exact_clean_minimum proves a sharp 29-gate bound in the restricted
class. GridLowerBound.required_filter shows what a circuit of size at most 28
must do, assuming just the 24 positive tests and 14 specified negative tests.
GridResult.posted_witness_requires_filter specializes this to the grid hypothesis
read directly from the type of the merged reduction R_meta_4893_629.

The unrestricted existence question at 28 gates remains open here.
The input bank and task are from Amritpal-Nijjar's reduction in PR #10940.
Solareyon described a related two-bit condition for a different graph
in discussion #12644, comment 19897837.

Checked with upstream e6bfe1a56efc768d244627b78f175b18de1acd6f, Lean 4.36.0.
See the grid research note for replay instructions.
-/

/-!
A passing 29-gate grid and a 28-gate grid with one missed positive.
The negative result below covers arbitrary natural number masks and uses just the
disjointness premise from the posted grid conditions.
-/
namespace GridReplay
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

def rows : List ℕ := [29, 225, 1793, 294, 586, 1170]
def ports : List ℕ := [3, 40, 1064, 272, 336, 516, 644, 48, 560, 264, 392, 68, 1092]

def bank (p w : ℕ) : List Bool :=
  (List.range 6).map p.testBit ++ (List.range 11).map w.testBit ++
    ports.map (fun q => decide (w &&& q ≠ 0))

def disjoint (p w : ℕ) : Prop :=
  ∀ i : Fin 6, p.testBit i.val = true → w &&& rows.getD i.val 0 = 0

private lemma clear (p w : ℕ) (h : disjoint p w) (i : Fin 6) (j : ℕ)
    (hp : p.testBit i.val = true) (edge : (rows.getD i.val 0).testBit j = true) :
    w.testBit j = false := by
  have b := congrArg (fun n : ℕ => n.testBit j) (h i hp)
  simpa only [Nat.testBit_and, edge, Bool.and_true, Nat.zero_testBit] using b

private def pairOr (a b : Bool) := GateOp.or.eval [a,b]
private def pairAnd (a b : Bool) := GateOp.and.eval [a,b]
private lemma or_eq (a b : Bool) : pairOr a b = (a || b) := by cases a <;> cases b <;> rfl
private lemma and_eq (a b : Bool) : pairAnd a b = (a && b) := by cases a <;> cases b <;> rfl
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def Good (full : List Bool) : Nat → List Gate → Prop
  | _, [] => True
  | n, g :: gs =>
    g.op.eval (g.inputs.map fun i => if i < n then full.getD i false else false) =
      full.getD n false ∧ Good full (n+1) gs

private theorem replay (full : List Bool) (n : Nat) (gs : List Gate)
    (len : n + gs.length ≤ full.length) (ok : Good full n gs) :
    gs.foldl step (full.take n) = full.take (n + gs.length) := by
  induction gs generalizing n with
  | nil => simp
  | cons g gs ih =>
    have hn : n < full.length := by simp at len; omega
    have read (i : Nat) : (full.take n).getD i false =
        (if i < n then full.getD i false else false) := by
      by_cases hi : i < n <;> simp [List.getD_eq_getElem?_getD, hi]
    have h : step (full.take n) g = full.take (n+1) := by
      rw [List.take_succ_eq_append_getElem hn]
      unfold step
      simp only [read, ok.1, List.getD_eq_getElem _ _ hn]
    rw [List.foldl_cons, h, ih _ (by simp at len; omega) ok.2]
    congr 1; simp; omega


def control : Circuit := ⟨[
  ⟨.or, [6,8]⟩,
  ⟨.or, [30,9]⟩,
  ⟨.or, [31,10]⟩,
  ⟨.and, [0,32]⟩,
  ⟨.or, [6,11]⟩,
  ⟨.or, [34,12]⟩,
  ⟨.or, [35,13]⟩,
  ⟨.and, [1,36]⟩,
  ⟨.or, [6,14]⟩,
  ⟨.or, [38,15]⟩,
  ⟨.or, [39,16]⟩,
  ⟨.and, [2,40]⟩,
  ⟨.or, [7,8]⟩,
  ⟨.or, [42,11]⟩,
  ⟨.or, [43,14]⟩,
  ⟨.and, [3,44]⟩,
  ⟨.or, [7,9]⟩,
  ⟨.or, [46,12]⟩,
  ⟨.or, [47,15]⟩,
  ⟨.and, [4,48]⟩,
  ⟨.or, [7,10]⟩,
  ⟨.or, [50,13]⟩,
  ⟨.or, [51,16]⟩,
  ⟨.and, [5,52]⟩,
  ⟨.or, [33,37]⟩,
  ⟨.or, [54,41]⟩,
  ⟨.or, [55,45]⟩,
  ⟨.or, [56,49]⟩,
  ⟨.or, [57,53]⟩
  ], 58⟩

theorem control_shape : IsAO2 30 control ∧ control.size = 29 ∧ control.output = 58 := by decide +kernel

private def controlFormula (p w : ℕ) : Bool := (pairOr (pairOr (pairOr (pairOr (pairOr (pairAnd (p.testBit 0) (pairOr (pairOr (pairOr (w.testBit 0) (w.testBit 2)) (w.testBit 3)) (w.testBit 4))) (pairAnd (p.testBit 1) (pairOr (pairOr (pairOr (w.testBit 0) (w.testBit 5)) (w.testBit 6)) (w.testBit 7)))) (pairAnd (p.testBit 2) (pairOr (pairOr (pairOr (w.testBit 0) (w.testBit 8)) (w.testBit 9)) (w.testBit 10)))) (pairAnd (p.testBit 3) (pairOr (pairOr (pairOr (w.testBit 1) (w.testBit 2)) (w.testBit 5)) (w.testBit 8)))) (pairAnd (p.testBit 4) (pairOr (pairOr (pairOr (w.testBit 1) (w.testBit 3)) (w.testBit 6)) (w.testBit 9)))) (pairAnd (p.testBit 5) (pairOr (pairOr (pairOr (w.testBit 1) (w.testBit 4)) (w.testBit 7)) (w.testBit 10))))

private theorem control_eval (p w : ℕ) : control.eval (bank p w) = controlFormula p w := by
  let inputs : List Bool := [p.testBit 0, p.testBit 1, p.testBit 2, p.testBit 3, p.testBit 4, p.testBit 5, w.testBit 0, w.testBit 1, w.testBit 2, w.testBit 3, w.testBit 4, w.testBit 5, w.testBit 6, w.testBit 7, w.testBit 8, w.testBit 9, w.testBit 10, decide (w &&& 3 ≠ 0), decide (w &&& 40 ≠ 0), decide (w &&& 1064 ≠ 0), decide (w &&& 272 ≠ 0), decide (w &&& 336 ≠ 0), decide (w &&& 516 ≠ 0), decide (w &&& 644 ≠ 0), decide (w &&& 48 ≠ 0), decide (w &&& 560 ≠ 0), decide (w &&& 264 ≠ 0), decide (w &&& 392 ≠ 0), decide (w &&& 68 ≠ 0), decide (w &&& 1092 ≠ 0)]
  have input_eq : bank p w = inputs := rfl
  let v30 := GateOp.or.eval [(w.testBit 0), (w.testBit 2)]
  let v31 := GateOp.or.eval [v30, (w.testBit 3)]
  let v32 := GateOp.or.eval [v31, (w.testBit 4)]
  let v33 := GateOp.and.eval [(p.testBit 0), v32]
  let v34 := GateOp.or.eval [(w.testBit 0), (w.testBit 5)]
  let v35 := GateOp.or.eval [v34, (w.testBit 6)]
  let v36 := GateOp.or.eval [v35, (w.testBit 7)]
  let v37 := GateOp.and.eval [(p.testBit 1), v36]
  let v38 := GateOp.or.eval [(w.testBit 0), (w.testBit 8)]
  let v39 := GateOp.or.eval [v38, (w.testBit 9)]
  let v40 := GateOp.or.eval [v39, (w.testBit 10)]
  let v41 := GateOp.and.eval [(p.testBit 2), v40]
  let v42 := GateOp.or.eval [(w.testBit 1), (w.testBit 2)]
  let v43 := GateOp.or.eval [v42, (w.testBit 5)]
  let v44 := GateOp.or.eval [v43, (w.testBit 8)]
  let v45 := GateOp.and.eval [(p.testBit 3), v44]
  let v46 := GateOp.or.eval [(w.testBit 1), (w.testBit 3)]
  let v47 := GateOp.or.eval [v46, (w.testBit 6)]
  let v48 := GateOp.or.eval [v47, (w.testBit 9)]
  let v49 := GateOp.and.eval [(p.testBit 4), v48]
  let v50 := GateOp.or.eval [(w.testBit 1), (w.testBit 4)]
  let v51 := GateOp.or.eval [v50, (w.testBit 7)]
  let v52 := GateOp.or.eval [v51, (w.testBit 10)]
  let v53 := GateOp.and.eval [(p.testBit 5), v52]
  let v54 := GateOp.or.eval [v33, v37]
  let v55 := GateOp.or.eval [v54, v41]
  let v56 := GateOp.or.eval [v55, v45]
  let v57 := GateOp.or.eval [v56, v49]
  let v58 := GateOp.or.eval [v57, v53]
  let values : List Bool := [v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58]
  let full := inputs ++ values
  have h : Good full 30 control.gates := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
  have hw : control.wires (bank p w) = full := by
    rw [input_eq]; exact replay full 30 control.gates (Nat.le_refl 59) h
  unfold Circuit.eval
  rw [hw]
  rfl

theorem control_positive : ∀ i : Fin 6, ∀ j : Fin 11,
    control.eval (bank (2^i.val) (2^j.val)) = ((rows.getD i.val 0).testBit j.val) := by
  simp only [control_eval]
  decide +kernel

theorem control_negative (p w : ℕ) (h : disjoint p w) :
    control.eval (bank p w) = false := by
  rw [control_eval]
  change (pairOr (pairOr (pairOr (pairOr (pairOr (pairAnd (p.testBit 0) (pairOr (pairOr (pairOr (w.testBit 0) (w.testBit 2)) (w.testBit 3)) (w.testBit 4))) (pairAnd (p.testBit 1) (pairOr (pairOr (pairOr (w.testBit 0) (w.testBit 5)) (w.testBit 6)) (w.testBit 7)))) (pairAnd (p.testBit 2) (pairOr (pairOr (pairOr (w.testBit 0) (w.testBit 8)) (w.testBit 9)) (w.testBit 10)))) (pairAnd (p.testBit 3) (pairOr (pairOr (pairOr (w.testBit 1) (w.testBit 2)) (w.testBit 5)) (w.testBit 8)))) (pairAnd (p.testBit 4) (pairOr (pairOr (pairOr (w.testBit 1) (w.testBit 3)) (w.testBit 6)) (w.testBit 9)))) (pairAnd (p.testBit 5) (pairOr (pairOr (pairOr (w.testBit 1) (w.testBit 4)) (w.testBit 7)) (w.testBit 10)))) = false
  have r0 : (pairAnd (p.testBit 0) (pairOr (pairOr (pairOr (w.testBit 0) (w.testBit 2)) (w.testBit 3)) (w.testBit 4))) = false := by
    cases hp : p.testBit 0 with
    | false => simp [and_eq]
    | true =>
      have c0 : w.testBit 0 = false := clear p w h ⟨0,by decide⟩ 0 hp (by decide)
      have c2 : w.testBit 2 = false := clear p w h ⟨0,by decide⟩ 2 hp (by decide)
      have c3 : w.testBit 3 = false := clear p w h ⟨0,by decide⟩ 3 hp (by decide)
      have c4 : w.testBit 4 = false := clear p w h ⟨0,by decide⟩ 4 hp (by decide)
      simp [and_eq, or_eq, c0, c2, c3, c4]
  have r1 : (pairAnd (p.testBit 1) (pairOr (pairOr (pairOr (w.testBit 0) (w.testBit 5)) (w.testBit 6)) (w.testBit 7))) = false := by
    cases hp : p.testBit 1 with
    | false => simp [and_eq]
    | true =>
      have c0 : w.testBit 0 = false := clear p w h ⟨1,by decide⟩ 0 hp (by decide)
      have c5 : w.testBit 5 = false := clear p w h ⟨1,by decide⟩ 5 hp (by decide)
      have c6 : w.testBit 6 = false := clear p w h ⟨1,by decide⟩ 6 hp (by decide)
      have c7 : w.testBit 7 = false := clear p w h ⟨1,by decide⟩ 7 hp (by decide)
      simp [and_eq, or_eq, c0, c5, c6, c7]
  have r2 : (pairAnd (p.testBit 2) (pairOr (pairOr (pairOr (w.testBit 0) (w.testBit 8)) (w.testBit 9)) (w.testBit 10))) = false := by
    cases hp : p.testBit 2 with
    | false => simp [and_eq]
    | true =>
      have c0 : w.testBit 0 = false := clear p w h ⟨2,by decide⟩ 0 hp (by decide)
      have c8 : w.testBit 8 = false := clear p w h ⟨2,by decide⟩ 8 hp (by decide)
      have c9 : w.testBit 9 = false := clear p w h ⟨2,by decide⟩ 9 hp (by decide)
      have c10 : w.testBit 10 = false := clear p w h ⟨2,by decide⟩ 10 hp (by decide)
      simp [and_eq, or_eq, c0, c8, c9, c10]
  have r3 : (pairAnd (p.testBit 3) (pairOr (pairOr (pairOr (w.testBit 1) (w.testBit 2)) (w.testBit 5)) (w.testBit 8))) = false := by
    cases hp : p.testBit 3 with
    | false => simp [and_eq]
    | true =>
      have c1 : w.testBit 1 = false := clear p w h ⟨3,by decide⟩ 1 hp (by decide)
      have c2 : w.testBit 2 = false := clear p w h ⟨3,by decide⟩ 2 hp (by decide)
      have c5 : w.testBit 5 = false := clear p w h ⟨3,by decide⟩ 5 hp (by decide)
      have c8 : w.testBit 8 = false := clear p w h ⟨3,by decide⟩ 8 hp (by decide)
      simp [and_eq, or_eq, c1, c2, c5, c8]
  have r4 : (pairAnd (p.testBit 4) (pairOr (pairOr (pairOr (w.testBit 1) (w.testBit 3)) (w.testBit 6)) (w.testBit 9))) = false := by
    cases hp : p.testBit 4 with
    | false => simp [and_eq]
    | true =>
      have c1 : w.testBit 1 = false := clear p w h ⟨4,by decide⟩ 1 hp (by decide)
      have c3 : w.testBit 3 = false := clear p w h ⟨4,by decide⟩ 3 hp (by decide)
      have c6 : w.testBit 6 = false := clear p w h ⟨4,by decide⟩ 6 hp (by decide)
      have c9 : w.testBit 9 = false := clear p w h ⟨4,by decide⟩ 9 hp (by decide)
      simp [and_eq, or_eq, c1, c3, c6, c9]
  have r5 : (pairAnd (p.testBit 5) (pairOr (pairOr (pairOr (w.testBit 1) (w.testBit 4)) (w.testBit 7)) (w.testBit 10))) = false := by
    cases hp : p.testBit 5 with
    | false => simp [and_eq]
    | true =>
      have c1 : w.testBit 1 = false := clear p w h ⟨5,by decide⟩ 1 hp (by decide)
      have c4 : w.testBit 4 = false := clear p w h ⟨5,by decide⟩ 4 hp (by decide)
      have c7 : w.testBit 7 = false := clear p w h ⟨5,by decide⟩ 7 hp (by decide)
      have c10 : w.testBit 10 = false := clear p w h ⟨5,by decide⟩ 10 hp (by decide)
      simp [and_eq, or_eq, c1, c4, c7, c10]
  rw [r0, r1, r2, r3, r4, r5]; rfl

def nearMiss : Circuit := ⟨[
  ⟨.or, [8,9]⟩,
  ⟨.or, [30,10]⟩,
  ⟨.and, [0,31]⟩,
  ⟨.or, [6,11]⟩,
  ⟨.or, [33,12]⟩,
  ⟨.or, [34,13]⟩,
  ⟨.and, [1,35]⟩,
  ⟨.or, [6,14]⟩,
  ⟨.or, [37,15]⟩,
  ⟨.or, [38,16]⟩,
  ⟨.and, [2,39]⟩,
  ⟨.or, [7,8]⟩,
  ⟨.or, [41,11]⟩,
  ⟨.or, [42,14]⟩,
  ⟨.and, [3,43]⟩,
  ⟨.or, [7,9]⟩,
  ⟨.or, [45,12]⟩,
  ⟨.or, [46,15]⟩,
  ⟨.and, [4,47]⟩,
  ⟨.or, [7,10]⟩,
  ⟨.or, [49,13]⟩,
  ⟨.or, [50,16]⟩,
  ⟨.and, [5,51]⟩,
  ⟨.or, [32,36]⟩,
  ⟨.or, [53,40]⟩,
  ⟨.or, [54,44]⟩,
  ⟨.or, [55,48]⟩,
  ⟨.or, [56,52]⟩
  ], 57⟩

theorem nearMiss_shape : IsAO2 30 nearMiss ∧ nearMiss.size = 28 ∧ nearMiss.output = 57 := by decide +kernel

private def nearMissFormula (p w : ℕ) : Bool := (pairOr (pairOr (pairOr (pairOr (pairOr (pairAnd (p.testBit 0) (pairOr (pairOr (w.testBit 2) (w.testBit 3)) (w.testBit 4))) (pairAnd (p.testBit 1) (pairOr (pairOr (pairOr (w.testBit 0) (w.testBit 5)) (w.testBit 6)) (w.testBit 7)))) (pairAnd (p.testBit 2) (pairOr (pairOr (pairOr (w.testBit 0) (w.testBit 8)) (w.testBit 9)) (w.testBit 10)))) (pairAnd (p.testBit 3) (pairOr (pairOr (pairOr (w.testBit 1) (w.testBit 2)) (w.testBit 5)) (w.testBit 8)))) (pairAnd (p.testBit 4) (pairOr (pairOr (pairOr (w.testBit 1) (w.testBit 3)) (w.testBit 6)) (w.testBit 9)))) (pairAnd (p.testBit 5) (pairOr (pairOr (pairOr (w.testBit 1) (w.testBit 4)) (w.testBit 7)) (w.testBit 10))))

private theorem nearMiss_eval (p w : ℕ) : nearMiss.eval (bank p w) = nearMissFormula p w := by
  let inputs : List Bool := [p.testBit 0, p.testBit 1, p.testBit 2, p.testBit 3, p.testBit 4, p.testBit 5, w.testBit 0, w.testBit 1, w.testBit 2, w.testBit 3, w.testBit 4, w.testBit 5, w.testBit 6, w.testBit 7, w.testBit 8, w.testBit 9, w.testBit 10, decide (w &&& 3 ≠ 0), decide (w &&& 40 ≠ 0), decide (w &&& 1064 ≠ 0), decide (w &&& 272 ≠ 0), decide (w &&& 336 ≠ 0), decide (w &&& 516 ≠ 0), decide (w &&& 644 ≠ 0), decide (w &&& 48 ≠ 0), decide (w &&& 560 ≠ 0), decide (w &&& 264 ≠ 0), decide (w &&& 392 ≠ 0), decide (w &&& 68 ≠ 0), decide (w &&& 1092 ≠ 0)]
  have input_eq : bank p w = inputs := rfl
  let v30 := GateOp.or.eval [(w.testBit 2), (w.testBit 3)]
  let v31 := GateOp.or.eval [v30, (w.testBit 4)]
  let v32 := GateOp.and.eval [(p.testBit 0), v31]
  let v33 := GateOp.or.eval [(w.testBit 0), (w.testBit 5)]
  let v34 := GateOp.or.eval [v33, (w.testBit 6)]
  let v35 := GateOp.or.eval [v34, (w.testBit 7)]
  let v36 := GateOp.and.eval [(p.testBit 1), v35]
  let v37 := GateOp.or.eval [(w.testBit 0), (w.testBit 8)]
  let v38 := GateOp.or.eval [v37, (w.testBit 9)]
  let v39 := GateOp.or.eval [v38, (w.testBit 10)]
  let v40 := GateOp.and.eval [(p.testBit 2), v39]
  let v41 := GateOp.or.eval [(w.testBit 1), (w.testBit 2)]
  let v42 := GateOp.or.eval [v41, (w.testBit 5)]
  let v43 := GateOp.or.eval [v42, (w.testBit 8)]
  let v44 := GateOp.and.eval [(p.testBit 3), v43]
  let v45 := GateOp.or.eval [(w.testBit 1), (w.testBit 3)]
  let v46 := GateOp.or.eval [v45, (w.testBit 6)]
  let v47 := GateOp.or.eval [v46, (w.testBit 9)]
  let v48 := GateOp.and.eval [(p.testBit 4), v47]
  let v49 := GateOp.or.eval [(w.testBit 1), (w.testBit 4)]
  let v50 := GateOp.or.eval [v49, (w.testBit 7)]
  let v51 := GateOp.or.eval [v50, (w.testBit 10)]
  let v52 := GateOp.and.eval [(p.testBit 5), v51]
  let v53 := GateOp.or.eval [v32, v36]
  let v54 := GateOp.or.eval [v53, v40]
  let v55 := GateOp.or.eval [v54, v44]
  let v56 := GateOp.or.eval [v55, v48]
  let v57 := GateOp.or.eval [v56, v52]
  let values : List Bool := [v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57]
  let full := inputs ++ values
  have h : Good full 30 nearMiss.gates := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
  have hw : nearMiss.wires (bank p w) = full := by
    rw [input_eq]; exact replay full 30 nearMiss.gates (Nat.le_refl 58) h
  unfold Circuit.eval
  rw [hw]
  rfl

theorem nearMiss_positive : ∀ i : Fin 6, ∀ j : Fin 11,
    nearMiss.eval (bank (2^i.val) (2^j.val)) = ((rows.getD i.val 0).testBit j.val && !(i.val == 0 && j.val == 0)) := by
  simp only [nearMiss_eval]
  decide +kernel

theorem nearMiss_negative (p w : ℕ) (h : disjoint p w) :
    nearMiss.eval (bank p w) = false := by
  rw [nearMiss_eval]
  change (pairOr (pairOr (pairOr (pairOr (pairOr (pairAnd (p.testBit 0) (pairOr (pairOr (w.testBit 2) (w.testBit 3)) (w.testBit 4))) (pairAnd (p.testBit 1) (pairOr (pairOr (pairOr (w.testBit 0) (w.testBit 5)) (w.testBit 6)) (w.testBit 7)))) (pairAnd (p.testBit 2) (pairOr (pairOr (pairOr (w.testBit 0) (w.testBit 8)) (w.testBit 9)) (w.testBit 10)))) (pairAnd (p.testBit 3) (pairOr (pairOr (pairOr (w.testBit 1) (w.testBit 2)) (w.testBit 5)) (w.testBit 8)))) (pairAnd (p.testBit 4) (pairOr (pairOr (pairOr (w.testBit 1) (w.testBit 3)) (w.testBit 6)) (w.testBit 9)))) (pairAnd (p.testBit 5) (pairOr (pairOr (pairOr (w.testBit 1) (w.testBit 4)) (w.testBit 7)) (w.testBit 10)))) = false
  have r0 : (pairAnd (p.testBit 0) (pairOr (pairOr (w.testBit 2) (w.testBit 3)) (w.testBit 4))) = false := by
    cases hp : p.testBit 0 with
    | false => simp [and_eq]
    | true =>
      have c2 : w.testBit 2 = false := clear p w h ⟨0,by decide⟩ 2 hp (by decide)
      have c3 : w.testBit 3 = false := clear p w h ⟨0,by decide⟩ 3 hp (by decide)
      have c4 : w.testBit 4 = false := clear p w h ⟨0,by decide⟩ 4 hp (by decide)
      simp [and_eq, or_eq, c2, c3, c4]
  have r1 : (pairAnd (p.testBit 1) (pairOr (pairOr (pairOr (w.testBit 0) (w.testBit 5)) (w.testBit 6)) (w.testBit 7))) = false := by
    cases hp : p.testBit 1 with
    | false => simp [and_eq]
    | true =>
      have c0 : w.testBit 0 = false := clear p w h ⟨1,by decide⟩ 0 hp (by decide)
      have c5 : w.testBit 5 = false := clear p w h ⟨1,by decide⟩ 5 hp (by decide)
      have c6 : w.testBit 6 = false := clear p w h ⟨1,by decide⟩ 6 hp (by decide)
      have c7 : w.testBit 7 = false := clear p w h ⟨1,by decide⟩ 7 hp (by decide)
      simp [and_eq, or_eq, c0, c5, c6, c7]
  have r2 : (pairAnd (p.testBit 2) (pairOr (pairOr (pairOr (w.testBit 0) (w.testBit 8)) (w.testBit 9)) (w.testBit 10))) = false := by
    cases hp : p.testBit 2 with
    | false => simp [and_eq]
    | true =>
      have c0 : w.testBit 0 = false := clear p w h ⟨2,by decide⟩ 0 hp (by decide)
      have c8 : w.testBit 8 = false := clear p w h ⟨2,by decide⟩ 8 hp (by decide)
      have c9 : w.testBit 9 = false := clear p w h ⟨2,by decide⟩ 9 hp (by decide)
      have c10 : w.testBit 10 = false := clear p w h ⟨2,by decide⟩ 10 hp (by decide)
      simp [and_eq, or_eq, c0, c8, c9, c10]
  have r3 : (pairAnd (p.testBit 3) (pairOr (pairOr (pairOr (w.testBit 1) (w.testBit 2)) (w.testBit 5)) (w.testBit 8))) = false := by
    cases hp : p.testBit 3 with
    | false => simp [and_eq]
    | true =>
      have c1 : w.testBit 1 = false := clear p w h ⟨3,by decide⟩ 1 hp (by decide)
      have c2 : w.testBit 2 = false := clear p w h ⟨3,by decide⟩ 2 hp (by decide)
      have c5 : w.testBit 5 = false := clear p w h ⟨3,by decide⟩ 5 hp (by decide)
      have c8 : w.testBit 8 = false := clear p w h ⟨3,by decide⟩ 8 hp (by decide)
      simp [and_eq, or_eq, c1, c2, c5, c8]
  have r4 : (pairAnd (p.testBit 4) (pairOr (pairOr (pairOr (w.testBit 1) (w.testBit 3)) (w.testBit 6)) (w.testBit 9))) = false := by
    cases hp : p.testBit 4 with
    | false => simp [and_eq]
    | true =>
      have c1 : w.testBit 1 = false := clear p w h ⟨4,by decide⟩ 1 hp (by decide)
      have c3 : w.testBit 3 = false := clear p w h ⟨4,by decide⟩ 3 hp (by decide)
      have c6 : w.testBit 6 = false := clear p w h ⟨4,by decide⟩ 6 hp (by decide)
      have c9 : w.testBit 9 = false := clear p w h ⟨4,by decide⟩ 9 hp (by decide)
      simp [and_eq, or_eq, c1, c3, c6, c9]
  have r5 : (pairAnd (p.testBit 5) (pairOr (pairOr (pairOr (w.testBit 1) (w.testBit 4)) (w.testBit 7)) (w.testBit 10))) = false := by
    cases hp : p.testBit 5 with
    | false => simp [and_eq]
    | true =>
      have c1 : w.testBit 1 = false := clear p w h ⟨5,by decide⟩ 1 hp (by decide)
      have c4 : w.testBit 4 = false := clear p w h ⟨5,by decide⟩ 4 hp (by decide)
      have c7 : w.testBit 7 = false := clear p w h ⟨5,by decide⟩ 7 hp (by decide)
      have c10 : w.testBit 10 = false := clear p w h ⟨5,by decide⟩ 10 hp (by decide)
      simp [and_eq, or_eq, c1, c4, c7, c10]
  rw [r0, r1, r2, r3, r4, r5]; rfl

end GridReplay

/-!
Fourteen negative inputs for the 28-gate grid in L-meta-8277.
They cover all allowed negative inputs with two distinct physical bits set.
-/
namespace GridPairCover

def rows : List ℕ := [29,225,1793,294,586,1170]
def ports : List ℕ := [3,40,1064,272,336,516,644,48,560,264,392,68,1092]

def tests : List (ℕ × ℕ) :=
  [(0,1091),(2,534),(2,1290),(5,162),(9,1728),(12,216),(16,389),
   (16,1073),(18,1300),(30,16),(33,864),(36,108),(40,521),(51,256)]

def negative (p w : ℕ) : Prop :=
  p &&& 7 ≠ 7 ∧ p &&& 56 ≠ 56 ∧
  (∀ q ∈ rows ++ ports, ((List.range 11).filter (w &&& q).testBit).length ≤ 2) ∧
  (∀ i : Fin 6, p.testBit i.val = true → w &&& rows.getD i.val 0 = 0)

instance (p w : ℕ) : Decidable (negative p w) := by unfold negative; infer_instance

def point (i : Fin 17) : ℕ := if i.val < 6 then 2 ^ i.val else 0
def line (i : Fin 17) : ℕ := if i.val < 6 then 0 else 2 ^ (i.val - 6)
def points (i j : Fin 17) := point i ||| point j
def lines (i j : Fin 17) := line i ||| line j
def subset (a b : ℕ) : Prop := a &&& b = a
instance (a b : ℕ) : Decidable (subset a b) := by unfold subset; infer_instance
def isNonedge (i j : Fin 17) : Bool :=
  !(i.val < 6 && 6 ≤ j.val && (rows.getD i.val 0).testBit (j.val-6))

theorem admissible : tests.length = 14 ∧ ∀ t ∈ tests, negative t.1 t.2 := by decide +kernel

theorem covers : ∀ i j : Fin 17, i < j → isNonedge i j = true →
    ∃ t ∈ tests, subset (points i j) t.1 ∧ subset (lines i j) t.2 := by decide +kernel

/-- For any monotone signal, being true on a nonincident pair implies it is true
on one of the 14 allowed negative tests. -/
theorem detects (f : ℕ → ℕ → Bool)
    (mono : ∀ p w p' w', subset p p' → subset w w' → f p w = true → f p' w' = true)
    (i j : Fin 17) (order : i < j) (nonedge : isNonedge i j = true)
    (fires : f (points i j) (lines i j) = true) :
    ∃ t ∈ tests, negative t.1 t.2 ∧ f t.1 t.2 = true := by
  obtain ⟨t, ht, hp, hw⟩ := covers i j order nonedge
  exact ⟨t, ht, admissible.2 t ht, mono _ _ _ _ hp hw fires⟩

end GridPairCover

/-! The physical graph and the supplied inputs of the six-point grid in L-meta-8277. -/
namespace GridGeometry

abbrev Vertex := Fin 17

def rows : List Nat := [29, 225, 1793, 294, 586, 1170]
def ports : List Nat := [3, 40, 1064, 272, 336, 516, 644, 48, 560, 264, 392, 68, 1092]

/-- Vertices 0–5 are points. Vertices 6–16 are lines. -/
def directed (p l : Vertex) : Bool :=
  p.val < 6 && 6 ≤ l.val && (rows.getD p.val 0).testBit (l.val - 6)

def Adj (u v : Vertex) : Bool := directed u v || directed v u

def neighbors (v : Vertex) : Finset Vertex := Finset.univ.filter (fun w => Adj v w)

def bankSupport (wire : Fin 30) : Finset Vertex :=
  Finset.univ.filter fun v =>
    if wire.val < 17 then wire.val = v.val
    else 6 ≤ v.val ∧ (ports.getD (wire.val-17) 0).testBit (v.val-6) = true

theorem mem_neighbors (c x : Vertex) : x ∈ neighbors c ↔ Adj c x = true := by
  simp [neighbors]

theorem adj_comm (v w : Vertex) : Adj v w = Adj w v := Bool.or_comm ..

theorem degree_le_four : ∀ v : Vertex, (neighbors v).card ≤ 4 := by decide +kernel

theorem common_neighbors : ∀ v w : Vertex, v ≠ w →
    ((neighbors v) ∩ (neighbors w)).card ≤ 1 := by decide +kernel

theorem bank_meets_star : ∀ (i : Fin 30) (v : Vertex),
    ((bankSupport i) ∩ (neighbors v)).card ≤ 1 := by decide +kernel

def edges : Finset (Vertex × Vertex) := Finset.univ.filter fun e => directed e.1 e.2

theorem edge_count : edges.card = 24 := by decide +kernel

/-- Any nonempty complete bipartite subgraph is a star with at most four leaves. -/
theorem rectangle_star {A B : Finset Vertex} (ha : A.Nonempty) (hb : B.Nonempty)
    (complete : ∀ a ∈ A, ∀ b ∈ B, Adj a b = true) :
    (∃ c, A = {c} ∧ B ⊆ neighbors c) ∨ (∃ c, B = {c} ∧ A ⊆ neighbors c) := by
  by_cases small : A.card ≤ 1
  · obtain ⟨c, hc⟩ := ha
    have hac := Finset.card_le_one.mp small
    have eq : A = {c} := by
      ext x
      simpa only [Finset.mem_singleton] using
        (show x ∈ A ↔ x = c from ⟨fun hx => hac _ hx _ hc, fun h => h ▸ hc⟩)
    exact Or.inl ⟨c, eq, fun b hb' => (mem_neighbors c b).mpr (complete c hc b hb')⟩
  · obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (show 1 < A.card by omega)
    have sub : B ⊆ neighbors u ∩ neighbors v := by
      intro b h
      exact Finset.mem_inter.mpr ⟨(mem_neighbors _ _).mpr (complete _ hu b h),
        (mem_neighbors _ _).mpr (complete _ hv b h)⟩
    have le := (Finset.card_le_card sub).trans (common_neighbors u v huv)
    obtain ⟨c, hc⟩ := hb
    have eq : B = {c} := by
      ext x
      simpa only [Finset.mem_singleton] using
        (show x ∈ B ↔ x = c from ⟨fun hx => Finset.card_le_one.mp le _ hx _ hc, fun h => h ▸ hc⟩)
    refine Or.inr ⟨c, eq, fun a h => (mem_neighbors _ _).mpr ?_⟩
    rw [adj_comm]
    exact complete a h c hc

theorem rectangle_size {A B : Finset Vertex} (ha : A.Nonempty) (hb : B.Nonempty)
    (complete : ∀ a ∈ A, ∀ b ∈ B, Adj a b = true) : A.card * B.card ≤ 4 := by
  rcases rectangle_star ha hb complete with ⟨c, rfl, sub⟩ | ⟨c, rfl, sub⟩
  · simpa using (Finset.card_le_card sub).trans (degree_le_four c)
  · simpa using (Finset.card_le_card sub).trans (degree_le_four c)

end GridGeometry

/-! Counting the raw OR gates needed to assemble the leaf sets of stars in a grid.
Wire indices increase in evaluation order. Sets of pending wires make the bound
valid when gates are reused by several later wires. -/

namespace GridStarCount

variable {α : Type*} [DecidableEq α]

/-- A large signature inside a neighborhood is either copied from an earlier
wire or assembled by a paid binary union of earlier signatures. -/
def BuildsWithin (sig : ℕ → Finset α) (paid : ℕ → Prop)
    (leaves : Finset α) (n : ℕ) : Prop :=
  ∀ i < n, sig i ⊆ leaves → 1 < (sig i).card →
    (∃ j < i, sig i = sig j) ∨
      (paid i ∧ ∃ a < i, ∃ b < i, sig i = sig a ∪ sig b)

/-- A paid gate can be charged to this center only when its whole
signature fits and contains at least two distinct leaves. -/
def charge (sig : ℕ → Finset α) (paid : ℕ → Prop) (leaves : Finset α) (i : ℕ) :=
  paid i ∧ 1 < (sig i).card ∧ sig i ⊆ leaves

noncomputable def charges (sig : ℕ → Finset α) (paid : ℕ → Prop)
    (leaves : Finset α) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter (charge sig paid leaves)

omit [DecidableEq α] in
private theorem charges_mono (sig : ℕ → Finset α) (paid : ℕ → Prop)
    (leaves : Finset α) (n : ℕ) :
    charges sig paid leaves n ⊆ charges sig paid leaves (n+1) := by
  classical
  intro i hi
  simp only [charges, Finset.mem_filter, Finset.mem_range] at hi ⊢
  exact ⟨Nat.lt_succ_of_lt hi.1, hi.2⟩

omit [DecidableEq α] in
private theorem charges_add (sig : ℕ → Finset α) (paid : ℕ → Prop)
    (leaves : Finset α) (n : ℕ) (h : charge sig paid leaves n) :
    (charges sig paid leaves (n+1)).card = (charges sig paid leaves n).card + 1 := by
  classical
  simp [charges, Finset.range_add_one, Finset.filter_insert, h]

/-- Distinct labels visible at the demanded wires cost at least one paid
union for each label beyond the number of demanded wires. -/
theorem labels_le_demands_add_charges (sig : ℕ → Finset α) (paid : ℕ → Prop)
    (leaves : Finset α) (n : ℕ) (hbuild : BuildsWithin sig paid leaves n)
    (d : Finset ℕ) (hrange : ∀ i ∈ d, i < n) (hfit : ∀ i ∈ d, sig i ⊆ leaves) :
    (d.biUnion sig).card ≤ d.card + (charges sig paid leaves n).card := by
  classical
  induction n generalizing d with
  | zero =>
    have : d = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun i hi => Nat.not_lt_zero _ (hrange i hi))
    simp [this]
  | succ n ih =>
    have earlier : BuildsWithin sig paid leaves n := fun i hi => hbuild i (Nat.lt_succ_of_lt hi)
    have mono := Finset.card_le_card (charges_mono sig paid leaves n)
    by_cases hn : n ∈ d
    · let rest := d.erase n
      have reverse : insert n rest = d := Finset.insert_erase hn
      have restCount : rest.card + 1 = d.card := Finset.card_erase_add_one hn
      have restRange : ∀ i ∈ rest, i < n := by
        intro i hi
        have ⟨hne, hm⟩ := Finset.mem_erase.mp hi
        have := hrange i hm
        omega
      have restFit : ∀ i ∈ rest, sig i ⊆ leaves :=
        fun i hi => hfit i (Finset.mem_of_mem_erase hi)
      have decompose : d.biUnion sig = sig n ∪ rest.biUnion sig := by
        rw [← Finset.biUnion_insert, reverse]
      by_cases small : (sig n).card ≤ 1
      · have prev := ih earlier rest restRange restFit
        rw [decompose]
        have := Finset.card_union_le (sig n) (rest.biUnion sig)
        omega
      · have large : 1 < (sig n).card := by omega
        rcases hbuild n (Nat.lt_succ_self _) (hfit n hn) large with ⟨j, hj, heq⟩ | ⟨hp, a, ha, b, hb, heq⟩
        · have fitj : sig j ⊆ leaves := heq ▸ hfit n hn
          have prev := ih earlier (insert j rest) (by simpa [hj] using restRange)
            (by simpa [fitj] using restFit)
          rw [Finset.biUnion_insert, ← heq, ← decompose] at prev
          have := Finset.card_insert_le j rest
          omega
        · have fitab : sig a ⊆ leaves ∧ sig b ⊆ leaves := by
            simpa [heq, Finset.union_subset_iff] using hfit n hn
          have prev := ih earlier (insert a (insert b rest))
            (by simpa [ha, hb] using restRange)
            (by simpa [fitab.1, fitab.2] using restFit)
          simp only [Finset.biUnion_insert] at prev
          rw [← Finset.union_assoc, ← heq, ← decompose] at prev
          have := Finset.card_insert_le a (insert b rest)
          have := Finset.card_insert_le b rest
          have := charges_add sig paid leaves n ⟨hp, large, hfit n hn⟩
          omega
    · have below : ∀ i ∈ d, i < n := by
        intro i hi
        have ne : i ≠ n := fun eq => hn (eq ▸ hi)
        have := hrange i hi
        omega
      have := ih earlier d below hfit
      omega


/-- An OR gate with an empty operand copies the other wire's signature.
If both operands have labels, it is eligible to be paid. A clean AND has
empty signature and therefore never presents a large signature. -/
theorem builds_of_wire_cases (sig : ℕ → Finset α) (paid : ℕ → Prop)
    (leaves : Finset α) (n : ℕ)
    (wireCases : ∀ i < n, (sig i ⊆ leaves → (sig i).card ≤ 1) ∨
      ∃ a < i, ∃ b < i, sig i = sig a ∪ sig b ∧
        (sig a ≠ ∅ → sig b ≠ ∅ → paid i)) : BuildsWithin sig paid leaves n := by
  intro i hi fit large
  rcases wireCases i hi with source | ⟨a, ha, b, hb, eq, counted⟩
  · exact False.elim (Nat.not_lt.mpr (source fit) large)
  · by_cases ea : sig a = ∅
    · exact Or.inl ⟨b, hb, by simpa [ea] using eq⟩
    by_cases eb : sig b = ∅
    · exact Or.inl ⟨a, ha, by simpa [eb] using eq⟩
    exact Or.inr ⟨counted ea eb, a, ha, b, hb, eq⟩

/-- Different centers can share at most one neighbor. Consequently a gate
counted for one center cannot be counted for another. Global budgeting then
costs at least the total number of covered center–leaf pairs minus the
total number of demanded leaf-side wires. -/
theorem grouped_labels_bound {κ : Type*} (centers : Finset κ)
    (neighbors : κ → Finset α) (sig : ℕ → Finset α) (paid : Finset ℕ)
    (demands : κ → Finset ℕ) (n : ℕ)
    (overlap : ∀ c ∈ centers, ∀ d ∈ centers, c ≠ d →
      ((neighbors c) ∩ (neighbors d)).card ≤ 1)
    (build : ∀ c ∈ centers, BuildsWithin sig (· ∈ paid) (neighbors c) n)
    (time : ∀ c ∈ centers, ∀ i ∈ demands c, i < n)
    (fit : ∀ c ∈ centers, ∀ i ∈ demands c, sig i ⊆ neighbors c) :
    (∑ c ∈ centers, ((demands c).biUnion sig).card) ≤
      (∑ c ∈ centers, (demands c).card) + paid.card := by
  classical
  let used := fun c => charges sig (· ∈ paid) (neighbors c) n
  have disj : (centers : Set κ).PairwiseDisjoint used := by
    intro c hc d hd ne
    apply Finset.disjoint_left.mpr
    intro i hic hid
    have h₁ := (Finset.mem_filter.mp hic).2
    have h₂ := (Finset.mem_filter.mp hid).2
    change charge sig (· ∈ paid) (neighbors c) i at h₁
    change charge sig (· ∈ paid) (neighbors d) i at h₂
    have inc := Finset.card_le_card (Finset.subset_inter h₁.2.2 h₂.2.2)
    have := overlap c hc d hd ne
    exact (Nat.not_lt.mpr (Nat.le_trans inc this)) h₁.2.1
  have total : centers.biUnion used ⊆ paid := by
    intro i hi
    obtain ⟨c, _, h⟩ := Finset.mem_biUnion.mp hi
    exact (Finset.mem_filter.mp h).2.1
  calc
    _ ≤ ∑ c ∈ centers, ((demands c).card + (used c).card) := by
      apply Finset.sum_le_sum
      intro c hc
      exact labels_le_demands_add_charges sig (· ∈ paid) (neighbors c) n
        (build c hc) (demands c) (time c hc) (fit c hc)
    _ = (∑ c ∈ centers, (demands c).card) + (centers.biUnion used).card := by
      rw [Finset.sum_add_distrib, Finset.card_biUnion disj]
    _ ≤ _ := Nat.add_le_add_left (Finset.card_le_card total) _


/-- Cover a family of edges by the leaf signatures of actual productive
stars. Each star names one center and one leaf-side wire. Several stars
may use the same wire, and several stars may cover the same edge. -/
theorem covered_edges_le_stars_add_paid {κ ε : Type*} [DecidableEq κ] [DecidableEq ε]
    (neighbors : κ → Finset α) (sig : ℕ → Finset α) (stars paid : Finset ℕ)
    (owner : ℕ → κ) (leaf : ℕ → ℕ) (n : ℕ) (edges : Finset ε) (encode : κ → α → ε)
    (overlap : ∀ c d, c ≠ d → ((neighbors c) ∩ (neighbors d)).card ≤ 1)
    (build : ∀ c, BuildsWithin sig (· ∈ paid) (neighbors c) n)
    (time : ∀ g ∈ stars, leaf g < n)
    (fit : ∀ g ∈ stars, sig (leaf g) ⊆ neighbors (owner g))
    (cover : ∀ e ∈ edges, ∃ g ∈ stars, ∃ v ∈ sig (leaf g), encode (owner g) v = e) :
    edges.card ≤ stars.card + paid.card := by
  classical
  let centers := stars.image owner
  let byCenter := fun c => stars.filter (fun g => owner g = c)
  let demands := fun c => (byCenter c).image leaf
  let labels := fun c => (demands c).biUnion sig
  have covered : edges ⊆ centers.biUnion (fun c => (labels c).image (encode c)) := by
    intro e he
    obtain ⟨g, hg, v, hv, rfl⟩ := cover e he
    apply Finset.mem_biUnion.mpr
    refine ⟨owner g, Finset.mem_image_of_mem owner hg, Finset.mem_image_of_mem _ ?_⟩
    apply Finset.mem_biUnion.mpr
    exact ⟨leaf g, Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hg, rfl⟩), hv⟩
  have coverCount : edges.card ≤ ∑ c ∈ centers, (labels c).card := by
    apply (Finset.card_le_card covered).trans
    apply Finset.card_biUnion_le.trans
    exact Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
  have lower := grouped_labels_bound centers neighbors sig paid demands n
    (fun c _ d _ hd => overlap c d hd) (fun c _ => build c)
    (by
      intro c _ i hi
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hi
      exact time g (Finset.mem_filter.mp hg).1)
    (by
      intro c _ i hi
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨hs, rfl⟩ := Finset.mem_filter.mp hg
      exact fit g hs)
  have bounded : (∑ c ∈ centers, (demands c).card) ≤ stars.card := by
    calc
      _ ≤ ∑ c ∈ centers, (byCenter c).card := Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
      _ = stars.card := (Finset.card_eq_sum_card_fiberwise
        (fun g hg => Finset.mem_image_of_mem owner hg)).symm
  exact coverCount.trans (lower.trans (Nat.add_le_add_right bounded _))

omit [DecidableEq α] in
/-- The independent degree bound: stars of at most four leaves cannot
cover 24 edges with fewer than six centers counted with multiplicity. -/
theorem covered_edges_le_degree_mul_stars {κ ε : Type*} [DecidableEq ε]
    (sig : ℕ → Finset α) (stars : Finset ℕ) (owner : ℕ → κ) (leaf : ℕ → ℕ)
    (edges : Finset ε) (encode : κ → α → ε) (degree : ℕ)
    (maxLeaves : ∀ g ∈ stars, (sig (leaf g)).card ≤ degree)
    (cover : ∀ e ∈ edges, ∃ g ∈ stars, ∃ v ∈ sig (leaf g), encode (owner g) v = e) :
    edges.card ≤ degree * stars.card := by
  classical
  have covered : edges ⊆ stars.biUnion (fun g => (sig (leaf g)).image (encode (owner g))) := by
    intro e he
    obtain ⟨g, hg, v, hv, h⟩ := cover e he
    exact Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_image.mpr ⟨v, hv, h⟩⟩
  calc
    _ ≤ _ := Finset.card_le_card covered
    _ ≤ _ := Finset.card_biUnion_le
    _ ≤ ∑ _g ∈ stars, degree := Finset.sum_le_sum
      (fun g hg => Finset.card_image_le.trans (maxLeaves g hg))
    _ = _ := by simp [Nat.mul_comm]

end GridStarCount

/-!
A point–line pair accepted by an AND/OR circuit but rejected on each singleton
requires a gate that combines the two singleton signals. Descending from the
output keeps the witness in its cone, even when the circuit has unused gates.
The supplied line-OR ports are included in the grid instantiation.
-/
namespace GridCleanWitness

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_6973 (wires_gate wires_len wires_eq run_preserves gateAt_eq value)

def wire (C : Circuit) (x : List Bool) (w : ℕ) := (C.wires x).getD w false

/-- A wire feeds itself or an actual downstream gate via a sequence of operand reads. -/
inductive Feeds (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop where
  | refl (w) : Feeds n C w w
  | next {s w j} (path : Feeds n C s w) (existsGate : j < C.size)
      (reads : w ∈ (gateAt C j).inputs) : Feeds n C s (n + j)

/-- The pair activates a wire while either singleton alone leaves it inactive. -/
def PairOnly (left right both : Bool) : Prop :=
  both = true ∧ left = false ∧ right = false

/-- Opposite operands are activated by opposite singletons. -/
def Crossed (la ra lb rb : Bool) : Prop :=
  (la = true ∧ ra = false ∧ lb = false ∧ rb = true) ∨
  (lb = true ∧ rb = false ∧ la = false ∧ ra = true)

private theorem and_step : ∀ la ra za lb rb zb : Bool,
    PairOnly (la && lb) (ra && rb) (za && zb) →
    PairOnly la ra za ∨ PairOnly lb rb zb ∨ Crossed la ra lb rb := by
  intro la ra za lb rb zb
  cases la <;> cases ra <;> cases za <;> cases lb <;> cases rb <;> cases zb <;>
    simp [PairOnly, Crossed]

private theorem or_step : ∀ la ra za lb rb zb : Bool,
    PairOnly (la || lb) (ra || rb) (za || zb) →
    PairOnly la ra za ∨ PairOnly lb rb zb := by unfold PairOnly; decide

private theorem two_inputs (l : List ℕ) (h : l.length = 2) : ∃ a b, l = [a,b] := by
  match l, h with
  | [a,b], _ => exact ⟨a,b,rfl⟩

/-- From the output (or any specified wire), trace back to an AND gate whose
two operand signatures contain the two different singleton inputs. -/
theorem crossed_and_feeds {n : ℕ} (C : Circuit) (shape : IsAO2 n C)
    (left right both : List Bool)
    (hl : left.length = n) (hr : right.length = n) (hz : both.length = n)
    (ports : ∀ i < n, both.getD i false = (left.getD i false || right.getD i false))
    (w : ℕ) (onPair : PairOnly (wire C left w) (wire C right w) (wire C both w)) :
    ∃ j < C.size, ∃ a b, (gateAt C j).op = GateOp.and ∧
      (gateAt C j).inputs = [a,b] ∧ Feeds n C (n+j) w ∧
      Crossed (wire C left a) (wire C right a) (wire C left b) (wire C right b) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < n
    · have base (x : List Bool) (hx : x.length = n) : wire C x w = x.getD w false := by
        unfold wire
        rw [wires_eq]
        exact run_preserves _ _ _ (by omega)
      rcases onPair with ⟨hb, hleft, hright⟩
      rw [base left hl] at hleft
      rw [base right hr] at hright
      rw [base both hz, ports w hw, hleft, hright] at hb
      contradiction
    · let j := w - n
      have hjw : n + j = w := by dsimp [j]; omega
      have hreal : j < C.size := by
        by_contra! h
        have tooLarge : (C.wires both).length ≤ w := by rw [wires_len, hz]; omega
        have ff : wire C both w = false := List.getD_eq_default _ _ tooLarge
        have tt := onPair.1
        simp [ff] at tt
      have mem : gateAt C j ∈ C.gates := by rw [gateAt_eq C j hreal]; exact List.getElem_mem _
      obtain ⟨a,b,hab⟩ := two_inputs _ (shape.2.2 _ mem)
      have ha : a ∈ (gateAt C j).inputs := by simp [hab]
      have hb : b ∈ (gateAt C j).inputs := by simp [hab]
      have backA := shape.2.1 j hreal a ha
      have backB := shape.2.1 j hreal b hb
      have reads (x : List Bool) (hx : x.length = n) :
          wire C x w = (gateAt C j).op.eval [wire C x a, wire C x b] := by
        unfold wire
        rw [← hjw, wires_gate n C shape.2.1 x hx j hreal]
        simp [value, hab]
      have extendPath (u : ℕ) (before : u < w) (readU : u ∈ (gateAt C j).inputs)
          (act : PairOnly (wire C left u) (wire C right u) (wire C both u)) :
          ∃ i < C.size, ∃ c d, (gateAt C i).op = GateOp.and ∧
            (gateAt C i).inputs = [c,d] ∧ Feeds n C (n+i) w ∧
            Crossed (wire C left c) (wire C right c) (wire C left d) (wire C right d) := by
        obtain ⟨i,hi,c,d,op,args,path,split⟩ := ih u before act
        exact ⟨i,hi,c,d,op,args,hjw ▸ Feeds.next path hreal readU,split⟩
      rw [reads left hl, reads right hr, reads both hz] at onPair
      rcases shape.1 _ mem with hand | hor
      · simp [hand, GateOp.eval] at onPair
        rcases and_step _ _ _ _ _ _ onPair with aa | bb | split
        · exact extendPath a (by omega) ha aa
        · exact extendPath b (by omega) hb bb
        · exact ⟨j,hreal,a,b,hand,hab,hjw ▸ Feeds.refl _,split⟩
      · simp [hor, GateOp.eval] at onPair
        rcases or_step _ _ _ _ _ _ onPair with aa | bb
        · exact extendPath a (by omega) ha aa
        · exact extendPath b (by omega) hb bb

open GridReplay (bank)

private theorem bank_union :
    ∀ (p : Fin 6) (l : Fin 11) (i : Fin 30),
      (bank (2^p.val) (2^l.val)).getD i.val false =
        ((bank (2^p.val) 0).getD i.val false || (bank 0 (2^l.val)).getD i.val false) := by
  decide +kernel

/-- For the actual thirty grid input ports, each accepted pair for which both
singletons are rejected has a witnessing AND gate on an output path. -/
theorem grid_pair_witness (C : Circuit) (shape : IsAO2 30 C)
    (p : Fin 6) (l : Fin 11)
    (hit : C.eval (bank (2^p.val) (2^l.val)) = true)
    (noPoint : C.eval (bank (2^p.val) 0) = false)
    (noLine : C.eval (bank 0 (2^l.val)) = false) :
    ∃ j < C.size, ∃ a b, (gateAt C j).op = GateOp.and ∧
      (gateAt C j).inputs = [a,b] ∧ Feeds 30 C (30+j) C.output ∧
      Crossed (wire C (bank (2^p.val) 0) a) (wire C (bank 0 (2^l.val)) a)
        (wire C (bank (2^p.val) 0) b) (wire C (bank 0 (2^l.val)) b) :=
  crossed_and_feeds C shape _ _ _ rfl rfl rfl
    (fun i hi => bank_union p l ⟨i,hi⟩) C.output ⟨hit,noPoint,noLine⟩

/-- Every required edge of a circuit passing the grid specification is
covered by a crossed AND gate. Both singleton rejections come from the
specified negative tests. -/
theorem grid_edge_covered (C : Circuit) (shape : IsAO2 30 C)
    (positive : ∀ (p : Fin 6) (l : Fin 11), (GridReplay.rows.getD p.val 0).testBit l.val = true →
      C.eval (bank (2^p.val) (2^l.val)) = true)
    (negative : ∀ p l, GridPairCover.negative p l → C.eval (bank p l) = false)
    (p : Fin 6) (l : Fin 11) (edge : (GridReplay.rows.getD p.val 0).testBit l.val = true) :
    ∃ j < C.size, ∃ a b, (gateAt C j).op = GateOp.and ∧
      (gateAt C j).inputs = [a,b] ∧ Feeds 30 C (30+j) C.output ∧
      Crossed (wire C (bank (2^p.val) 0) a) (wire C (bank 0 (2^l.val)) a)
        (wire C (bank (2^p.val) 0) b) (wire C (bank 0 (2^l.val)) b) := by
  have onePoint : ∀ p : Fin 6, GridPairCover.negative (2^p.val) 0 := by decide +kernel
  have oneLine : ∀ l : Fin 11, GridPairCover.negative 0 (2^l.val) := by decide +kernel
  exact grid_pair_witness C shape p l (positive p l edge) (negative _ _ (onePoint p))
    (negative _ _ (oneLine l))

open GridPairCover (point line points lines)

def singleBank (i : Fin 17) := bank (point i) (line i)
def pairBank (i j : Fin 17) := bank (points i j) (lines i j)

/-- Monotonicity is applied to the actual thirty ports, including all thirteen
supplied ORs, whose values depend on the physical line bits. -/
theorem singleton_preserved (C : Circuit) (shape : IsAO2 30 C) (i j : Fin 17) (w : ℕ) :
    wire C (singleBank i) w = true → wire C (pairBank i j) w = true := by
  have port : ∀ (i j : Fin 17) (k : Fin 30), (singleBank i).getD k.val false = true →
      (pairBank i j).getD k.val false = true := by decide +kernel
  apply PEqualNP.Outside.L_meta_8029.wire_mono C _ (singleBank i) (pairBank i j) rfl _ w
  · intro g hg
    exact ⟨by simpa using shape.1 g hg, le_of_eq (shape.2.2 g hg)⟩
  · intro k hk
    by_cases h : k < 30
    · exact port i j ⟨k,h⟩ hk
    · have out : (singleBank i).length ≤ k := by change 30 ≤ k; omega
      rw [List.getD_eq_default _ _ out] at hk
      contradiction

private theorem pair_comm (i j : Fin 17) : pairBank i j = pairBank j i := by
  simp only [pairBank, points, lines, Nat.or_comm (point i), Nat.or_comm (line i)]

/-- All singleton pairs from opposite operands of an AND activate it. -/
theorem pair_fires (C : Circuit) (shape : IsAO2 30 C) {j a b : ℕ} (inRange : j < C.size)
    (isAnd : (gateAt C j).op = GateOp.and) (operands : (gateAt C j).inputs = [a,b])
    (i t : Fin 17) (left : wire C (singleBank i) a = true)
    (right : wire C (singleBank t) b = true) : wire C (pairBank i t) (30+j) = true := by
  have l := singleton_preserved C shape i t a left
  have r := singleton_preserved C shape t i b right
  rw [pair_comm t i] at r
  unfold wire at *
  rw [wires_gate 30 C shape.2.1 (pairBank i t) rfl j inRange]
  simp only [value, isAnd, operands, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id, l, r]
  rfl

/-- A clean AND's two operand signatures are disjoint and their cross product
contains no forbidden physical pairs. Cleanliness is required only on distinct
forbidden two-bit inputs. -/
theorem clean_rectangle (C : Circuit) (shape : IsAO2 30 C) {j a b : ℕ} (inRange : j < C.size)
    (isAnd : (gateAt C j).op = GateOp.and) (operands : (gateAt C j).inputs = [a,b])
    (clean : ∀ i t : Fin 17, i ≠ t → GridPairCover.negative (points i t) (lines i t) →
      wire C (pairBank i t) (30+j) = false)
    (i t : Fin 17) (left : wire C (singleBank i) a = true)
    (right : wire C (singleBank t) b = true) :
    i ≠ t ∧ ¬ GridPairCover.negative (points i t) (lines i t) := by
  have distinct : i ≠ t := by
    rintro rfl
    have extension : ∀ u : Fin 17, ∃ v : Fin 17, u ≠ v ∧
        GridPairCover.negative (points u v) (lines u v) := by decide +kernel
    obtain ⟨v,ne,neg⟩ := extension i
    have l := singleton_preserved C shape i v a left
    have r := singleton_preserved C shape i v b right
    have off := clean i v ne neg
    unfold wire at l r off
    rw [wires_gate 30 C shape.2.1 (pairBank i v) rfl j inRange] at off
    simp only [value, isAnd, operands, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id, l, r] at off
    contradiction
  refine ⟨distinct, fun neg => ?_⟩
  have on' := pair_fires C shape inRange isAnd operands i t left right
  rw [clean i t distinct neg] at on'
  contradiction

end GridCleanWitness

/-! Singleton signatures for the thirty-port grid. These lemmas connect
the concrete circuit semantics to the finite geometric and counting arguments. -/
namespace GridCircuitSigs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_6973 (wires_gate wires_eq run_preserves value)
open GridCleanWitness
open GridPairCover (point line points lines)
open GridGeometry (Vertex Adj directed edges bankSupport)
open GridReplay (bank)

def sig (C : Circuit) (w : ℕ) : Finset Vertex :=
  Finset.univ.filter fun v => wire C (singleBank v) w = true

theorem mem_sig {C : Circuit} {w : ℕ} {v : Vertex} :
    v ∈ sig C w ↔ wire C (singleBank v) w = true := by simp [sig]

/-- Every AND on a path to the output is off on each forbidden two-bit input. -/
def LiveClean (C : Circuit) : Prop :=
  ∀ j < C.size, (gateAt C j).op = GateOp.and → Feeds 30 C (30+j) C.output →
    ∀ i t : Vertex, i ≠ t → GridPairCover.negative (points i t) (lines i t) →
      wire C (pairBank i t) (30+j) = false

def Positive (C : Circuit) : Prop :=
  ∀ (p : Fin 6) (l : Fin 11), (GridReplay.rows.getD p.val 0).testBit l.val = true →
    C.eval (bank (2^p.val) (2^l.val)) = true

def Negative (C : Circuit) : Prop :=
  ∀ p l, GridPairCover.negative p l → C.eval (bank p l) = false

theorem bank_sig (C : Circuit) (i : Fin 30) : sig C i.val = bankSupport i := by
  have inputs : ∀ (i : Fin 30) (u : Vertex),
      (singleBank u).getD i.val false = true ↔ u ∈ bankSupport i := by decide +kernel
  ext u
  rw [mem_sig, ← inputs i u]
  unfold wire
  rw [wires_eq, run_preserves _ _ _ (show i.val < (singleBank u).length from i.isLt)]

theorem or_sig (C : Circuit) (shape : IsAO2 30 C) {j a b : ℕ} (hj : j < C.size)
    (hop : (gateAt C j).op = GateOp.or) (hargs : (gateAt C j).inputs = [a,b]) :
    sig C (30+j) = sig C a ∪ sig C b := by
  ext u
  simp only [Finset.mem_union, mem_sig, wire]
  rw [wires_gate 30 C shape.2.1 (singleBank u) rfl j hj]
  simp only [value, hop, hargs, List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
    List.any_nil, id, Bool.or_false, Bool.or_eq_true]

theorem clean_and_sig (C : Circuit) (shape : IsAO2 30 C) (clean : LiveClean C)
    {j : ℕ} (hj : j < C.size) (hop : (gateAt C j).op = GateOp.and)
    (live : Feeds 30 C (30+j) C.output) : sig C (30+j) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  have enlarge : ∀ u : Vertex, ∃ v : Vertex, u ≠ v ∧
      GridPairCover.negative (points u v) (lines u v) := by decide +kernel
  obtain ⟨v,ne,neg⟩ := enlarge u
  have on' := singleton_preserved C shape u v _ (mem_sig.mp hu)
  rw [clean j hj hop live u v ne neg] at on'
  contradiction

theorem clean_and_adj (C : Circuit) (shape : IsAO2 30 C) (clean : LiveClean C)
    {j a b : ℕ} (hj : j < C.size) (hop : (gateAt C j).op = GateOp.and)
    (hargs : (gateAt C j).inputs = [a,b]) (live : Feeds 30 C (30+j) C.output)
    {u v : Vertex} (hu : u ∈ sig C a) (hv : v ∈ sig C b) : Adj u v = true := by
  have geom : ∀ u v : Vertex, ¬ GridPairCover.negative (points u v) (lines u v) →
      Adj u v = true := by decide +kernel
  exact geom u v (clean_rectangle C shape hj hop hargs (clean j hj hop live) u v
    (mem_sig.mp hu) (mem_sig.mp hv)).2

theorem output_sig (C : Circuit) (negative : Negative C) : sig C C.output = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hit
  have single : ∀ u : Vertex, GridPairCover.negative (point u) (line u) := by decide +kernel
  have on' := mem_sig.mp hit
  change C.eval (bank (point u) (line u)) = true at on'
  rw [negative _ _ (single u)] at on'
  contradiction

/-- Every one of the 24 directed grid edges is covered by the rectangle of a
live AND gate, in either orientation of its two operands. -/
theorem edge_covered (C : Circuit) (shape : IsAO2 30 C)
    (positive : Positive C) (negative : Negative C) {u v : Vertex} (edge : (u,v) ∈ edges) :
    ∃ j < C.size, ∃ a b, (gateAt C j).op = GateOp.and ∧ (gateAt C j).inputs = [a,b] ∧
      Feeds 30 C (30+j) C.output ∧
      ((u ∈ sig C a ∧ v ∈ sig C b) ∨ (v ∈ sig C a ∧ u ∈ sig C b)) := by
  have facts : ∀ u v : Vertex, directed u v = true →
      let p := Fin.ofNat 6 u.val
      let l := Fin.ofNat 11 (v.val-6)
      (GridReplay.rows.getD p.val 0).testBit l.val = true ∧
        singleBank u = bank (2^p.val) 0 ∧ singleBank v = bank 0 (2^l.val) := by decide +kernel
  obtain ⟨ok,hp,hl⟩ := facts u v ((Finset.mem_filter.mp edge).2)
  obtain ⟨j,hj,a,b,op,ins,path,split⟩ := grid_edge_covered C shape positive negative _ _ ok
  refine ⟨j,hj,a,b,op,ins,path,?_⟩
  simp only [mem_sig, hp, hl]
  rcases split with h | h
  · exact Or.inl ⟨h.1,h.2.2.2⟩
  · exact Or.inr ⟨h.2.2.2,h.1⟩

end GridCircuitSigs

/-!
A gate-count lemma for finite fan-in-two circuits. Follow an empty-signature
wire forward. Unless it is the output, some gate in the output cone must read
it. Counting distinct uses proves the merger bound even with shared wires,
repeated operands, and paths that leave the empty-signature gates.
-/
namespace GridConeCount

open Finset
variable {Wire : Type*} [DecidableEq Wire]

/-- Both ends of a use are wire labels. Only the reader must be a gate. -/
def Reads (gates : Finset Wire) (inputs : Wire → Finset Wire) (u g : Wire) : Prop :=
  g ∈ gates ∧ u ∈ inputs g

/-- The gates on directed paths ending at the designated output. -/
noncomputable def cone (gates : Finset Wire) (inputs : Wire → Finset Wire)
    (output : Wire) : Finset Wire := by
  classical
  exact gates.filter (fun g => Relation.ReflTransGen (Reads gates inputs) g output)

omit [DecidableEq Wire] in
/-- Every gate in the cone other than its output has a reader in the cone. -/
theorem exists_reader {gates : Finset Wire} {inputs : Wire → Finset Wire}
    {output u : Wire} (hu : u ∈ cone gates inputs output) (hne : u ≠ output) :
    ∃ g ∈ cone gates inputs output, u ∈ inputs g := by
  classical
  obtain ⟨_, path⟩ := mem_filter.mp hu
  obtain ⟨g, ⟨hg, hin⟩, rest⟩ := path.cases_head.resolve_left hne
  exact ⟨g, mem_filter.mpr ⟨hg, rest⟩, hin⟩

/-- In a clean AND/OR circuit, every AND has empty singleton signature.
A gate with nonempty signature must therefore be an OR, and at least one
of its operands has nonempty signature. This is the only signature law used.

The three counts below are, in order, empty gates with no empty operand,
empty gates with an empty operand, and nonempty gates with an empty operand.
Empty gates of the first kind are the productive ANDs when all input ports
have nonempty signature and OR computes union. -/
theorem productive_le_other_add_mixed_add_one
    (gates : Finset Wire) (inputs : Wire → Finset Wire) (output : Wire)
    (empty : Wire → Prop) [DecidablePred empty]
    (hfan : ∀ g ∈ gates, (inputs g).card ≤ 2)
    (hpass : ∀ g ∈ gates, ¬empty g → ∃ u ∈ inputs g, ¬empty u) :
    let live := cone gates inputs output
    let used := fun g => (inputs g).filter empty
    (live.filter (fun g => empty g ∧ used g = ∅)).card ≤
      (live.filter (fun g => empty g ∧ (used g).Nonempty)).card +
      (live.filter (fun g => ¬empty g ∧ (used g).Nonempty)).card + 1 := by
  classical
  let live := cone gates inputs output
  let used := fun g => (inputs g).filter empty
  let P := fun g => empty g ∧ used g = ∅
  let B := fun g => empty g ∧ (used g).Nonempty
  let M := fun g => ¬empty g ∧ (used g).Nonempty
  change (live.filter P).card ≤ (live.filter B).card + (live.filter M).card + 1
  have allUsed : (live.filter empty).erase output ⊆ live.biUnion used := by
    intro u hu
    obtain ⟨hne, hu'⟩ := mem_erase.mp hu
    obtain ⟨hlive, hempty⟩ := mem_filter.mp hu'
    obtain ⟨g, hg, huin⟩ := exists_reader hlive hne
    exact mem_biUnion.mpr ⟨g, hg, mem_filter.mpr ⟨huin, hempty⟩⟩
  have need : (live.filter empty).card ≤ (∑ g ∈ live, (used g).card) + 1 := by
    have h := (card_le_card allUsed).trans card_biUnion_le
    by_cases hout : output ∈ live.filter empty
    · rw [card_erase_of_mem hout] at h
      omega
    · rw [erase_eq_of_notMem hout] at h
      omega
  have slots : ∀ g ∈ live, (used g).card ≤
      ((if B g then 1 else 0) + (if B g then 1 else 0)) + (if M g then 1 else 0) := by
    intro g hg
    have hgate : g ∈ gates := (mem_filter.mp hg).1
    by_cases hz : (used g).Nonempty
    · by_cases he : empty g
      · simpa [B, M, he, hz] using
          (card_filter_le (inputs g) empty).trans (hfan g hgate)
      · obtain ⟨u, hu, hn⟩ := hpass g hgate he
        have hs : used g ⊂ inputs g := Finset.ssubset_iff_subset_ne.mpr
          ⟨filter_subset _ _, fun eq => hn (mem_filter.mp (eq ▸ hu : u ∈ used g)).2⟩
        have lt := card_lt_card hs
        have two := hfan g hgate
        simp [B, M, he, hz]
        omega
    · simp [Finset.not_nonempty_iff_eq_empty.mp hz]
  have enough := Finset.sum_le_sum slots
  simp only [Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id] at enough
  change (∑ g ∈ live, (used g).card) ≤ (live.filter B).card + (live.filter B).card + (live.filter M).card at enough
  have split : (live.filter P).card + (live.filter B).card = (live.filter empty).card := by
    have h := card_filter_add_card_filter_not (s := live.filter empty) (fun g => used g = ∅)
    simpa [P, B, Finset.filter_filter, Finset.nonempty_iff_ne_empty] using h
  omega

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_6973 (wires_gate gateAt_eq value)

/-- Wire indices that are computed by gates in the project's circuit model. -/
def gateWires (n : ℕ) (C : Circuit) : Finset ℕ := Ico n (n + C.gates.length)

/-- The physical ports have no operands. Duplicate uses of an operand count once. -/
def inputsAt (n : ℕ) (C : Circuit) (w : ℕ) : Finset ℕ :=
  if w < n then ∅ else ((C.gates.getD (w - n) ⟨.or, []⟩).inputs).toFinset

/-- A wire has empty signature for these tests if it is false on all of them.
For the grid, take the 17 assignments that set one physical bit in the bank. -/
def silent (C : Circuit) (tests : List (List Bool)) (w : ℕ) : Prop :=
  ∀ x ∈ tests, (C.wires x).getD w false = false

instance (C : Circuit) (tests : List (List Bool)) : DecidablePred (silent C tests) :=
  fun w => by unfold silent; infer_instance

theorem gate_eval_eq (C : Circuit) (n : ℕ) (h : IsAO2 n C)
    (x : List Bool) (hx : x.length = n) (i : ℕ) (hi : i < C.gates.length) :
    (C.wires x).getD (n + i) false =
      C.gates[i].op.eval (C.gates[i].inputs.map fun v => (C.wires x).getD v false) := by
  rw [wires_gate n C h.2.1 x hx i hi, gateAt_eq C i hi]
  rfl

theorem active_operand (C : Circuit) (n : ℕ) (h : IsAO2 n C)
    (x : List Bool) (hx : x.length = n) {w : ℕ} (hw : w ∈ gateWires n C)
    (on : (C.wires x).getD w false = true) :
    ∃ v ∈ inputsAt n C w, (C.wires x).getD v false = true := by
  obtain ⟨lo, hi⟩ := mem_Ico.mp hw
  let i := w - n
  have hix : i < C.gates.length := by dsimp [i]; omega
  have eq : n + i = w := by dsimp [i]; omega
  rw [← eq, gate_eval_eq C n h x hx i hix] at on
  have hop := h.1 C.gates[i] (List.getElem_mem hix)
  have arity := h.2.2 C.gates[i] (List.getElem_mem hix)
  have existsOn : ∃ v ∈ C.gates[i].inputs, (C.wires x).getD v false = true := by
    rcases hop with ha | ho
    · rw [ha] at on
      simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply,
        id_eq] at on
      have ne : C.gates[i].inputs ≠ [] := by intro e; simp [e] at arity
      obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ ne
      exact ⟨v, hv, on v hv⟩
    · simpa [ho, GateOp.eval, List.any_eq_true] using on
  obtain ⟨v, hv, hvon⟩ := existsOn
  refine ⟨v, ?_, hvon⟩
  unfold inputsAt
  rw [ite_eq_right (Nat.not_lt.mpr lo)]
  change v ∈ (C.gates.getD i ⟨.or, []⟩).inputs.toFinset
  rw [List.getD_eq_getElem _ _ hix, List.mem_toFinset]
  exact hv

/-- The use-count bound for actual AO2 circuits and signatures obtained by
running the upstream evaluator. There is no graph or gate-count assumption
other than the posted circuit format and the specified length of each test. -/
theorem circuit_merge_bound (C : Circuit) (n : ℕ) (h : IsAO2 n C)
    (tests : List (List Bool)) (lengths : ∀ x ∈ tests, x.length = n) :
    let live := cone (gateWires n C) (inputsAt n C) C.output
    let empty := silent C tests
    let used := fun g => (inputsAt n C g).filter empty
    (live.filter (fun g => empty g ∧ used g = ∅)).card ≤
      (live.filter (fun g => empty g ∧ (used g).Nonempty)).card +
      (live.filter (fun g => ¬empty g ∧ (used g).Nonempty)).card + 1 := by
  apply productive_le_other_add_mixed_add_one
  · intro w hw
    obtain ⟨lo, hi⟩ := mem_Ico.mp hw
    have hix : w - n < C.gates.length := by omega
    simp only [inputsAt, ite_eq_right (Nat.not_lt.mpr lo), List.getD_eq_getElem _ _ hix]
    exact (List.toFinset_card_le ..).trans (h.2.2 _ (List.getElem_mem hix)).le
  · intro w hw hn
    change ¬ ∀ x ∈ tests, (C.wires x).getD w false = false at hn
    push Not at hn
    obtain ⟨x, hx, hxw⟩ := hn
    obtain ⟨v, hv, hvon⟩ := active_operand C n h x (lengths x hx) hw (by simpa using hxw)
    exact ⟨v, hv, fun he => Bool.noConfusion (hvon.symm.trans (he x hx))⟩

/-- Gate classes used in the final size count. -/
noncomputable def liveGates (n : ℕ) (C : Circuit) :=
  cone (gateWires n C) (inputsAt n C) C.output

def emptyInputs (n : ℕ) (C : Circuit) (tests : List (List Bool)) (w : ℕ) : Finset ℕ :=
  (inputsAt n C w).filter (silent C tests)

noncomputable def sourceGates (n : ℕ) (C : Circuit) (tests : List (List Bool)) : Finset ℕ :=
  (liveGates n C).filter fun w => silent C tests w ∧ emptyInputs n C tests w = ∅

noncomputable def rawGates (n : ℕ) (C : Circuit) (tests : List (List Bool)) : Finset ℕ :=
  (liveGates n C).filter fun w => ¬silent C tests w ∧ emptyInputs n C tests w = ∅

noncomputable def otherGates (n : ℕ) (C : Circuit) (tests : List (List Bool)) : Finset ℕ :=
  (liveGates n C).filter fun w => (emptyInputs n C tests w).Nonempty

theorem source_le_other_succ (C : Circuit) (n : ℕ) (h : IsAO2 n C)
    (tests : List (List Bool)) (lengths : ∀ x ∈ tests, x.length = n) :
    (sourceGates n C tests).card ≤ (otherGates n C tests).card + 1 := by
  classical
  have budget := circuit_merge_bound C n h tests lengths
  let live := liveGates n C
  let used := emptyInputs n C tests
  change (sourceGates n C tests).card ≤
    (live.filter (fun g => silent C tests g ∧ (used g).Nonempty)).card +
    (live.filter (fun g => ¬silent C tests g ∧ (used g).Nonempty)).card + 1 at budget
  have split := card_filter_add_card_filter_not (s := otherGates n C tests) (silent C tests)
  simp only [otherGates, Finset.filter_filter] at split
  unfold otherGates
  simpa only [live, used, and_comm, split] using budget

theorem class_cards_le_size (n : ℕ) (C : Circuit) (tests : List (List Bool)) :
    (sourceGates n C tests).card + (rawGates n C tests).card +
      (otherGates n C tests).card ≤ C.size := by
  classical
  let live := liveGates n C
  let cleanInputs := fun w => emptyInputs n C tests w = ∅
  have first := card_filter_add_card_filter_not (s := live.filter cleanInputs) (silent C tests)
  have rest := card_filter_add_card_filter_not (s := live) cleanInputs
  have a : (sourceGates n C tests).card + (rawGates n C tests).card =
      (live.filter cleanInputs).card := by
    simpa [sourceGates, rawGates, live, cleanInputs, Finset.filter_filter, and_comm] using first
  have b : (live.filter cleanInputs).card + (otherGates n C tests).card = live.card := by
    simpa [otherGates, live, cleanInputs, Finset.nonempty_iff_ne_empty] using rest
  rw [a, b]
  have bound : live.card ≤ (gateWires n C).card := card_filter_le _ _
  simpa [gateWires, Circuit.size] using bound

@[simp] theorem inputsAt_gate (n : ℕ) (C : Circuit) (j : ℕ) :
    inputsAt n C (n + j) = (gateAt C j).inputs.toFinset := by
  simp [inputsAt, gateAt, Nat.not_lt.mpr (Nat.le_add_right n j)]

private theorem emptyInputs_eq_empty (n : ℕ) (C : Circuit) (tests : List (List Bool)) (w : ℕ) :
    emptyInputs n C tests w = ∅ ↔ ∀ u ∈ inputsAt n C w, ¬silent C tests u := by
  simp [emptyInputs, Finset.filter_eq_empty_iff]

@[simp] theorem mem_sourceGates_iff (n : ℕ) (C : Circuit) (tests : List (List Bool)) (w : ℕ) :
    w ∈ sourceGates n C tests ↔ w ∈ liveGates n C ∧ silent C tests w ∧
      ∀ u ∈ inputsAt n C w, ¬silent C tests u := by
  simp [sourceGates, emptyInputs_eq_empty]

@[simp] theorem mem_rawGates_iff (n : ℕ) (C : Circuit) (tests : List (List Bool)) (w : ℕ) :
    w ∈ rawGates n C tests ↔ w ∈ liveGates n C ∧ ¬silent C tests w ∧
      ∀ u ∈ inputsAt n C w, ¬silent C tests u := by
  simp [rawGates, emptyInputs_eq_empty]

theorem feeds_iff_reachable (n : ℕ) (C : Circuit) (u w : ℕ) :
    GridCleanWitness.Feeds n C u w ↔
      Relation.ReflTransGen (Reads (gateWires n C) (inputsAt n C)) u w := by
  constructor
  · intro path
    induction path with
    | refl => exact .refl
    | @next v j p hj read ih =>
      apply ih.tail
      refine ⟨mem_Ico.mpr ⟨by omega, by change j < C.gates.length at hj; omega⟩, ?_⟩
      simpa only [inputsAt_gate, List.mem_toFinset] using read
  · intro path
    induction path with
    | refl => exact .refl _
    | @tail a b p hab ih =>
      obtain ⟨hg, hup⟩ := hab
      obtain ⟨lo, hi⟩ := mem_Ico.mp hg
      let j := b - n
      have hj : j < C.size := by dsimp [j, Circuit.size]; omega
      have hw : n + j = b := by dsimp [j]; omega
      rw [← hw, inputsAt_gate, List.mem_toFinset] at hup
      exact hw ▸ GridCleanWitness.Feeds.next ih hj hup

@[simp] theorem mem_liveGates_iff (n : ℕ) (C : Circuit) (w : ℕ) :
    w ∈ liveGates n C ↔ w ∈ gateWires n C ∧ GridCleanWitness.Feeds n C w C.output := by
  classical
  simp only [liveGates, cone, mem_filter, feeds_iff_reachable]

end GridConeCount

namespace GridCoverCount

open GridGeometry

/-- Physical points have smaller vertex indices than physical lines. -/
def canonicalEdge (x y : Vertex) : Vertex × Vertex := (min x y, max x y)

theorem edge_sorted : ∀ e ∈ edges, canonicalEdge e.1 e.2 = e := by decide +kernel

theorem canonicalEdge_swap (x y : Vertex) : canonicalEdge x y = canonicalEdge y x := by
  simp [canonicalEdge, min_comm x y, max_comm x y]

/-- For the actual grid, the productive ANDs must cover at least six stars.
Together those stars and their paid raw ORs require at least 24 gates. -/
theorem star_counts (sig : ℕ → Finset Vertex) (stars paid : Finset ℕ)
    (center : ℕ → Vertex) (leafWire : ℕ → ℕ) (n : ℕ)
    (build : ∀ c, GridStarCount.BuildsWithin sig (· ∈ paid) (neighbors c) n)
    (time : ∀ g ∈ stars, leafWire g < n)
    (fit : ∀ g ∈ stars, sig (leafWire g) ⊆ neighbors (center g))
    (cover : ∀ e ∈ edges, ∃ g ∈ stars, ∃ v ∈ sig (leafWire g),
      canonicalEdge (center g) v = e) :
    24 ≤ stars.card + paid.card ∧ 24 ≤ 4 * stars.card := by
  constructor
  · rw [← edge_count]
    exact GridStarCount.covered_edges_le_stars_add_paid neighbors sig stars paid center
      leafWire n edges canonicalEdge common_neighbors build time fit cover
  · rw [← edge_count]
    exact GridStarCount.covered_edges_le_degree_mul_stars sig stars center leafWire
      edges canonicalEdge 4
      (fun g hg => (Finset.card_le_card (fit g hg)).trans (degree_le_four _)) cover


/-- The counting bound stated on the two raw operands of each productive
AND. It uses the grid's rectangle theorem to choose a center, including
when both operands are singletons and either orientation is possible. -/
theorem rectangle_counts (sig : ℕ → Finset Vertex) (stars paid : Finset ℕ)
    (left right : ℕ → ℕ) (n : ℕ)
    (build : ∀ c, GridStarCount.BuildsWithin sig (· ∈ paid) (neighbors c) n)
    (time : ∀ g ∈ stars, left g < n ∧ right g < n)
    (nonempty : ∀ g ∈ stars, (sig (left g)).Nonempty ∧ (sig (right g)).Nonempty)
    (complete : ∀ g ∈ stars, ∀ x ∈ sig (left g), ∀ y ∈ sig (right g), Adj x y = true)
    (cover : ∀ e ∈ edges, ∃ g ∈ stars,
      (e.1 ∈ sig (left g) ∧ e.2 ∈ sig (right g)) ∨
      (e.2 ∈ sig (left g) ∧ e.1 ∈ sig (right g))) :
    24 ≤ stars.card + paid.card ∧ 24 ≤ 4 * stars.card := by
  classical
  have selectStar : ∀ g, ∃ c : Vertex, ∃ l : ℕ, g ∈ stars →
      l < n ∧ sig l ⊆ neighbors c ∧
      (∀ x ∈ sig (left g), ∀ y ∈ sig (right g),
        ∃ v ∈ sig l, canonicalEdge c v = canonicalEdge x y) := by
    intro g
    by_cases hg : g ∈ stars
    · rcases rectangle_star (nonempty g hg).1 (nonempty g hg).2 (complete g hg) with
        ⟨c, singleton, sub⟩ | ⟨c, singleton, sub⟩
      · refine ⟨c, right g, fun _ => ⟨(time g hg).2, sub, ?_⟩⟩
        intro x hx y hy
        have eq : x = c := Finset.mem_singleton.mp (singleton ▸ hx)
        exact ⟨y, hy, eq ▸ rfl⟩
      · refine ⟨c, left g, fun _ => ⟨(time g hg).1, sub, ?_⟩⟩
        intro x hx y hy
        have eq : y = c := Finset.mem_singleton.mp (singleton ▸ hy)
        exact ⟨x, hx, eq ▸ canonicalEdge_swap c x⟩
    · exact ⟨0, 0, fun h => (hg h).elim⟩
  choose center leaf facts using selectStar
  apply star_counts sig stars paid center leaf n build (fun g hg => (facts g hg).1)
    (fun g hg => (facts g hg).2.1)
  intro e he
  obtain ⟨g, hg, hit⟩ := cover e he
  refine ⟨g, hg, ?_⟩
  rcases hit with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · obtain ⟨v, hv, pair⟩ := (facts g hg).2.2 _ hx _ hy
    exact ⟨v, hv, pair.trans (edge_sorted e he)⟩
  · obtain ⟨v, hv, pair⟩ := (facts g hg).2.2 _ hx _ hy
    exact ⟨v, hv, pair.trans ((canonicalEdge_swap _ _).trans (edge_sorted e he))⟩

end GridCoverCount

/-! Connect singleton signatures from the actual 30-port circuit to the
raw-OR count. Wires outside the output cone receive empty signatures here,
so unused gates need no cleanliness assumption. -/
namespace GridLiveBuild

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_6973 (gateAt_eq)
open GridGeometry GridCleanWitness GridCircuitSigs GridConeCount

def tests : List (List Bool) := List.ofFn singleBank

theorem tests_length : ∀ x ∈ tests, x.length = 30 := by
  intro x hx
  obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hx
  rfl

noncomputable def liveSig (C : Circuit) (w : ℕ) : Finset Vertex := by
  classical
  exact if Feeds 30 C w C.output then sig C w else ∅

theorem liveSig_eq (C : Circuit) {w : ℕ} (h : Feeds 30 C w C.output) :
    liveSig C w = sig C w := by classical simp [liveSig, h]

theorem silent_iff (C : Circuit) (w : ℕ) : silent C tests w ↔ sig C w = ∅ := by
  constructor
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have off := h (singleBank v) (List.mem_ofFn.mpr ⟨v,rfl⟩)
    exact Bool.noConfusion ((mem_sig.mp hv).symm.trans off)
  · intro h x hx
    obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hx
    by_contra! on
    have := mem_sig.mpr (show wire C (singleBank v) w = true by simpa [wire] using on)
    simp [h] at this

private theorem trans_path {C : Circuit} {n x y z : ℕ} (a : Feeds n C x y)
    (b : Feeds n C y z) : Feeds n C x z := by
  induction b with
  | refl => exact a
  | next _ hg hr ih => exact .next ih hg hr

theorem operand_live (C : Circuit) {j w : ℕ} (hj : j < C.size)
    (hw : w ∈ (gateAt C j).inputs) (hg : Feeds 30 C (30+j) C.output) :
    Feeds 30 C w C.output := trans_path (.next (.refl w) hj hw) hg

private theorem two_operands (l : List ℕ) (h : l.length = 2) : ∃ a b, l = [a,b] := by
  rcases l with _ | ⟨a, _ | ⟨b,t⟩⟩ <;> simp_all

theorem builds (C : Circuit) (shape : IsAO2 30 C) (clean : LiveClean C) (c : Vertex) :
    GridStarCount.BuildsWithin (liveSig C) (· ∈ rawGates 30 C tests) (neighbors c) (30+C.size) := by
  classical
  apply GridStarCount.builds_of_wire_cases
  intro w hw
  by_cases live : Feeds 30 C w C.output
  · by_cases input : w < 30
    · left
      rw [liveSig_eq C live, bank_sig C ⟨w,input⟩]
      intro sub
      exact (Finset.card_le_card (Finset.subset_inter (Finset.Subset.rfl) sub)).trans
        (bank_meets_star ⟨w,input⟩ c)
    · let j := w-30
      have hjw : 30+j = w := by dsimp [j]; omega
      have hj : j < C.size := by omega
      have gateMem : gateAt C j ∈ C.gates := by rw [gateAt_eq C j hj]; exact List.getElem_mem _
      have gateLive : Feeds 30 C (30+j) C.output := hjw ▸ live
      rcases shape.1 _ gateMem with isAnd | isOr
      · left
        rw [liveSig_eq C live, ← hjw, clean_and_sig C shape clean hj isAnd gateLive]
        simp
      · right
        obtain ⟨a,b,args⟩ := two_operands _ (shape.2.2 _ gateMem)
        have ha : a ∈ (gateAt C j).inputs := by simp [args]
        have hb : b ∈ (gateAt C j).inputs := by simp [args]
        have liveA := operand_live C hj ha gateLive
        have liveB := operand_live C hj hb gateLive
        have backA : a < w := hjw ▸ shape.2.1 j hj a ha
        have backB : b < w := hjw ▸ shape.2.1 j hj b hb
        have join : sig C w = sig C a ∪ sig C b := hjw ▸ or_sig C shape hj isOr args
        refine ⟨a, backA, b, backB, ?_, ?_⟩
        · rw [liveSig_eq C live, liveSig_eq C liveA, liveSig_eq C liveB, join]
        · rw [liveSig_eq C liveA, liveSig_eq C liveB]
          intro activeA activeB
          apply (mem_rawGates_iff 30 C tests w).mpr
          refine ⟨(mem_liveGates_iff 30 C w).mpr ⟨?_, live⟩, ?_, ?_⟩
          · exact Finset.mem_Ico.mpr ⟨by omega, hw⟩
          · rw [silent_iff, join]
            simp [activeA]
          · intro u hu
            rw [← hjw, inputsAt_gate, args] at hu
            simp only [List.toFinset_cons, List.toFinset_nil, Finset.mem_insert,
              Finset.notMem_empty, or_false] at hu
            rw [silent_iff]
            rcases hu with rfl | rfl <;> assumption
  · left
    simp [liveSig, live]

end GridLiveBuild

/-! The fourteen diagnostic tests alone force every singleton input to be
rejected. This suffices for the step that covers the 24 positive pairs by
productive AND gates. -/
namespace GridFewTests

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open GridCircuitSigs GridCleanWitness GridGeometry GridReplay

def RejectsFourteen (C : Circuit) : Prop :=
  ∀ t ∈ GridPairCover.tests, C.eval (bank t.1 t.2) = false

theorem singleton_off (C : Circuit) (shape : IsAO2 30 C) (rejects : RejectsFourteen C)
    (v : Vertex) : C.eval (singleBank v) = false := by
  have dominated : ∀ v : Vertex, ∃ t ∈ GridPairCover.tests, ∀ k : Fin 30,
      (singleBank v).getD k.val false = true → (bank t.1 t.2).getD k.val false = true := by
    decide +kernel
  obtain ⟨t, ht, mask⟩ := dominated v
  by_contra! on
  have hit := PEqualNP.Outside.L_meta_8029.wire_mono C (fun g hg =>
    ⟨by simpa using shape.1 g hg, le_of_eq (shape.2.2 g hg)⟩)
    (singleBank v) (bank t.1 t.2) rfl (by
      intro k hk
      by_cases h : k < 30
      · exact mask ⟨k,h⟩ hk
      · have outside : (singleBank v).length ≤ k := by change 30 ≤ k; omega
        rw [List.getD_eq_default _ _ outside] at hk
        contradiction) C.output (show wire C (singleBank v) C.output = true by
      change C.eval (singleBank v) = true
      simpa using on)
  exact Bool.noConfusion (hit.symm.trans (rejects t ht))

theorem edge_covered (C : Circuit) (shape : IsAO2 30 C)
    (positive : Positive C) (rejects : RejectsFourteen C) {u v : Vertex} (edge : (u,v) ∈ edges) :
    ∃ j < C.size, ∃ a b, (gateAt C j).op = GateOp.and ∧ (gateAt C j).inputs = [a,b] ∧
      Feeds 30 C (30+j) C.output ∧
      ((u ∈ sig C a ∧ v ∈ sig C b) ∨ (v ∈ sig C a ∧ u ∈ sig C b)) := by
  have facts : ∀ u v : Vertex, directed u v = true →
      let p := Fin.ofNat 6 u.val
      let l := Fin.ofNat 11 (v.val-6)
      (GridReplay.rows.getD p.val 0).testBit l.val = true ∧
        singleBank u = bank (2^p.val) 0 ∧ singleBank v = bank 0 (2^l.val) := by decide +kernel
  obtain ⟨ok,hp,hl⟩ := facts u v ((Finset.mem_filter.mp edge).2)
  obtain ⟨j,hj,a,b,op,ins,path,split⟩ := grid_pair_witness C shape _ _ (positive _ _ ok)
    (hp ▸ singleton_off C shape rejects u) (hl ▸ singleton_off C shape rejects v)
  refine ⟨j,hj,a,b,op,ins,path,?_⟩
  simp only [mem_sig, hp, hl]
  rcases split with h | h
  · exact Or.inl ⟨h.1,h.2.2.2⟩
  · exact Or.inr ⟨h.2.2.2,h.1⟩

end GridFewTests

/-! When a wire is true but its downstream output is false, an AND along the
path receives a true operand and blocks it. A two-bit witness can be detected
on one of the 14 specified negative masks, including the supplied line ORs. -/
namespace GridFiltering

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_6973 (wires_gate value gateAt_eq)
open GridCleanWitness

theorem feeds_index_le (C : Circuit) (shape : IsAO2 30 C) {a b : ℕ}
    (path : Feeds 30 C a b) : a ≤ b := by
  induction path with
  | refl => rfl
  | next _ hj read ih => exact le_trans ih (shape.2.1 _ hj _ read).le

theorem blocking_and (C : Circuit) (shape : IsAO2 30 C) (x : List Bool) (hlen : x.length = 30)
    {src dst : ℕ} (path : Feeds 30 C src dst)
    (on : wire C x src = true) (off : wire C x dst = false) :
    ∃ j < C.size, ∃ u ∈ (gateAt C j).inputs, (gateAt C j).op = GateOp.and ∧
      Feeds 30 C src u ∧ Feeds 30 C (30+j) dst ∧
      wire C x u = true ∧ wire C x (30+j) = false := by
  induction path with
  | refl => rw [on] at off; contradiction
  | @next w g hpath hj hr ih =>
    cases hv : wire C x w with
    | false =>
      obtain ⟨i, hi, u, hu, andGate, p, q, enabled, blocked⟩ := ih hv
      exact ⟨i, hi, u, hu, andGate, p, Feeds.next q hj hr, enabled, blocked⟩
    | true =>
      have mem : gateAt C g ∈ C.gates := by rw [gateAt_eq C g hj]; exact List.getElem_mem _
      rcases shape.1 _ mem with isAnd | isOr
      · exact ⟨g,hj,w,hr,isAnd,hpath,Feeds.refl _,hv,off⟩
      · have yes : wire C x (30+g) = true := by
          unfold wire
          rw [wires_gate 30 C shape.2.1 x hlen g hj]
          simp only [value, isOr, GateOp.eval, List.any_map, Function.comp_apply, id_eq,
            List.any_eq_true]
          exact ⟨w, hr, hv⟩
        rw [yes] at off
        contradiction

open GridPairCover (points lines tests negative)
open GridReplay (bank)

private theorem test_mask_dominates :
    ∀ i j : Fin 17, i ≠ j → negative (points i j) (lines i j) →
      ∃ t ∈ tests, ∀ k : Fin 30, (pairBank i j).getD k.val false = true →
        (bank t.1 t.2).getD k.val false = true := by
  decide +kernel

theorem detected (C : Circuit) (shape : IsAO2 30 C) {w : ℕ} {i j : Fin 17}
    (distinct : i ≠ j) (legal : negative (points i j) (lines i j))
    (fires : wire C (pairBank i j) w = true) :
    ∃ t ∈ tests, wire C (bank t.1 t.2) w = true := by
  obtain ⟨t, ht, reach⟩ := test_mask_dominates i j distinct legal
  refine ⟨t, ht, PEqualNP.Outside.L_meta_8029.wire_mono C ?_ (pairBank i j)
    (bank t.1 t.2) rfl ?_ w fires⟩
  · intro g hg; exact ⟨by simpa using shape.1 g hg, le_of_eq (shape.2.2 g hg)⟩
  · intro k hk
    by_cases h : k < 30
    · exact reach ⟨k,h⟩ hk
    · have out : (pairBank i j).length ≤ k := by change 30 ≤ k; omega
      rw [List.getD_eq_default _ _ out] at hk
      contradiction

end GridFiltering

/-! A restricted size bound for the 28-gate grid. A clean circuit is one in
which every AND feeding the output is off on every legal two-bit negative.
No restriction is placed on sharing, nesting, or dead gates. -/
namespace GridLowerBound

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open GridGeometry (edges Vertex Adj)
open GridCircuitSigs GridCleanWitness GridConeCount GridLiveBuild

private def arg (C : Circuit) (slot w : ℕ) : ℕ := (gateAt C (w-30)).inputs.getD slot 0

private theorem args_at {C : Circuit} {j a b : ℕ} (args : (gateAt C j).inputs = [a,b]) :
    arg C 0 (30+j) = a ∧ arg C 1 (30+j) = b := by simp [arg, args]

private theorem cone_operands (C : Circuit) {j a b : ℕ} (hj : j < C.size)
    (args : (gateAt C j).inputs = [a,b]) (live : Feeds 30 C (30+j) C.output) :
    liveSig C a = sig C a ∧ liveSig C b = sig C b := by
  constructor
  · exact liveSig_eq C (operand_live C hj (by simp [args] : a ∈ (gateAt C j).inputs) live)
  · exact liveSig_eq C (operand_live C hj (by simp [args] : b ∈ (gateAt C j).inputs) live)

/-- A source gate in the output cone has two nonempty operand signatures,
and every physical pair across the two signatures is incident. -/
private theorem source_rectangle (C : Circuit) (shape : IsAO2 30 C) (clean : LiveClean C)
    {w : ℕ} (member : w ∈ sourceGates 30 C tests) :
    (arg C 0 w < 30+C.size ∧ arg C 1 w < 30+C.size) ∧
    ((liveSig C (arg C 0 w)).Nonempty ∧ (liveSig C (arg C 1 w)).Nonempty) ∧
    (∀ x ∈ liveSig C (arg C 0 w), ∀ y ∈ liveSig C (arg C 1 w), Adj x y = true) := by
  obtain ⟨hm, empty, inputsOn⟩ := (mem_sourceGates_iff ..).mp member
  obtain ⟨real, path⟩ := (mem_liveGates_iff ..).mp hm
  obtain ⟨lo, hi⟩ := Finset.mem_Ico.mp real
  let j := w - 30
  have index : w = 30+j := by dsimp [j]; omega
  have hj : j < C.size := by change j < C.gates.length; dsimp [j]; omega
  rw [index] at empty inputsOn path ⊢
  have mem : gateAt C j ∈ C.gates := by
    rw [PEqualNP.Outside.L_meta_6973.gateAt_eq C j hj]
    exact List.getElem_mem _
  have arity := shape.2.2 _ mem
  have two (xs : List ℕ) (h : xs.length = 2) : ∃ a b, xs = [a,b] := by
    match xs, h with
    | [a,b], _ => exact ⟨a,b,rfl⟩
  obtain ⟨a,b,args⟩ := two _ arity
  obtain ⟨la,lb⟩ := args_at args
  obtain ⟨sa,sb⟩ := cone_operands C hj args path
  rw [la, lb, sa, sb]
  have ma : a ∈ (gateAt C j).inputs := by simp [args]
  have mb : b ∈ (gateAt C j).inputs := by simp [args]
  have active (u : ℕ) (hu : u ∈ (gateAt C j).inputs) : (sig C u).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    exact fun eq => inputsOn u (by simpa only [inputsAt_gate, List.mem_toFinset] using hu)
      ((silent_iff C u).mpr eq)
  have back (u) (hu : u ∈ (gateAt C j).inputs) : u < 30+C.size :=
    (shape.2.1 j hj u hu).trans (by omega)
  refine ⟨⟨back _ ma,back _ mb⟩, ⟨active _ ma,active _ mb⟩, ?_⟩
  rcases shape.1 _ mem with ha | ho
  · exact fun _ hx _ hy => clean_and_adj C shape clean hj ha args path hx hy
  · have eq := (silent_iff C _).mp empty
    rw [or_sig C shape hj ho args, Finset.union_eq_empty] at eq
    exact False.elim ((active a ma).ne_empty eq.1)

private theorem rectangle_cover (C : Circuit) (shape : IsAO2 30 C) (positive : Positive C)
    (rejects : GridFewTests.RejectsFourteen C) (clean : LiveClean C) :
    ∀ e ∈ edges, ∃ w ∈ sourceGates 30 C tests,
      (e.1 ∈ liveSig C (arg C 0 w) ∧ e.2 ∈ liveSig C (arg C 1 w)) ∨
      (e.2 ∈ liveSig C (arg C 0 w) ∧ e.1 ∈ liveSig C (arg C 1 w)) := by
  rintro ⟨x,y⟩ edge
  obtain ⟨j, hj, a, b, isAnd, args, path, hx⟩ := GridFewTests.edge_covered C shape positive rejects edge
  obtain ⟨sa,sb⟩ := cone_operands C hj args path
  obtain ⟨la,lb⟩ := args_at args
  have active : (sig C a).Nonempty ∧ (sig C b).Nonempty := by
    rcases hx with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact ⟨⟨_,h1⟩, ⟨_,h2⟩⟩
    · exact ⟨⟨_,h1⟩, ⟨_,h2⟩⟩
  refine ⟨30+j, (mem_sourceGates_iff ..).mpr ⟨(mem_liveGates_iff ..).mpr ⟨?_,path⟩,
    (silent_iff C _).mpr (clean_and_sig C shape clean hj isAnd path), ?_⟩, ?_⟩
  · apply Finset.mem_Ico.mpr
    change 30 ≤ 30+j ∧ 30+j < 30+C.size
    omega
  · intro u hu
    simp only [inputsAt_gate, List.mem_toFinset, args, List.mem_cons,
      List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · exact fun h => active.1.ne_empty ((silent_iff C _).mp h)
    · exact fun h => active.2.ne_empty ((silent_iff C _).mp h)
  · simpa only [la,lb,sa,sb] using hx

/-- Every passing circuit with clean ANDs in its output cone costs at least 29 gates. -/
theorem clean_size (C : Circuit) (shape : IsAO2 30 C) (positive : Positive C)
    (rejects : GridFewTests.RejectsFourteen C) (clean : LiveClean C) : 29 ≤ C.size := by
  have bounds := GridCoverCount.rectangle_counts (liveSig C) (sourceGates 30 C tests)
    (rawGates 30 C tests) (arg C 0) (arg C 1) (30+C.size) (builds C shape clean)
    (fun _ h => (source_rectangle C shape clean h).1)
    (fun _ h => (source_rectangle C shape clean h).2.1)
    (fun _ h => (source_rectangle C shape clean h).2.2)
    (rectangle_cover C shape positive rejects clean)
  have merge := source_le_other_succ C 30 shape tests tests_length
  have total := class_cards_le_size 30 C tests
  omega

/-- A solution within budget must use an AND that is active on a forbidden
two-bit input, and that AND must be on a path to the output. -/
theorem dirty_pair (C : Circuit) (shape : IsAO2 30 C) (positive : Positive C)
    (rejects : GridFewTests.RejectsFourteen C) (small : C.size ≤ 28) :
    ∃ j < C.size, (gateAt C j).op = GateOp.and ∧ Feeds 30 C (30+j) C.output ∧
      ∃ u v : Vertex, u ≠ v ∧ GridPairCover.negative (GridPairCover.points u v)
        (GridPairCover.lines u v) ∧ wire C (pairBank u v) (30+j) = true := by
  by_contra! absent
  have clean : LiveClean C := by
    intro j hj op path u v ne legal
    simpa using absent j hj op path u v ne legal
  have := clean_size C shape positive rejects clean
  omega

/-- The active AND can also be detected on one of the listed fourteen negative
tests. On that very test, a later AND feeding the output blocks a true operand. -/
theorem required_filter (C : Circuit) (shape : IsAO2 30 C) (positive : Positive C)
    (rejects : GridFewTests.RejectsFourteen C) (small : C.size ≤ 28) :
    ∃ t ∈ GridPairCover.tests, ∃ j < C.size, (gateAt C j).op = GateOp.and ∧
      Feeds 30 C (30+j) C.output ∧ wire C (GridReplay.bank t.1 t.2) (30+j) = true ∧
      ∃ k < C.size, j < k ∧ ∃ u ∈ (gateAt C k).inputs, (gateAt C k).op = GateOp.and ∧
        Feeds 30 C (30+j) u ∧ Feeds 30 C (30+k) C.output ∧
        wire C (GridReplay.bank t.1 t.2) u = true ∧
        wire C (GridReplay.bank t.1 t.2) (30+k) = false := by
  obtain ⟨j,hj,op,path,i,v,ne,legal,onPair⟩ := dirty_pair C shape positive rejects small
  obtain ⟨t,ht,onTest⟩ := GridFiltering.detected C shape ne legal onPair
  obtain ⟨k,hk,u,read,gate,prior,next,onU,offK⟩ := GridFiltering.blocking_and C shape _ rfl path
    onTest (rejects t ht)
  have le := GridFiltering.feeds_index_le C shape prior
  have lt := shape.2.1 k hk u read
  exact ⟨t,ht,j,hj,op,path,onTest,k,hk,by omega,u,read,gate,prior,next,onU,offK⟩

end GridLowerBound

/-! Check the thirty-port grid specification against the *type* of the merged
reduction. The twenty-nine-gate control has no AND firing on a negative input. -/
namespace GridSharp

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_6973 (wires_gate value)
open GridCleanWitness GridCircuitSigs GridReplay
open Lean Elab Term

/-- Read the grid hypothesis itself from the imported reduction. The type
checker checks the following comparison against its actual binder domain. -/
elab "upstreamGridHypothesis" : term => do
  let info ← getConstInfo ``PEqualNP.Outside.R_meta_4893_629
  match info.type with
  | .forallE _ domain _ _ => pure domain
  | _ => throwError "Expected a universally quantified reduction"

def PostedGrid : Prop := upstreamGridHypothesis

/-- The published statement uses four successive negative-test premises.
This grouped version has exactly the same proof obligations. -/
theorem source_binding : PostedGrid ↔ ∃ C : Circuit, IsAO2 30 C ∧ C.size = 28 ∧ C.output = 57 ∧
    Positive C ∧ Negative C := by
  change (∃ C : Circuit, IsAO2 30 C ∧ C.size = 28 ∧ C.output = 57 ∧ Positive C ∧
    ∀ p w : ℕ, p &&& 7 ≠ 7 → p &&& 56 ≠ 56 →
      (∀ q ∈ rows ++ ports, ((List.range 11).filter (w &&& q).testBit).length ≤ 2) →
      disjoint p w → C.eval (bank p w) = false) ↔ _
  constructor
  · rintro ⟨C,h,s,o,pos,neg⟩
    exact ⟨C,h,s,o,pos,fun p w hn => neg p w hn.1 hn.2.1 hn.2.2.1 hn.2.2.2⟩
  · rintro ⟨C,h,s,o,pos,neg⟩
    exact ⟨C,h,s,o,pos,fun p w h1 h2 h3 h4 => neg p w ⟨h1,h2,h3,h4⟩⟩

attribute [local instance] gateOpDecEq

private theorem off_at_or {x : List Bool} (hx : x.length = 30) {j a b : ℕ}
    (hj : j < control.size) (hop : (gateAt control j).op = GateOp.or)
    (args : (gateAt control j).inputs = [a,b]) (off : wire control x (30+j) = false) :
    wire control x a = false ∧ wire control x b = false := by
  unfold wire at *
  rw [wires_gate 30 control control_shape.1.2.1 x hx j hj] at off
  simpa only [value,hop,args,List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,
    id,Bool.or_false,Bool.or_eq_false_iff] using off

/-- For this circuit every AND feeds the output through ORs alone. Therefore
each is off on every input rejected by the output. This includes all legal
negatives, beyond the two-bit inputs in the cleanliness definition. -/
theorem control_and_off {x : List Bool} (hx : x.length = 30) (off : control.eval x = false)
    {j : ℕ} (hj : j < control.size) (isAnd : (gateAt control j).op = GateOp.and) :
    wire control x (30+j) = false := by
  have h58 := off_at_or hx (j := 28) (a := 57) (b := 53) (by decide) rfl rfl off
  have h57 := off_at_or hx (j := 27) (a := 56) (b := 49) (by decide) rfl rfl h58.1
  have h56 := off_at_or hx (j := 26) (a := 55) (b := 45) (by decide) rfl rfl h57.1
  have h55 := off_at_or hx (j := 25) (a := 54) (b := 41) (by decide) rfl rfl h56.1
  have h54 := off_at_or hx (j := 24) (a := 33) (b := 37) (by decide) rfl rfl h55.1
  have idx : ∀ k : Fin 29, (gateAt control k.val).op = GateOp.and →
      k.val = 3 ∨ k.val = 7 ∨ k.val = 11 ∨ k.val = 15 ∨ k.val = 19 ∨ k.val = 23 := by
    decide +kernel
  rcases idx ⟨j,hj⟩ isAnd with h | h | h | h | h | h <;>
    change j = _ at h <;> subst j
  · exact h54.1
  · exact h54.2
  · exact h55.2
  · exact h56.2
  · exact h57.2
  · exact h58.2

/-- The explicit 29-gate control is a clean circuit for the exact grid tests. -/
theorem clean_control : IsAO2 30 control ∧ control.size = 29 ∧ control.output = 58 ∧
    Positive control ∧ Negative control ∧ LiveClean control := by
  refine ⟨control_shape.1,control_shape.2.1,control_shape.2.2,?_,?_,?_⟩
  · intro p l edge
    exact (control_positive p l).trans edge
  · intro p l neg
    exact control_negative p l neg.2.2.2
  · intro j hj op _ i t _ forbidden
    exact control_and_off rfl (control_negative _ _ forbidden.2.2.2) hj op

end GridSharp

namespace GridResult

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open GridCleanWitness GridCircuitSigs

private theorem rejects_fourteen {C : Circuit} (negative : Negative C) :
    GridFewTests.RejectsFourteen C :=
  fun t ht => negative _ _ (GridPairCover.admissible.2 t ht)

/-- Among all circuits passing the grid specification whose output-relevant ANDs
are off on every legal two-bit negative input, 29 gates are necessary and sufficient. -/
theorem exact_clean_minimum :
    IsLeast {n : ℕ | ∃ C : Circuit, IsAO2 30 C ∧ C.size = n ∧
      Positive C ∧ Negative C ∧ LiveClean C} 29 := by
  obtain ⟨shape, size, _, pos, neg, clean⟩ := GridSharp.clean_control
  constructor
  · exact ⟨GridReplay.control, shape, size, pos, neg, clean⟩
  · rintro n ⟨C, hc, rfl, p, q, h⟩
    exact GridLowerBound.clean_size C hc p (rejects_fourteen q) h

/-- Applied to the exact hypothesis of the published reduction, a witness
must show internal activation and later suppression on one of the 14 tests. -/
theorem posted_witness_requires_filter (posted : GridSharp.PostedGrid) :
    ∃ C : Circuit, IsAO2 30 C ∧ C.size = 28 ∧ C.output = 57 ∧
      Positive C ∧ Negative C ∧
      ∃ t ∈ GridPairCover.tests, ∃ j < C.size, (gateAt C j).op = GateOp.and ∧
        Feeds 30 C (30+j) C.output ∧ wire C (GridReplay.bank t.1 t.2) (30+j) = true ∧
        ∃ k < C.size, j < k ∧ ∃ u ∈ (gateAt C k).inputs, (gateAt C k).op = GateOp.and ∧
          Feeds 30 C (30+j) u ∧ Feeds 30 C (30+k) C.output ∧
          wire C (GridReplay.bank t.1 t.2) u = true ∧
          wire C (GridReplay.bank t.1 t.2) (30+k) = false := by
  obtain ⟨C,shape,size,output,pos,neg⟩ := GridSharp.source_binding.mp posted
  exact ⟨C,shape,size,output,pos,neg,GridLowerBound.required_filter C shape pos
    (rejects_fourteen neg) size.le⟩

end GridResult

#print axioms GridSharp.source_binding
#print axioms GridResult.exact_clean_minimum
#print axioms GridLowerBound.required_filter
#print axioms GridResult.posted_witness_requires_filter


/-! Size bounds when internal ANDs may fire on forbidden pairs from one side of
the point-line graph. The input bank, tests, and circuit semantics come from
the earlier clean-AND bound. -/

namespace GridSideWitness

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open GridGeometry GridCleanWitness GridCircuitSigs GridConeCount GridLiveBuild
open GridPairCover (points lines)

def side (pointsFirst : Bool) (v : Vertex) : Bool :=
  if pointsFirst then decide (v.val < 6) else decide (6 ≤ v.val)

/-- An AND may misfire on pairs containing no vertex from the selected side. -/
def CleanOn (s : Bool) (C : Circuit) : Prop :=
  ∀ j < C.size, (gateAt C j).op = GateOp.and → Feeds 30 C (30+j) C.output →
    ∀ u v : Vertex, (side s u || side s v) = true → u ≠ v →
      GridPairCover.negative (points u v) (lines u v) →
      wire C (pairBank u v) (30+j) = false

def keep (s : Bool) (A : Finset Vertex) :=
  if (A.filter fun v => side s v).Nonempty then A.filter (fun v => side s v) else A

private theorem keep_zero (s : Bool) : keep s ∅ = ∅ := by simp [keep]

private theorem combine (s : Bool) (A B : Finset Vertex) :
    keep s (A ∪ B) = keep s A ∨ keep s (A ∪ B) = keep s B ∨
    keep s (A ∪ B) = keep s A ∪ keep s B := by
  simp only [keep, Finset.filter_union, Finset.union_nonempty]
  split_ifs <;> simp_all [Finset.not_nonempty_iff_eq_empty]

private theorem pure_bank (s : Bool) (i : Fin 30) : keep s (bankSupport i) = bankSupport i := by
  revert s i
  decide +kernel

private theorem and_silent (C : Circuit) (shape : IsAO2 30 C) {s : Bool} (h : CleanOn s C)
    {j : ℕ} (hj : j < C.size) (op : (gateAt C j).op = GateOp.and)
    (live : Feeds 30 C (30+j) C.output) : sig C (30+j) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  have geom : ∀ (s : Bool) (u : Vertex), ∃ v : Vertex, (side s u || side s v) = true ∧
      u ≠ v ∧ GridPairCover.negative (points u v) (lines u v) := by decide +kernel
  obtain ⟨v, hs, ne, neg⟩ := geom s u
  have on := singleton_preserved C shape u v _ (mem_sig.mp hu)
  rw [h j hj op live u v hs ne neg] at on
  contradiction

private theorem raw_pair (C : Circuit) (shape : IsAO2 30 C) {s : Bool} (h : CleanOn s C)
    {j a b : ℕ} (hj : j < C.size) (op : (gateAt C j).op = GateOp.and)
    (args : (gateAt C j).inputs = [a,b]) (live : Feeds 30 C (30+j) C.output)
    {u v : Vertex} (hu : u ∈ sig C a) (hv : v ∈ sig C b) :
    Adj u v = true ∨ (side s u = false ∧ side s v = false) := by
  by_cases hs : (side s u || side s v) = true
  · left
    have geom : ∀ u v : Vertex, ¬ GridPairCover.negative (points u v) (lines u v) →
        Adj u v = true := by decide +kernel
    by_cases eq : u = v
    · subst v
      have on := pair_fires C shape hj op args u u (mem_sig.mp hu) (mem_sig.mp hv)
      have diag : ∀ u : Vertex, pairBank u u = singleBank u := by decide +kernel
      rw [diag] at on
      have mem := mem_sig.mpr on
      simp [and_silent C shape h hj op live] at mem
    · apply geom
      intro neg
      have on := pair_fires C shape hj op args u v (mem_sig.mp hu) (mem_sig.mp hv)
      rw [h j hj op live u v hs eq neg] at on
      contradiction
  · right
    simpa using hs

private theorem projected_edge (s : Bool) (A B : Finset Vertex)
    (pairs : ∀ x ∈ A, ∀ y ∈ B, Adj x y = true ∨ (side s x = false ∧ side s y = false))
    {u v : Vertex} (hu : u ∈ A) (hv : v ∈ B) (adj : Adj u v = true) :
    u ∈ keep s A ∧ v ∈ keep s B ∧ ∀ x ∈ keep s A, ∀ y ∈ keep s B, Adj x y = true := by
  have diff : ∀ (s : Bool) (x y : Vertex), Adj x y = true → side s x ≠ side s y := by decide +kernel
  have uv := diff s u v adj
  by_cases su : side s u = true
  · have sv : side s v = false := by cases e : side s v <;> simp_all
    have noB : B.filter (fun v => side s v) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro y hy
      obtain ⟨hyB, hyS⟩ := Finset.mem_filter.mp hy
      rcases pairs u hu y hyB with e | e
      · exact diff s u y e (su.trans hyS.symm)
      · simp_all
    have hasA : (A.filter fun v => side s v).Nonempty := ⟨u,Finset.mem_filter.mpr ⟨hu,su⟩⟩
    simp only [keep, hasA, noB, Finset.not_nonempty_empty, ite_true, ite_false]
    refine ⟨Finset.mem_filter.mpr ⟨hu,su⟩,hv,?_⟩
    intro x hx y hy
    obtain ⟨ha,hs⟩ := Finset.mem_filter.mp hx
    rcases pairs x ha y hy with e | e <;> simp_all
  · have sv : side s v = true := by cases e : side s v <;> simp_all
    have noA : A.filter (fun v => side s v) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨hxA, hxS⟩ := Finset.mem_filter.mp hx
      rcases pairs x hxA v hv with e | e
      · exact diff s x v e (hxS.trans sv.symm)
      · simp_all
    have hasB : (B.filter fun v => side s v).Nonempty := ⟨v,Finset.mem_filter.mpr ⟨hv,sv⟩⟩
    simp only [keep, hasB, noA, Finset.not_nonempty_empty, ite_true, ite_false]
    refine ⟨hu,Finset.mem_filter.mpr ⟨hv,sv⟩,?_⟩
    intro x hx y hy
    obtain ⟨hb,hs⟩ := Finset.mem_filter.mp hy
    rcases pairs x hx y hb with e | e <;> simp_all

noncomputable def key (s : Bool) (C : Circuit) (w : ℕ) := keep s (liveSig C w)

private theorem builds_keys (s : Bool) (C : Circuit) (shape : IsAO2 30 C) (h : CleanOn s C)
    (c : Vertex) : GridStarCount.BuildsWithin (key s C) (· ∈ rawGates 30 C tests)
      (neighbors c) (30+C.size) := by
  classical
  intro w time fit large
  by_cases live : Feeds 30 C w C.output
  · by_cases input : w < 30
    · rw [key, liveSig_eq C live, bank_sig C ⟨w,input⟩, pure_bank] at fit large
      have small := (Finset.card_le_card (Finset.subset_inter (Finset.Subset.rfl) fit)).trans
        (bank_meets_star ⟨w,input⟩ c)
      omega
    · let j := w-30
      have index : 30+j = w := by dsimp [j]; omega
      have hj : j < C.size := by omega
      have gateMem : gateAt C j ∈ C.gates := by
        rw [PEqualNP.Outside.L_meta_6973.gateAt_eq C j hj]; exact List.getElem_mem _
      have liveG : Feeds 30 C (30+j) C.output := index ▸ live
      rcases shape.1 _ gateMem with op | op
      · rw [key, liveSig_eq C live, ← index, and_silent C shape h hj op liveG, keep_zero] at large
        simp at large
      · have two (l : List ℕ) (arity : l.length = 2) : ∃ a b, l = [a,b] := by
          match l, arity with | [a,b], _ => exact ⟨a,b,rfl⟩
        obtain ⟨a,b,args⟩ := two _ (shape.2.2 _ gateMem)
        have ha : a ∈ (gateAt C j).inputs := by simp [args]
        have hb : b ∈ (gateAt C j).inputs := by simp [args]
        have la := operand_live C hj ha liveG
        have lb := operand_live C hj hb liveG
        have ta : a < w := index ▸ shape.2.1 j hj a ha
        have tb : b < w := index ▸ shape.2.1 j hj b hb
        have join : sig C w = sig C a ∪ sig C b := index ▸ or_sig C shape hj op args
        have eqs := combine s (sig C a) (sig C b)
        rw [← join, ← liveSig_eq C live, ← liveSig_eq C la, ← liveSig_eq C lb] at eqs
        change key s C w = key s C a ∨ key s C w = key s C b ∨
          key s C w = key s C a ∪ key s C b at eqs
        rcases eqs with ca | cb | both
        · exact .inl ⟨a,ta,ca⟩
        · exact .inl ⟨b,tb,cb⟩
        · by_cases aa : sig C a = ∅
          · have k : key s C a = ∅ := by simp [key,liveSig_eq C la,aa,keep_zero]
            exact .inl ⟨b,tb,by simpa [k] using both⟩
          by_cases bb : sig C b = ∅
          · have k : key s C b = ∅ := by simp [key,liveSig_eq C lb,bb,keep_zero]
            exact .inl ⟨a,ta,by simpa [k] using both⟩
          refine .inr ⟨?_,a,ta,b,tb,both⟩
          apply (mem_rawGates_iff 30 C tests w).mpr
          refine ⟨(mem_liveGates_iff 30 C w).mpr ⟨Finset.mem_Ico.mpr ⟨by omega,time⟩,live⟩,?_,?_⟩
          · rw [silent_iff,join]; simp [aa]
          · intro v hv
            rw [← index, inputsAt_gate, args] at hv
            simp only [List.toFinset_cons, List.toFinset_nil, Finset.mem_insert,
              Finset.notMem_empty, or_false] at hv
            rw [silent_iff]
            rcases hv with rfl | rfl <;> assumption
  · simp [key,liveSig,live,keep_zero] at large

private def port (C : Circuit) (i w : ℕ) := (gateAt C (w-30)).inputs.getD i 0

private def valid (s : Bool) (C : Circuit) (w : ℕ) : Prop :=
  port C 0 w < 30+C.size ∧ port C 1 w < 30+C.size ∧
  (key s C (port C 0 w)).Nonempty ∧ (key s C (port C 1 w)).Nonempty ∧
  ∀ x ∈ key s C (port C 0 w), ∀ y ∈ key s C (port C 1 w), Adj x y = true

private noncomputable def stars (s : Bool) (C : Circuit) := by
  classical exact (sourceGates 30 C tests).filter (valid s C)

private theorem covered (s : Bool) (C : Circuit) (shape : IsAO2 30 C) (positive : Positive C)
    (rejects : GridFewTests.RejectsFourteen C) (h : CleanOn s C) :
    ∀ e ∈ edges, ∃ w ∈ stars s C,
      (e.1 ∈ key s C (port C 0 w) ∧ e.2 ∈ key s C (port C 1 w)) ∨
      (e.2 ∈ key s C (port C 0 w) ∧ e.1 ∈ key s C (port C 1 w)) := by
  classical
  rintro ⟨x,y⟩ edge
  have adj : Adj x y = true := by
    change (x,y) ∈ Finset.univ.filter _ at edge
    have := (Finset.mem_filter.mp edge).2
    simp [Adj,this]
  obtain ⟨j,hj,a,b,op,args,path,split⟩ := GridFewTests.edge_covered C shape positive rejects edge
  have aa : port C 0 (30+j) = a := by simp [port,args]
  have bb : port C 1 (30+j) = b := by simp [port,args]
  have ha : a ∈ (gateAt C j).inputs := by simp [args]
  have hb : b ∈ (gateAt C j).inputs := by simp [args]
  have la := operand_live C hj ha path
  have lb := operand_live C hj hb path
  have rawA : (sig C a).Nonempty := by rcases split with ⟨hx,hy⟩ | ⟨hy,hx⟩; exact ⟨x,hx⟩; exact ⟨y,hy⟩
  have rawB : (sig C b).Nonempty := by rcases split with ⟨hx,hy⟩ | ⟨hy,hx⟩; exact ⟨y,hy⟩; exact ⟨x,hx⟩
  have src : 30+j ∈ sourceGates 30 C tests := by
    apply (mem_sourceGates_iff ..).mpr
    refine ⟨(mem_liveGates_iff ..).mpr ⟨?_,path⟩,(silent_iff C _).mpr (and_silent C shape h hj op path),?_⟩
    · change 30+j ∈ Finset.Ico 30 (30+C.gates.length)
      exact Finset.mem_Ico.mpr ⟨by omega, by change j < C.gates.length at hj; omega⟩
    · intro u hu
      simp only [inputsAt_gate,List.mem_toFinset,args,List.mem_cons,List.not_mem_nil,or_false] at hu
      rw [silent_iff]
      rcases hu with rfl | rfl
      · exact rawA.ne_empty
      · exact rawB.ne_empty
  have rule (i k : Vertex) (ih : i ∈ sig C a) (kh : k ∈ sig C b) (ik : Adj i k = true) :=
    projected_edge s (sig C a) (sig C b)
      (fun z hz t ht => raw_pair C shape h hj op args path hz ht) ih kh ik
  have make (i k : Vertex) (ih : i ∈ sig C a) (kh : k ∈ sig C b) (ik : Adj i k = true) :
      30+j ∈ stars s C ∧ i ∈ key s C (port C 0 (30+j)) ∧ k ∈ key s C (port C 1 (30+j)) := by
    obtain ⟨left,right,rect⟩ := rule i k ih kh ik
    unfold stars
    rw [Finset.mem_filter]
    simp only [valid,aa,bb,key,liveSig_eq C la,liveSig_eq C lb]
    exact ⟨⟨src,(shape.2.1 j hj a ha).trans (by omega),(shape.2.1 j hj b hb).trans (by omega),
      ⟨i,left⟩,⟨k,right⟩,rect⟩,left,right⟩
  rcases split with ⟨left,right⟩ | ⟨left,right⟩
  · obtain ⟨mem,l,r⟩ := make x y left right adj
    exact ⟨_,mem,.inl ⟨l,r⟩⟩
  · obtain ⟨mem,l,r⟩ := make y x left right ((adj_comm y x).trans adj)
    exact ⟨_,mem,.inr ⟨l,r⟩⟩

/-- The 29-gate lower bound permits arbitrary internal errors on two-line
pairs, or arbitrary internal errors on two-point pairs, chosen uniformly. -/
theorem one_side_size (C : Circuit) (shape : IsAO2 30 C) (pos : Positive C)
    (neg : GridFewTests.RejectsFourteen C) (s : Bool) (h : CleanOn s C) : 29 ≤ C.size := by
  classical
  have prop (w : ℕ) (hw : w ∈ stars s C) : valid s C w := (Finset.mem_filter.mp hw).2
  have counts := GridCoverCount.rectangle_counts (key s C) (stars s C) (rawGates 30 C tests)
    (port C 0) (port C 1) (30+C.size) (builds_keys s C shape h)
    (fun w hw => ⟨(prop w hw).1,(prop w hw).2.1⟩)
    (fun w hw => ⟨(prop w hw).2.2.1,(prop w hw).2.2.2.1⟩)
    (fun w hw => (prop w hw).2.2.2.2)
    (covered s C shape pos neg h)
  have sub : (stars s C).card ≤ (sourceGates 30 C tests).card := Finset.card_le_card (Finset.filter_subset ..)
  have merge := source_le_other_succ C 30 shape tests tests_length
  have total := class_cards_le_size 30 C tests
  omega

/-- A live AND gate activates on this legal negative pair of physical bits. -/
def Fires (C : Circuit) (u v : Vertex) : Prop := u ≠ v ∧
    GridPairCover.negative (points u v) (lines u v) ∧
    ∃ j < C.size, (gateAt C j).op = GateOp.and ∧ Feeds 30 C (30+j) C.output ∧
      wire C (pairBank u v) (30+j) = true

/-- Either a point and a line witness an internal error, or both a two-point
input and a two-line input do. The two internal errors may use different ANDs. -/
def WitnessKinds (C : Circuit) : Prop :=
  (∃ u v : Vertex, Fires C u v ∧ side true u ≠ side true v) ∨
  ((∃ u v : Vertex, Fires C u v ∧ side true u = true ∧ side true v = true) ∧
   (∃ u v : Vertex, Fires C u v ∧ side true u = false ∧ side true v = false))

theorem kinds_required (C : Circuit) (shape : IsAO2 30 C) (pos : Positive C)
    (neg : GridFewTests.RejectsFourteen C) (small : C.size ≤ 28) : WitnessKinds C := by
  classical
  have existsOn (s : Bool) : ∃ u v, Fires C u v ∧ (side s u || side s v) = true := by
    by_contra missing
    have clean : CleanOn s C := by
      intro j hj op path u v sideHit ne bad
      by_contra! on
      exact missing ⟨u,v,⟨ne,bad,j,hj,op,path,by simpa using on⟩,sideHit⟩
    have := one_side_size C shape pos neg s clean
    omega
  obtain ⟨u,v,point,one⟩ := existsOn true
  obtain ⟨a,b,line,two⟩ := existsOn false
  by_cases uv : side true u = side true v
  · by_cases ab : side true a = side true b
    · right
      have flip : ∀ v : Vertex, side false v = !side true v := by decide +kernel
      rw [uv,Bool.or_self] at one
      rw [flip,flip,ab,Bool.or_self,Bool.not_eq_true'] at two
      exact ⟨⟨u,v,point,uv.trans one,one⟩,⟨a,b,line,ab.trans two,two⟩⟩
    · exact .inl ⟨a,b,line,ab⟩
  · exact .inl ⟨u,v,point,uv⟩

theorem fires_is_filtered (C : Circuit) (shape : IsAO2 30 C) (neg : Negative C)
    {u v : Vertex} (f : Fires C u v) :
    ∃ j < C.size, ∃ k < C.size, j < k ∧ (gateAt C j).op = GateOp.and ∧
      (gateAt C k).op = GateOp.and ∧ wire C (pairBank u v) (30+j) = true ∧
      ∃ t ∈ (gateAt C k).inputs, Feeds 30 C (30+j) t ∧ Feeds 30 C (30+k) C.output ∧
        wire C (pairBank u v) t = true ∧ wire C (pairBank u v) (30+k) = false := by
  obtain ⟨_,bad,j,hj,op,path,on⟩ := f
  have off : wire C (pairBank u v) C.output = false := neg _ _ bad
  obtain ⟨k,hk,t,read,opK,fromJ,toOut,yes,no⟩ := GridFiltering.blocking_and C shape _ rfl path on off
  have late := GridFiltering.feeds_index_le C shape fromJ
  have early := shape.2.1 k hk t read
  exact ⟨j,hj,k,hk,by omega,op,opK,on,t,read,fromJ,toOut,yes,no⟩

theorem exact_one_side_minimum (s : Bool) :
    IsLeast {n : ℕ | ∃ C : Circuit, IsAO2 30 C ∧ C.size = n ∧
      Positive C ∧ Negative C ∧ CleanOn s C} 29 := by
  obtain ⟨shape,size,_,pos,neg,clean⟩ := GridSharp.clean_control
  constructor
  · exact ⟨GridReplay.control,shape,size,pos,neg,fun j hj op path u v _ ne bad =>
      clean j hj op path u v ne bad⟩
  · rintro n ⟨C,shape,rfl,pos,neg,h⟩
    exact one_side_size C shape pos (fun t ht => neg _ _ (GridPairCover.admissible.2 t ht)) s h

theorem posted_kinds (posted : GridSharp.PostedGrid) :
    ∃ C : Circuit, IsAO2 30 C ∧ C.size = 28 ∧ C.output = 57 ∧
      Positive C ∧ Negative C ∧ WitnessKinds C := by
  obtain ⟨C,shape,size,out,pos,neg⟩ := GridSharp.source_binding.mp posted
  exact ⟨C,shape,size,out,pos,neg,kinds_required C shape pos
    (fun t ht => neg _ _ (GridPairCover.admissible.2 t ht)) size.le⟩

end GridSideWitness

#print axioms GridSideWitness.one_side_size
#print axioms GridSideWitness.posted_kinds
#print axioms GridSideWitness.fires_is_filtered
#print axioms GridSideWitness.exact_one_side_minimum

namespace GridPublishedRepair
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open GridCleanWitness GridCircuitSigs GridGeometry
open GridPairCover (points lines)
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
local instance (op : GateOp) : Decidable (op = GateOp.and) := by
  cases op <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)

/-- The published 28-gate layout with wire 43 changed to OR(16,32). -/
def circuit : Circuit := ⟨[
  ⟨.or, [13, 6]⟩,
  ⟨.or, [8, 10]⟩,
  ⟨.or, [15, 6]⟩,
  ⟨.or, [6, 9]⟩,
  ⟨.or, [15, 9]⟩,
  ⟨.or, [33, 31]⟩,
  ⟨.or, [12, 34]⟩,
  ⟨.or, [36, 7]⟩,
  ⟨.and, [4, 37]⟩,
  ⟨.and, [0, 35]⟩,
  ⟨.or, [7, 14]⟩,
  ⟨.or, [30, 12]⟩,
  ⟨.or, [13, 16]⟩,
  ⟨.or, [16, 32]⟩,
  ⟨.or, [14, 43]⟩,
  ⟨.or, [10, 42]⟩,
  ⟨.or, [40, 8]⟩,
  ⟨.or, [7, 45]⟩,
  ⟨.or, [11, 41]⟩,
  ⟨.and, [3, 46]⟩,
  ⟨.and, [2, 44]⟩,
  ⟨.or, [39, 50]⟩,
  ⟨.and, [1, 48]⟩,
  ⟨.or, [52, 49]⟩,
  ⟨.and, [47, 5]⟩,
  ⟨.or, [54, 51]⟩,
  ⟨.or, [55, 38]⟩,
  ⟨.or, [56, 53]⟩
  ], 57⟩

theorem shape : IsAO2 30 circuit ∧ circuit.size = 28 ∧ circuit.output = 57 := by decide +kernel

theorem singleton_outputs : ∀ (p : Fin 6) (l : Fin 11),
    circuit.eval (GridReplay.bank (2^p.val) (2^l.val)) =
      ((GridReplay.rows.getD p.val 0).testBit l.val && !(p.val == 3 && l.val == 5)) := by
  decide +kernel

theorem clean : LiveClean circuit := by
  have off : ∀ (u v : Vertex), u ≠ v → GridPairCover.negative (points u v) (lines u v) →
      ∀ j : Fin 28, (gateAt circuit j.val).op = GateOp.and →
        wire circuit (pairBank u v) (30+j.val) = false := by decide +kernel
  intro j hj op _ u v ne bad
  exact off u v ne bad ⟨j, hj⟩ op

end GridPublishedRepair

#print axioms GridPublishedRepair.clean
#print axioms GridPublishedRepair.singleton_outputs
