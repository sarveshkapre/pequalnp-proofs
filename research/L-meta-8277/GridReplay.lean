import PEqualNP.Defs

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
