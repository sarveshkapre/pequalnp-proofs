import PEqualNP.Defs

/-! A 28-gate near miss with a useful internal AND on a forbidden pair. -/
namespace GridMixed
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


def circuit : Circuit := ⟨[
  ⟨.or, [13,6]⟩,
  ⟨.or, [8,10]⟩,
  ⟨.or, [15,6]⟩,
  ⟨.or, [6,9]⟩,
  ⟨.or, [15,9]⟩,
  ⟨.or, [33,31]⟩,
  ⟨.or, [12,34]⟩,
  ⟨.or, [36,7]⟩,
  ⟨.and, [4,37]⟩,
  ⟨.and, [0,35]⟩,
  ⟨.or, [7,14]⟩,
  ⟨.or, [30,12]⟩,
  ⟨.or, [13,16]⟩,
  ⟨.and, [30,32]⟩,
  ⟨.or, [14,43]⟩,
  ⟨.or, [10,42]⟩,
  ⟨.or, [40,8]⟩,
  ⟨.or, [7,45]⟩,
  ⟨.or, [11,41]⟩,
  ⟨.and, [3,46]⟩,
  ⟨.and, [2,44]⟩,
  ⟨.or, [39,50]⟩,
  ⟨.and, [1,48]⟩,
  ⟨.or, [52,49]⟩,
  ⟨.and, [47,5]⟩,
  ⟨.or, [54,51]⟩,
  ⟨.or, [55,38]⟩,
  ⟨.or, [56,53]⟩
  ], 57⟩
theorem shape : IsAO2 30 circuit ∧ circuit.size = 28 ∧ circuit.output = 57 := by decide +kernel

private def formula (p w : ℕ) : Bool := (pairOr (pairOr (pairOr (pairAnd (pairOr (w.testBit 1) (pairOr (w.testBit 4) (pairOr (w.testBit 7) (w.testBit 10)))) (p.testBit 5)) (pairOr (pairAnd (p.testBit 0) (pairOr (pairOr (w.testBit 0) (w.testBit 3)) (pairOr (w.testBit 2) (w.testBit 4)))) (pairAnd (p.testBit 2) (pairOr (w.testBit 8) (pairAnd (pairOr (w.testBit 7) (w.testBit 0)) (pairOr (w.testBit 9) (w.testBit 0))))))) (pairAnd (p.testBit 4) (pairOr (pairOr (w.testBit 6) (pairOr (w.testBit 9) (w.testBit 3))) (w.testBit 1)))) (pairOr (pairAnd (p.testBit 1) (pairOr (w.testBit 5) (pairOr (pairOr (w.testBit 7) (w.testBit 0)) (w.testBit 6)))) (pairAnd (p.testBit 3) (pairOr (pairOr (w.testBit 1) (w.testBit 8)) (w.testBit 2)))))

private theorem symbols (p w : ℕ) : circuit.eval (bank p w) = formula p w ∧
    (circuit.wires (bank p w)).getD 43 false = (pairAnd (pairOr (w.testBit 7) (w.testBit 0)) (pairOr (w.testBit 9) (w.testBit 0))) ∧
    (circuit.wires (bank p w)).getD 50 false = (pairAnd (p.testBit 2) (pairOr (w.testBit 8) (pairAnd (pairOr (w.testBit 7) (w.testBit 0)) (pairOr (w.testBit 9) (w.testBit 0))))) := by
  let inputs : List Bool := [p.testBit 0, p.testBit 1, p.testBit 2, p.testBit 3, p.testBit 4, p.testBit 5, w.testBit 0, w.testBit 1, w.testBit 2, w.testBit 3, w.testBit 4, w.testBit 5, w.testBit 6, w.testBit 7, w.testBit 8, w.testBit 9, w.testBit 10, decide (w &&& 3 ≠ 0), decide (w &&& 40 ≠ 0), decide (w &&& 1064 ≠ 0), decide (w &&& 272 ≠ 0), decide (w &&& 336 ≠ 0), decide (w &&& 516 ≠ 0), decide (w &&& 644 ≠ 0), decide (w &&& 48 ≠ 0), decide (w &&& 560 ≠ 0), decide (w &&& 264 ≠ 0), decide (w &&& 392 ≠ 0), decide (w &&& 68 ≠ 0), decide (w &&& 1092 ≠ 0)]
  have input_eq : bank p w = inputs := rfl
  let v30 := GateOp.or.eval [(w.testBit 7), (w.testBit 0)]
  let v31 := GateOp.or.eval [(w.testBit 2), (w.testBit 4)]
  let v32 := GateOp.or.eval [(w.testBit 9), (w.testBit 0)]
  let v33 := GateOp.or.eval [(w.testBit 0), (w.testBit 3)]
  let v34 := GateOp.or.eval [(w.testBit 9), (w.testBit 3)]
  let v35 := GateOp.or.eval [v33, v31]
  let v36 := GateOp.or.eval [(w.testBit 6), v34]
  let v37 := GateOp.or.eval [v36, (w.testBit 1)]
  let v38 := GateOp.and.eval [(p.testBit 4), v37]
  let v39 := GateOp.and.eval [(p.testBit 0), v35]
  let v40 := GateOp.or.eval [(w.testBit 1), (w.testBit 8)]
  let v41 := GateOp.or.eval [v30, (w.testBit 6)]
  let v42 := GateOp.or.eval [(w.testBit 7), (w.testBit 10)]
  let v43 := GateOp.and.eval [v30, v32]
  let v44 := GateOp.or.eval [(w.testBit 8), v43]
  let v45 := GateOp.or.eval [(w.testBit 4), v42]
  let v46 := GateOp.or.eval [v40, (w.testBit 2)]
  let v47 := GateOp.or.eval [(w.testBit 1), v45]
  let v48 := GateOp.or.eval [(w.testBit 5), v41]
  let v49 := GateOp.and.eval [(p.testBit 3), v46]
  let v50 := GateOp.and.eval [(p.testBit 2), v44]
  let v51 := GateOp.or.eval [v39, v50]
  let v52 := GateOp.and.eval [(p.testBit 1), v48]
  let v53 := GateOp.or.eval [v52, v49]
  let v54 := GateOp.and.eval [v47, (p.testBit 5)]
  let v55 := GateOp.or.eval [v54, v51]
  let v56 := GateOp.or.eval [v55, v38]
  let v57 := GateOp.or.eval [v56, v53]
  let full := inputs ++ [v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57]
  have good : Good full 30 circuit.gates := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
  have hw : circuit.wires (bank p w) = full := by
    rw [input_eq]; exact replay full 30 circuit.gates (Nat.le_refl 58) good
  unfold Circuit.eval
  rw [hw]
  exact ⟨rfl,rfl,rfl⟩

theorem singleton_pairs : ∀ i : Fin 6, ∀ j : Fin 11,
    circuit.eval (bank (2^i.val) (2^j.val)) = ((rows.getD i.val 0).testBit j.val &&
      !(i.val == 2 && (j.val == 9 || j.val == 10) || i.val == 3 && j.val == 5)) := by
  have table : ∀ i : Fin 6, ∀ j : Fin 11,
      formula (2^i.val) (2^j.val) = ((rows.getD i.val 0).testBit j.val &&
      !(i.val == 2 && (j.val == 9 || j.val == 10) || i.val == 3 && j.val == 5)) := by decide +kernel
  intro i j
  rw [(symbols _ _).1]
  exact table i j

theorem disjoint_inputs (p w : ℕ) (h : disjoint p w) : circuit.eval (bank p w) = false := by
  rw [(symbols _ _).1]
  have term54 : (pairAnd (pairOr (w.testBit 1) (pairOr (w.testBit 4) (pairOr (w.testBit 7) (w.testBit 10)))) (p.testBit 5)) = false := by
    cases hp : p.testBit 5 with
    | false => simp [and_eq]
    | true =>
      have c1 : w.testBit 1 = false := clear p w h ⟨5,by decide⟩ 1 hp (by decide)
      have c4 : w.testBit 4 = false := clear p w h ⟨5,by decide⟩ 4 hp (by decide)
      have c7 : w.testBit 7 = false := clear p w h ⟨5,by decide⟩ 7 hp (by decide)
      have c10 : w.testBit 10 = false := clear p w h ⟨5,by decide⟩ 10 hp (by decide)
      simp [and_eq, or_eq, c1, c4, c7, c10]
  have term39 : (pairAnd (p.testBit 0) (pairOr (pairOr (w.testBit 0) (w.testBit 3)) (pairOr (w.testBit 2) (w.testBit 4)))) = false := by
    cases hp : p.testBit 0 with
    | false => simp [and_eq]
    | true =>
      have c0 : w.testBit 0 = false := clear p w h ⟨0,by decide⟩ 0 hp (by decide)
      have c2 : w.testBit 2 = false := clear p w h ⟨0,by decide⟩ 2 hp (by decide)
      have c3 : w.testBit 3 = false := clear p w h ⟨0,by decide⟩ 3 hp (by decide)
      have c4 : w.testBit 4 = false := clear p w h ⟨0,by decide⟩ 4 hp (by decide)
      simp [and_eq, or_eq, c0, c2, c3, c4]
  have term50 : (pairAnd (p.testBit 2) (pairOr (w.testBit 8) (pairAnd (pairOr (w.testBit 7) (w.testBit 0)) (pairOr (w.testBit 9) (w.testBit 0))))) = false := by
    cases hp : p.testBit 2 with
    | false => simp [and_eq]
    | true =>
      have c0 : w.testBit 0 = false := clear p w h ⟨2,by decide⟩ 0 hp (by decide)
      have c8 : w.testBit 8 = false := clear p w h ⟨2,by decide⟩ 8 hp (by decide)
      have c9 : w.testBit 9 = false := clear p w h ⟨2,by decide⟩ 9 hp (by decide)
      simp [and_eq, or_eq, c0, c8, c9]
  have term38 : (pairAnd (p.testBit 4) (pairOr (pairOr (w.testBit 6) (pairOr (w.testBit 9) (w.testBit 3))) (w.testBit 1))) = false := by
    cases hp : p.testBit 4 with
    | false => simp [and_eq]
    | true =>
      have c1 : w.testBit 1 = false := clear p w h ⟨4,by decide⟩ 1 hp (by decide)
      have c3 : w.testBit 3 = false := clear p w h ⟨4,by decide⟩ 3 hp (by decide)
      have c6 : w.testBit 6 = false := clear p w h ⟨4,by decide⟩ 6 hp (by decide)
      have c9 : w.testBit 9 = false := clear p w h ⟨4,by decide⟩ 9 hp (by decide)
      simp [and_eq, or_eq, c1, c3, c6, c9]
  have term52 : (pairAnd (p.testBit 1) (pairOr (w.testBit 5) (pairOr (pairOr (w.testBit 7) (w.testBit 0)) (w.testBit 6)))) = false := by
    cases hp : p.testBit 1 with
    | false => simp [and_eq]
    | true =>
      have c0 : w.testBit 0 = false := clear p w h ⟨1,by decide⟩ 0 hp (by decide)
      have c5 : w.testBit 5 = false := clear p w h ⟨1,by decide⟩ 5 hp (by decide)
      have c6 : w.testBit 6 = false := clear p w h ⟨1,by decide⟩ 6 hp (by decide)
      have c7 : w.testBit 7 = false := clear p w h ⟨1,by decide⟩ 7 hp (by decide)
      simp [and_eq, or_eq, c0, c5, c6, c7]
  have term49 : (pairAnd (p.testBit 3) (pairOr (pairOr (w.testBit 1) (w.testBit 8)) (w.testBit 2))) = false := by
    cases hp : p.testBit 3 with
    | false => simp [and_eq]
    | true =>
      have c1 : w.testBit 1 = false := clear p w h ⟨3,by decide⟩ 1 hp (by decide)
      have c2 : w.testBit 2 = false := clear p w h ⟨3,by decide⟩ 2 hp (by decide)
      have c8 : w.testBit 8 = false := clear p w h ⟨3,by decide⟩ 8 hp (by decide)
      simp [and_eq, or_eq, c1, c2, c8]
  unfold formula
  rw [term54, term39, term50, term38, term52, term49]; rfl

theorem suppressed : (circuit.wires (bank 8 1)).getD 43 false = true ∧
    (circuit.wires (bank 8 1)).getD 50 false = false ∧ circuit.eval (bank 8 1) = false := by
  rw [(symbols _ _).2.1, (symbols _ _).2.2, (symbols _ _).1]
  decide +kernel
end GridMixed
