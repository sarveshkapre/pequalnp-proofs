import PEqualNP.Outside.L_meta_2420

/-!
# Partial result for L-meta-2216

The public step asks whether a two-output monotone circuit with at most 61 gates exists.
This file supplies a 62-gate construction and proves its optimality when both designated
wires have line-degree at most one. See `PuncturedPlane.exact_linear_minimum` at the end.
The unrestricted nonexistence statement remains open in this file.

The argument uses the upstream full-plane lower bound `PEqualNP.Outside.L_meta_2420`.
The two-gate reattachment follows the idea in upstream `R_meta_650_517` and `L_meta_2217`,
with the line labels reversed here to match the lower bound's coordinate convention.
Tested on upstream commit e6bfe1a56efc768d244627b78f175b18de1acd6f, Lean 4.36.0.
-/

/-! A boundary construction for L-meta-2216. The assigned nonexistence question at 61 gates is open here. -/
namespace PuncturedPlane
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

def incident (p l : Fin 25) : Prop :=
  p.val < 12 ∧ 12 ≤ l.val ∧ (p.val + l.val + 2) % 13 ∈ ([0, 1, 3, 9] : List ℕ)

def rows : List (Fin 25 × List (Fin 25)) :=
  [(0, [12, 14, 20, 24]),
    (1, [13, 19, 23, 24]),
    (2, [12, 18, 22, 23]),
    (3, [17, 21, 22, 24]),
    (4, [16, 20, 21, 23]),
    (5, [15, 19, 20, 22]),
    (6, [14, 18, 19, 21]),
    (7, [13, 17, 18, 20]),
    (8, [12, 16, 17, 19]),
    (9, [15, 16, 18, 24]),
    (10, [14, 15, 17, 23]),
    (11, [13, 14, 16, 22])]

def circuit : Circuit :=
  ⟨[⟨.or, [12, 14]⟩,
    ⟨.or, [25, 20]⟩,
    ⟨.or, [26, 24]⟩,
    ⟨.and, [0, 27]⟩,
    ⟨.or, [13, 19]⟩,
    ⟨.or, [29, 23]⟩,
    ⟨.or, [30, 24]⟩,
    ⟨.and, [1, 31]⟩,
    ⟨.or, [12, 18]⟩,
    ⟨.or, [33, 22]⟩,
    ⟨.or, [34, 23]⟩,
    ⟨.and, [2, 35]⟩,
    ⟨.or, [17, 21]⟩,
    ⟨.or, [37, 22]⟩,
    ⟨.or, [38, 24]⟩,
    ⟨.and, [3, 39]⟩,
    ⟨.or, [16, 20]⟩,
    ⟨.or, [41, 21]⟩,
    ⟨.or, [42, 23]⟩,
    ⟨.and, [4, 43]⟩,
    ⟨.or, [15, 19]⟩,
    ⟨.or, [45, 20]⟩,
    ⟨.or, [46, 22]⟩,
    ⟨.and, [5, 47]⟩,
    ⟨.or, [14, 18]⟩,
    ⟨.or, [49, 19]⟩,
    ⟨.or, [50, 21]⟩,
    ⟨.and, [6, 51]⟩,
    ⟨.or, [13, 17]⟩,
    ⟨.or, [53, 18]⟩,
    ⟨.or, [54, 20]⟩,
    ⟨.and, [7, 55]⟩,
    ⟨.or, [12, 16]⟩,
    ⟨.or, [57, 17]⟩,
    ⟨.or, [58, 19]⟩,
    ⟨.and, [8, 59]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.or, [61, 18]⟩,
    ⟨.or, [62, 24]⟩,
    ⟨.and, [9, 63]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.or, [65, 17]⟩,
    ⟨.or, [66, 23]⟩,
    ⟨.and, [10, 67]⟩,
    ⟨.or, [13, 14]⟩,
    ⟨.or, [69, 16]⟩,
    ⟨.or, [70, 22]⟩,
    ⟨.and, [11, 71]⟩,
    ⟨.or, [28, 32]⟩,
    ⟨.or, [73, 36]⟩,
    ⟨.or, [74, 40]⟩,
    ⟨.or, [75, 44]⟩,
    ⟨.or, [76, 48]⟩,
    ⟨.or, [77, 52]⟩,
    ⟨.or, [78, 56]⟩,
    ⟨.or, [79, 60]⟩,
    ⟨.or, [80, 64]⟩,
    ⟨.or, [81, 68]⟩,
    ⟨.or, [82, 72]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [84, 15]⟩,
    ⟨.or, [85, 21]⟩], 83⟩

def auxiliary : Nat := 86

theorem rows_correct (p l : Fin 25) :
    (∃ r ∈ rows, r.1 = p ∧ l ∈ r.2) ↔ incident p l := by
  have table : ∀ i j : Fin 25, rows.any (fun r => decide (r.1 = i ∧ j ∈ r.2)) =
      decide (i.val < 12 ∧ 12 ≤ j.val ∧ (i.val + j.val + 2) % 13 ∈ ([0,1,3,9] : List ℕ)) := by
    decide +kernel
  simpa only [List.any_eq_true, decide_eq_true_eq, incident] using
    (Bool.eq_iff_iff.mp (table p l))

def edgeOutput (x : Fin 25 → Bool) : Bool :=
  rows.any fun r => x r.1 && r.2.any x

theorem edgeOutput_correct (x : Fin 25 → Bool) :
    edgeOutput x = true ↔ ∃ p l, incident p l ∧ x p = true ∧ x l = true := by
  simp only [edgeOutput, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨r, hr, hp, l, hl, hxl⟩
    exact ⟨r.1, l, (rows_correct _ _).mp ⟨r, hr, rfl, hl⟩, hp, hxl⟩
  · rintro ⟨p, l, h, hp, hl⟩
    obtain ⟨r, hr, he, hmem⟩ := (rows_correct _ _).mpr h
    exact ⟨r, hr, he ▸ hp, l, hmem, hl⟩

theorem monotone : Monotone2 circuit := by
  intro g h
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp

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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
private theorem outputs (x : Fin 25 → Bool) :
    circuit.eval (List.ofFn x) = edgeOutput x ∧
    (circuit.wires (List.ofFn x)).getD auxiliary false = (x 12 || x 13 || x 15 || x 21) := by
  let inputs : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24]
  have input_eq : List.ofFn x = inputs := rfl
  let w25 := GateOp.or.eval [x 12, x 14]
  let w26 := GateOp.or.eval [w25, x 20]
  let w27 := GateOp.or.eval [w26, x 24]
  let w28 := GateOp.and.eval [x 0, w27]
  let w29 := GateOp.or.eval [x 13, x 19]
  let w30 := GateOp.or.eval [w29, x 23]
  let w31 := GateOp.or.eval [w30, x 24]
  let w32 := GateOp.and.eval [x 1, w31]
  let w33 := GateOp.or.eval [x 12, x 18]
  let w34 := GateOp.or.eval [w33, x 22]
  let w35 := GateOp.or.eval [w34, x 23]
  let w36 := GateOp.and.eval [x 2, w35]
  let w37 := GateOp.or.eval [x 17, x 21]
  let w38 := GateOp.or.eval [w37, x 22]
  let w39 := GateOp.or.eval [w38, x 24]
  let w40 := GateOp.and.eval [x 3, w39]
  let w41 := GateOp.or.eval [x 16, x 20]
  let w42 := GateOp.or.eval [w41, x 21]
  let w43 := GateOp.or.eval [w42, x 23]
  let w44 := GateOp.and.eval [x 4, w43]
  let w45 := GateOp.or.eval [x 15, x 19]
  let w46 := GateOp.or.eval [w45, x 20]
  let w47 := GateOp.or.eval [w46, x 22]
  let w48 := GateOp.and.eval [x 5, w47]
  let w49 := GateOp.or.eval [x 14, x 18]
  let w50 := GateOp.or.eval [w49, x 19]
  let w51 := GateOp.or.eval [w50, x 21]
  let w52 := GateOp.and.eval [x 6, w51]
  let w53 := GateOp.or.eval [x 13, x 17]
  let w54 := GateOp.or.eval [w53, x 18]
  let w55 := GateOp.or.eval [w54, x 20]
  let w56 := GateOp.and.eval [x 7, w55]
  let w57 := GateOp.or.eval [x 12, x 16]
  let w58 := GateOp.or.eval [w57, x 17]
  let w59 := GateOp.or.eval [w58, x 19]
  let w60 := GateOp.and.eval [x 8, w59]
  let w61 := GateOp.or.eval [x 15, x 16]
  let w62 := GateOp.or.eval [w61, x 18]
  let w63 := GateOp.or.eval [w62, x 24]
  let w64 := GateOp.and.eval [x 9, w63]
  let w65 := GateOp.or.eval [x 14, x 15]
  let w66 := GateOp.or.eval [w65, x 17]
  let w67 := GateOp.or.eval [w66, x 23]
  let w68 := GateOp.and.eval [x 10, w67]
  let w69 := GateOp.or.eval [x 13, x 14]
  let w70 := GateOp.or.eval [w69, x 16]
  let w71 := GateOp.or.eval [w70, x 22]
  let w72 := GateOp.and.eval [x 11, w71]
  let w73 := GateOp.or.eval [w28, w32]
  let w74 := GateOp.or.eval [w73, w36]
  let w75 := GateOp.or.eval [w74, w40]
  let w76 := GateOp.or.eval [w75, w44]
  let w77 := GateOp.or.eval [w76, w48]
  let w78 := GateOp.or.eval [w77, w52]
  let w79 := GateOp.or.eval [w78, w56]
  let w80 := GateOp.or.eval [w79, w60]
  let w81 := GateOp.or.eval [w80, w64]
  let w82 := GateOp.or.eval [w81, w68]
  let w83 := GateOp.or.eval [w82, w72]
  let w84 := GateOp.or.eval [x 12, x 13]
  let w85 := GateOp.or.eval [w84, x 15]
  let w86 := GateOp.or.eval [w85, x 21]
  let values : List Bool := [w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63, w64, w65, w66, w67, w68, w69, w70, w71, w72, w73, w74, w75, w76, w77, w78, w79, w80, w81, w82, w83, w84, w85, w86]
  let full := inputs ++ values
  have h : Good full 25 circuit.gates := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
  have hw : circuit.wires (List.ofFn x) = full := by
    rw [input_eq]; exact replay full 25 circuit.gates (Nat.le_refl 87) h
  unfold Circuit.eval
  rw [hw]
  change w83 = edgeOutput x ∧ w86 = _
  simp only [w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63, w64, w65, w66, w67, w68, w69, w70, w71, w72, w73, w74, w75, w76, w77, w78, w79, w80, w81, w82, w83, w84, w85, w86, GateOp.eval, rows, edgeOutput, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.and_true, Bool.or_assoc, and_self, eq_self]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 1200000 in
theorem boundary_degrees :
    circuit.lineDeg 25 (Finset.Ico 12 25) = 1 ∧
    (circuit.lineDegrees 25 (Finset.Ico 12 25)).getD auxiliary 0 = 1 := by
  decide +kernel

theorem boundary :
    circuit.size = 62 ∧ Monotone2 circuit ∧ circuit.output < 25 + circuit.size ∧
    auxiliary < 25 + circuit.size ∧ ∀ x : Fin 25 → Bool,
      (circuit.eval (List.ofFn x) = true ↔ ∃ p l, incident p l ∧ x p = true ∧ x l = true) ∧
      (circuit.eval (List.ofFn x) = false →
        (circuit.wires (List.ofFn x)).getD auxiliary false = (x 12 || x 13 || x 15 || x 21)) := by
  refine ⟨rfl, monotone, by decide, by decide, ?_⟩
  intro x
  exact ⟨(outputs x).1 ▸ edgeOutput_correct x, fun _ => (outputs x).2⟩

end PuncturedPlane

/-! A restricted lower bound for L-meta-2216, using the project's full-plane theorem L-meta-2420. -/
namespace PuncturedLineBound
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Reinsert point zero and reverse the line labels so incidence reads p = l + d. -/
def embed (i : Fin 25) : Fin 26 :=
  if i.val < 12 then ⟨i.val+1, by omega⟩
  else ⟨13 + (13 - (i.val - 12)) % 13, by omega⟩

def relabel (i : ℕ) : ℕ := if h : i < 25 then (embed ⟨i,h⟩).val else i+1

def relGate (g : Gate) : Gate := ⟨g.op, g.inputs.map relabel⟩

def extend (C : Circuit) (tap : ℕ) : Circuit :=
  ⟨C.gates.map relGate ++
      [⟨.and, [0, relabel tap]⟩, ⟨.or, [relabel C.output, 26 + C.size]⟩],
    26 + C.size + 1⟩

private def step (alg : GateOp → List α → α) (z : α) (w : List α) (g : Gate) : List α :=
  w ++ [alg g.op (g.inputs.map fun i => w.getD i z)]

private theorem read {a b : List α} (ha : a.length = 25) (hb : b.length = 26)
    (z : α) (base : ∀ i : Fin 25, b.getD (embed i).val z = a.getD i.val z)
    (t : List α) (k : ℕ) :
    (b ++ t).getD (relabel k) z = (a ++ t).getD k z := by
  by_cases h : k < 25
  · simp only [relabel, dite_eq_left h]
    rw [List.getD_append _ _ _ _ (by rw [hb]; exact (embed ⟨k,h⟩).isLt),
      List.getD_append _ _ _ _ (by omega)]
    exact base ⟨k,h⟩
  · simp only [relabel, dite_eq_right h]
    rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
    congr 1; omega

private theorem simulate (alg : GateOp → List α → α) (z : α) (a b : List α)
    (ha : a.length = 25) (hb : b.length = 26)
    (base : ∀ i : Fin 25, b.getD (embed i).val z = a.getD i.val z)
    (gs : List Gate) (s : List α) :
    ∃ t : List α, t.length = s.length + gs.length ∧
      gs.foldl (step alg z) (a ++ s) = a ++ t ∧
      (gs.map relGate).foldl (step alg z) (b ++ s) = b ++ t := by
  induction gs generalizing s with
  | nil => exact ⟨s, by simp, rfl, rfl⟩
  | cons g gs ih =>
    let v := alg g.op (g.inputs.map fun i => (a ++ s).getD i z)
    have h : (g.inputs.map relabel).map (fun i => (b ++ s).getD i z) =
        g.inputs.map (fun i => (a ++ s).getD i z) := by
      simp only [List.map_map, Function.comp_def, read ha hb z base]
    obtain ⟨t, ht, h1, h2⟩ := ih (s ++ [v])
    refine ⟨t, by simp at ht ⊢; omega, ?_, ?_⟩
    · simpa only [List.foldl_cons, step, List.append_assoc, v] using h1
    · simp only [List.map_cons, List.foldl_cons, step, relGate, h, List.append_assoc]
      exact h2

attribute [local instance] lineDegreeGateOpDecEq
private def deg (op : GateOp) (v : List ℕ) : ℕ :=
  if op = .and then v.sum else v.foldr max 0

private def d25 : List ℕ := (List.range 25).map fun i => if i ∈ Finset.Ico 12 25 then 1 else 0
private def d26 : List ℕ := (List.range 26).map fun i => if i ∈ Finset.Ico 13 26 then 1 else 0

private lemma deg_base : ∀ i : Fin 25, d26.getD (embed i).val 0 = d25.getD i.val 0 := by decide

private lemma relabel_lt {i k : ℕ} (hi : i < 25 + k) : relabel i < 26 + k := by
  unfold relabel
  split
  · rename_i h
    exact Nat.lt_of_lt_of_le (embed ⟨i,h⟩).isLt (by omega)
  · omega

private theorem aux_bounds (C : Circuit) (tap : ℕ) (ho : C.output < 25+C.size)
    (h1 : C.lineDeg 25 (Finset.Ico 12 25) ≤ 1)
    (h2 : (C.lineDegrees 25 (Finset.Ico 12 25)).getD tap 0 ≤ 1) :
    HasLineDegree 26 (Finset.Ico 13 26) (extend C tap) 1 := by
  obtain ⟨t, ht, hs, hb⟩ := simulate deg 0 d25 d26 (by decide) (by decide) deg_base C.gates []
  simp only [List.append_nil, List.length_nil, Nat.zero_add] at hs hb ht
  change (C.gates.foldl (step deg 0) d25).getD C.output 0 ≤ 1 at h1
  change (C.gates.foldl (step deg 0) d25).getD tap 0 ≤ 1 at h2
  rw [hs] at h1 h2
  let w := d26 ++ t
  have hw : w.length = 26 + C.size := by simp [w, d26, ht, Circuit.size]
  have hz : w.getD 0 0 = 0 := List.getD_append _ _ _ _ (by decide)
  have hmain := read (a := d25) (b := d26) (by decide) (by decide) 0 deg_base t C.output
  have haux := read (a := d25) (b := d26) (by decide) (by decide) 0 deg_base t tap
  change w.getD _ 0 = _ at hmain haux
  change (((C.gates.map relGate ++ _).foldl (step deg 0) d26).getD (26+C.size+1) 0) ≤ 1
  rw [List.foldl_append, hb]
  change (step deg 0 (step deg 0 w ⟨.and, [0, relabel tap]⟩)
    ⟨.or, [relabel C.output, 26+C.size]⟩).getD (26+C.size+1) 0 ≤ 1
  have land : step deg 0 w ⟨.and, [0, relabel tap]⟩ = w ++ [w.getD (relabel tap) 0] := by
    simp [step, deg, hz, -List.getD_eq_getElem?_getD]
  rw [land]
  have mainWire : (w ++ [w.getD (relabel tap) 0]).getD (relabel C.output) 0 = w.getD (relabel C.output) 0 :=
    List.getD_append _ _ _ _ (hw ▸ relabel_lt ho)
  have newWire : (w ++ [w.getD (relabel tap) 0]).getD (26+C.size) 0 = w.getD (relabel tap) 0 := by
    rw [← hw]; simp
  let v := w.getD (relabel tap) 0
  let u := w.getD (relabel C.output) 0
  have lor : step deg 0 (w ++ [v]) ⟨.or, [relabel C.output, 26+C.size]⟩ =
      (w ++ [v]) ++ [max u v] := by
    simp [step, deg, mainWire, newWire, u, v, -List.getD_eq_getElem?_getD]
  rw [lor]
  have length2 : (w ++ [v]).length = 26+C.size+1 := by simp [hw]
  rw [← length2]
  have hm : max u v ≤ 1 := max_le (by change w.getD _ 0 ≤ 1; rwa [hmain]) (by change w.getD _ 0 ≤ 1; rwa [haux])
  simpa using hm

private lemma extension_mono {C : Circuit} {tap : ℕ} (hC : Monotone2 C) :
    Monotone2 (extend C tap) := by
  intro g hg
  simp only [extend, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with ⟨g', h, rfl⟩ | rfl | rfl
  · simpa [relGate] using hC g' h
  · simp
  · simp

private theorem eval_extension (C : Circuit) (tap : ℕ) (ho : C.output < 25+C.size)
    (x : Fin 26 → Bool) :
    (extend C tap).eval (List.ofFn x) =
      (C.eval (List.ofFn (x ∘ embed)) ||
        (x 0 && (C.wires (List.ofFn (x ∘ embed))).getD tap false)) := by
  let a := List.ofFn (x ∘ embed)
  let b := List.ofFn x
  have base (i : Fin 25) : b.getD (embed i).val false = a.getD i.val false := by
    change (List.ofFn x).getD (embed i).val false = (List.ofFn (x ∘ embed)).getD i.val false
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using (embed i).isLt),
      List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt)]
    simp only [List.getElem_ofFn, Function.comp_apply]
  have ha : a.length = 25 := by simp [a]
  have hb : b.length = 26 := by simp [b]
  obtain ⟨t, ht, hs, hn⟩ := simulate GateOp.eval false a b ha hb base C.gates []
  simp only [List.append_nil, List.length_nil, Nat.zero_add] at hs hn ht
  let w := b ++ t
  have hw : w.length = 26+C.size := by simp [w, hb, ht, Circuit.size]
  have hz : w.getD 0 false = x 0 := by
    rw [show w = b ++ t from rfl, List.getD_append _ _ _ _ (by omega)]
    simp [b]
  have hmain := read ha hb false base t C.output
  have haux := read ha hb false base t tap
  change w.getD _ false = _ at hmain haux
  change (((C.gates.map relGate ++ _).foldl (step GateOp.eval false) b).getD (26+C.size+1) false) = _
  rw [List.foldl_append, hn]
  have old : C.wires a = a ++ t := hs
  change (step GateOp.eval false (step GateOp.eval false w ⟨.and, [0, relabel tap]⟩)
    ⟨.or, [relabel C.output, 26+C.size]⟩).getD (26+C.size+1) false =
      ((C.wires a).getD C.output false || (x 0 && (C.wires a).getD tap false))
  rw [old]
  let v := x 0 && w.getD (relabel tap) false
  have hand : step GateOp.eval false w ⟨.and, [0, relabel tap]⟩ = w ++ [v] := by
    simp [step, GateOp.eval, hz, v, -List.getD_eq_getElem?_getD]
  have mainWire := List.getD_append w [v] false (relabel C.output) (hw ▸ relabel_lt ho)
  have newWire : (w ++ [v]).getD (26+C.size) false = v := by rw [← hw]; simp
  have hor : step GateOp.eval false (w ++ [v]) ⟨.or, [relabel C.output, 26+C.size]⟩ =
      (w ++ [v]) ++ [w.getD (relabel C.output) false || v] := by
    simp [step, GateOp.eval, mainWire, newWire, -List.getD_eq_getElem?_getD]
  rw [hand, hor, show 26+C.size+1 = (w ++ [v]).length by simp [hw]]
  simpa [v, hmain, haux, -List.getD_eq_getElem?_getD] using
    (show ((w ++ [v]) ++ [w.getD (relabel C.output) false || v]).getD (w ++ [v]).length false =
      (w.getD (relabel C.output) false || v) by simp)

abbrev Inc (i j : Fin 25) : Prop :=
  i.val < 12 ∧ 12 ≤ j.val ∧ (i.val + j.val + 2) % 13 ∈ ([0,1,3,9] : List ℕ)

abbrev Plane (p l : Fin 13) := ∃ d ∈ ({0,1,3,9} : Finset (Fin 13)), p = l+d

private def pt (i : Fin 25) : Fin 13 := Fin.ofNat 13 (i.val+1)
private def ln (j : Fin 25) : Fin 13 := Fin.ofNat 13 (13 - (j.val-12))
private def oldPt (p : Fin 13) : Fin 25 := ⟨p.val-1, by omega⟩
private def oldLn (l : Fin 13) : Fin 25 := ⟨12 + (13-l.val)%13, by omega⟩

private lemma keep : ∀ i j : Fin 25, Inc i j →
    Plane (pt i) (ln j) ∧ Fin.castAdd 13 (pt i) = embed i ∧
    Fin.natAdd 13 (ln j) = embed j := by decide +kernel

private lemma back : ∀ p l : Fin 13, p ≠ 0 → Plane p l →
    Inc (oldPt p) (oldLn l) ∧ embed (oldPt p) = Fin.castAdd 13 p ∧
    embed (oldLn l) = Fin.natAdd 13 l := by decide +kernel

private lemma deleted : ∀ j ∈ ([12,13,15,21] : List (Fin 25)),
    Plane 0 (ln j) ∧ Fin.natAdd 13 (ln j) = embed j := by
  decide +kernel

private lemma deletedBack : ∀ l : Fin 13, Plane 0 l →
    oldLn l ∈ ([12,13,15,21] : List (Fin 25)) ∧ embed (oldLn l) = Fin.natAdd 13 l := by
  decide +kernel

abbrev CorrectAt (C : Circuit) (tap : ℕ) (y : Fin 25 → Bool) : Prop :=
  (C.eval (List.ofFn y) = true ↔ ∃ i j, Inc i j ∧ y i = true ∧ y j = true) ∧
  (C.eval (List.ofFn y) = false → (C.wires (List.ofFn y)).getD tap false =
    (y 12 || y 13 || y 15 || y 21))

abbrev Computes (C : Circuit) (tap : ℕ) := ∀ y, CorrectAt C tap y

private theorem extended_at {C : Circuit} {tap : ℕ} (ho : C.output < 25+C.size)
    (x : Fin 26 → Bool) (hc : CorrectAt C tap (x ∘ embed)) :
    (extend C tap).eval (List.ofFn x) = true ↔
      ∃ p l, Plane p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
  let y := x ∘ embed
  let N := y 12 || y 13 || y 15 || y 21
  let H := C.eval (List.ofFn y)
  have att : N = true ↔ ∃ j ∈ ([12,13,15,21] : List (Fin 25)), y j = true := by
    simp [N, or_assoc]
  have graph : (H = true ∨ (x 0 = true ∧ N = true)) ↔
      ∃ p l, Plane p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
    constructor
    · rintro (h | ⟨hp,hl⟩)
      · obtain ⟨i,j,hi,hp,hl⟩ := hc.1.mp h
        obtain ⟨hpl, a, b⟩ := keep i j hi
        exact ⟨pt i,ln j,hpl,a ▸ hp,b ▸ hl⟩
      · obtain ⟨j,hj,hx⟩ := att.mp hl
        obtain ⟨hpl, b⟩ := deleted j hj
        exact ⟨0,ln j,hpl,hp,b ▸ hx⟩
    · rintro ⟨p,l,hpl,hp,hl⟩
      by_cases h0 : p = 0
      · subst p
        obtain ⟨hj, hb⟩ := deletedBack l hpl
        exact Or.inr ⟨hp,att.mpr ⟨oldLn l,hj,by change x (embed _) = true; rwa [hb]⟩⟩
      · obtain ⟨hi,a,b⟩ := back p l h0 hpl
        exact Or.inl (hc.1.mpr ⟨_,_,hi,by change x (embed _) = true; rwa [a],by change x (embed _) = true; rwa [b]⟩)
  rw [← graph, eval_extension C tap ho]
  change (H || (x 0 && (C.wires (List.ofFn y)).getD tap false)) = true ↔ _
  cases h : H with
  | true => simp
  | false =>
    have ht := hc.2 h
    change (C.wires (List.ofFn y)).getD tap false = N at ht
    rw [ht]; simp

/-- The finite test domain allows any point inputs and at most one active line input. -/
def oneLine (y : Fin 25 → Bool) : Prop :=
  ∀ i j : Fin 25, 12 ≤ i.val → 12 ≤ j.val → y i = true → y j = true → i = j

private lemma line_label : ∀ j : Fin 25, 12 ≤ j.val → Fin.natAdd 13 (ln j) = embed j := by
  decide +kernel

private lemma embed_inj : Function.Injective embed := by
  unfold Function.Injective
  decide +kernel

/-- The bound already holds on inputs with at most one active line. -/
theorem slice_bound (C : Circuit) (tap : ℕ) (hm : Monotone2 C)
    (ho : C.output < 25+C.size) (hc : ∀ y, oneLine y → CorrectAt C tap y)
    (hd : C.lineDeg 25 (Finset.Ico 12 25) ≤ 1)
    (ht : (C.lineDegrees 25 (Finset.Ico 12 25)).getD tap 0 ≤ 1) : 62 ≤ C.size := by
  apply Nat.le_of_add_le_add_right (b := 2)
  have h := PEqualNP.Outside.L_meta_2420 (extend C tap) (extension_mono hm)
    (aux_bounds C tap ho hd ht) (fun x hx => extended_at ho x (hc (x ∘ embed) (by
      obtain ⟨l, unique⟩ := hx
      intro i j hi hj hxi hxj
      have ei := line_label i hi
      have ej := line_label j hj
      apply embed_inj
      rw [← ei, ← ej]
      exact congrArg (Fin.natAdd 13)
        ((unique (ln i) (ei ▸ hxi)).trans (unique (ln j) (ej ▸ hxj)).symm))))
  simpa [extend, Circuit.size, Nat.add_assoc] using h

/-- Any witness to the positive twin of L-meta-2216 needs line-degree at least two at the
main output or the auxiliary wire. The general problem permits both wires to have higher degree. -/
theorem linear_line_bound (C : Circuit) (tap : ℕ) (hm : Monotone2 C)
    (ho : C.output < 25+C.size) (hc : Computes C tap)
    (hd : C.lineDeg 25 (Finset.Ico 12 25) ≤ 1)
    (ht : (C.lineDegrees 25 (Finset.Ico 12 25)).getD tap 0 ≤ 1) : 62 ≤ C.size := by
  exact slice_bound C tap hm ho (fun y _ => hc y) hd ht

end PuncturedLineBound
namespace PuncturedLineBound
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Each wire is viewed as a Boolean function on inputs with at most one active line. -/
abbrev TestInput := {y : Fin 25 → Bool // oneLine y}
abbrev Signal := TestInput → Bool

namespace Compression

private def zero : Signal := fun _ => false
private def source (w : List Signal) (i : ℕ) := w.getD i zero

private def value (w : List Signal) (g : Gate) : Signal :=
  fun t => g.op.eval (g.inputs.map fun i => source w i t)

/-- Compare on the one-line test domain. Replace a constant AND with a constant,
and an AND that agrees with any earlier wire with a copy of that wire.
If the operands are comparable, their AND agrees with the smaller operand. -/
noncomputable def replace (w : List Signal) (g : Gate) : Gate := by
  classical
  exact if g.op ≠ .and then g
    else if ∀ t, value w g t = false then ⟨.or, []⟩
    else if ∀ t, value w g t = true then ⟨.and, []⟩
    else if h : ∃ i : Fin w.length, ∀ t, value w g t = source w i.val t then
      ⟨.or, [h.choose.val]⟩
    else g

private lemma replace_value (w : List Signal) (g : Gate) (t : TestInput) :
    value w (replace w g) t = value w g t := by
  classical
  unfold replace
  split
  · rfl
  · split
    · next h => exact (h t).symm
    · split
      · next h => exact (h t).symm
      · split
        · next h =>
          have hc := h.choose_spec t
          simpa [value, GateOp.eval] using hc.symm
        · rfl

private def allowed (g : Gate) := g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

private theorem replace_allowed {g : Gate} (hg : allowed g) (w : List Signal) :
    allowed (replace w g) := by
  classical
  unfold replace
  split
  · exact hg
  · split
    · simp [allowed]
    · split
      · simp [allowed]
      · split
        · simp [allowed]
        · exact hg

noncomputable def rebuild (w : List Signal) : List Gate → List Gate
  | [] => []
  | g :: gs => replace w g :: rebuild (w ++ [value w g]) gs

private lemma length_rebuild (w : List Signal) (gs : List Gate) :
    (rebuild w gs).length = gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [rebuild, List.length_cons, ih]

private lemma all_allowed (w : List Signal) (gs : List Gate) (hg : ∀ g ∈ gs, allowed g) :
    ∀ g ∈ rebuild w gs, allowed g := by
  induction gs generalizing w with
  | nil => simp [rebuild]
  | cons g gs ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | h
    · exact replace_allowed (hg _ (by simp)) _
    · exact ih _ (fun r hr => hg r (List.mem_cons_of_mem _ hr)) q h

private def advance (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma advance_eval (w : List Signal) (g : Gate) (t : TestInput) :
    advance (w.map (fun f => f t)) g = (w ++ [value w g]).map (fun f => f t) := by
  have he (i : ℕ) : (w.map (fun f => f t)).getD i false = source w i t :=
    List.getD_map w zero (fun f => f t)
  simp only [advance, List.map_append, List.map_cons, List.map_nil, value, he]

private lemma sim (w : List Signal) (gs : List Gate) (t : TestInput) :
    (rebuild w gs).foldl advance (w.map (fun f => f t)) =
    gs.foldl advance (w.map (fun f => f t)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [rebuild, List.foldl_cons, advance_eval, List.map_append, List.map_cons,
      List.map_nil, replace_value]
    simpa only [List.map_append, List.map_cons, List.map_nil] using ih (w ++ [value w g])

private def inputs : List Signal := List.ofFn fun i t => t.val i

noncomputable def simplify (C : Circuit) : Circuit := ⟨rebuild inputs C.gates, C.output⟩

theorem size_eq (C : Circuit) : (simplify C).size = C.size := length_rebuild inputs C.gates

theorem same_on_slice (C : Circuit) (y : Fin 25 → Bool) (hy : oneLine y) :
    (simplify C).wires (List.ofFn y) = C.wires (List.ofFn y) := by
  have h := sim inputs C.gates ⟨y,hy⟩
  have source_eq : inputs.map (fun f => f ⟨y,hy⟩) = List.ofFn y := by
    simp only [inputs, List.map_ofFn, Function.comp_def]
  rw [source_eq] at h
  exact h

/-- A small solution must still have line-degree ≥ 2 after replacing every AND that is constant or
agrees with any earlier wire on the one-line test domain. -/
theorem necessary_after_simplification (C : Circuit) (tap : ℕ) (hm : Monotone2 C)
    (hs : C.size ≤ 61) (ho : C.output < 25+C.size) (hc : Computes C tap) :
    2 ≤ (simplify C).lineDeg 25 (Finset.Ico 12 25) ∨
    2 ≤ ((simplify C).lineDegrees 25 (Finset.Ico 12 25)).getD tap 0 := by
  by_contra! hn
  have mono : Monotone2 (simplify C) := all_allowed inputs C.gates hm
  have out : (simplify C).output < 25+(simplify C).size := by rw [size_eq]; exact ho
  have small := slice_bound (simplify C) tap mono out (fun y hy => by
    have e := same_on_slice C y hy
    simpa only [CorrectAt, Circuit.eval, e, show (simplify C).output = C.output from rfl] using hc y)
    (by omega) (by omega)
  rw [size_eq] at small
  omega

end Compression
end PuncturedLineBound

namespace PuncturedPlane
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PuncturedLineBound

/-- The exact optimum for the assigned function in the class in which both designated wires
have syntactic line-degree at most one. -/
theorem exact_linear_minimum :
    IsLeast {k : ℕ | ∃ (C : Circuit) (tap : ℕ), C.size = k ∧ Monotone2 C ∧
      C.output < 25 + C.size ∧ tap < 25 + C.size ∧ Computes C tap ∧
      C.lineDeg 25 (Finset.Ico 12 25) ≤ 1 ∧
      (C.lineDegrees 25 (Finset.Ico 12 25)).getD tap 0 ≤ 1} 62 := by
  constructor
  · obtain ⟨sz, hm, ho, ht, h⟩ := boundary
    exact ⟨circuit, auxiliary, sz, hm, ho, ht, h, boundary_degrees.1.le, boundary_degrees.2.le⟩
  · rintro k ⟨C, tap, rfl, hm, ho, _, hc, hd, ht⟩
    exact linear_line_bound C tap hm ho hc hd ht

/-- Feasibility includes all the bounds and both wire conditions from the desk. -/
abbrev Feasible61 (C : Circuit) (tap : ℕ) : Prop :=
  Monotone2 C ∧ C.size ≤ 61 ∧ C.output < 25 + C.size ∧
    tap < 25 + C.size ∧ Computes C tap

/-- An exact reduction of the posted task to its remaining high-degree case. -/
theorem remaining_cases :
    (¬ ∃ C tap, Feasible61 C tap) ↔
    ¬ ∃ C tap, Feasible61 C tap ∧
      (2 ≤ C.lineDeg 25 (Finset.Ico 12 25) ∨
       2 ≤ (C.lineDegrees 25 (Finset.Ico 12 25)).getD tap 0) := by
  constructor
  · rintro h ⟨C, tap, hC, _⟩
    exact h ⟨C, tap, hC⟩
  · rintro h ⟨C, tap, hC⟩
    apply h
    refine ⟨C, tap, hC, ?_⟩
    obtain ⟨hm, hs, ho, _, hc⟩ := hC
    by_contra! hn
    have := linear_line_bound C tap hm ho hc (by omega) (by omega)
    omega

end PuncturedPlane
