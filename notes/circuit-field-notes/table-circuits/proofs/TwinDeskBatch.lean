import PEqualNP.Outside.TwinTable

namespace PEqualNP.Outside.TwinDeskBatch_aux
open PEqualNP.MetaComplexity PEqualNP.Represents
open TwinCircuit_aux

abbrev Entry := Nat × Nat × Nat × Nat
abbrev Cert := Entry × List Nat × List Nat

def certs : List Cert :=
  [((3,4,301,7),[0, 2, 1],[0, 2, 1, 1]),
   ((3,4,316,7),[2, 0, 1],[0, 1, 2, 2]),
   ((3,4,366,7),[0, 1, 2],[2, 0, 0, 1]),
   ((4,5,33886,9),[0, 1, 2, 2],[2, 0, 1, 1, 1]),
   ((4,5,33916,9),[2, 0, 1, 1],[0, 1, 2, 2, 2]),
   ((4,5,34009,9),[0, 2, 1, 1],[0, 2, 2, 1, 1]),
   ((4,5,34014,9),[0, 1, 2, 2],[2, 0, 0, 1, 1]),
   ((4,5,35773,9),[0, 0, 2, 1],[0, 2, 1, 1, 1]),
   ((4,5,35964,9),[2, 0, 0, 1],[0, 1, 2, 2, 2]),
   ((4,5,39129,9),[0, 2, 2, 1],[0, 2, 2, 1, 1]),
   ((4,5,39134,9),[0, 1, 1, 2],[2, 0, 0, 1, 1]),
   ((4,5,39737,9),[0, 0, 2, 1],[0, 2, 2, 1, 1]),
   ((4,5,39902,10),[0, 0, 1, 2],[2, 0, 0, 1, 1]),
   ((4,5,47582,9),[0, 1, 1, 2],[2, 0, 0, 0, 1]),
   ((4,5,48094,10),[0, 0, 1, 2],[2, 0, 0, 0, 1]),
   ((4,5,101624,9),[2, 0, 1, 1],[0, 0, 1, 2, 2]),
   ((4,5,101788,9),[0, 1, 2, 2],[2, 2, 0, 0, 1]),
   ((4,5,105720,10),[2, 0, 0, 1],[0, 0, 1, 2, 2]),
   ((4,6,266429,10),[0, 2, 1, 1],[0, 2, 1, 1, 1, 1]),
   ((4,6,266430,10),[0, 1, 2, 2],[2, 0, 1, 1, 1, 1]),
   ((4,6,266686,10),[0, 1, 2, 2],[2, 0, 0, 1, 1, 1]),
   ((4,6,266744,10),[2, 0, 1, 1],[0, 1, 1, 2, 2, 2]),
   ((4,6,267198,10),[0, 1, 2, 2],[2, 0, 0, 0, 1, 1]),
   ((4,6,268222,10),[0, 1, 2, 2],[2, 0, 0, 0, 0, 1]),
   ((4,6,274301,10),[0, 0, 2, 1],[0, 2, 1, 1, 1, 1]),
   ((4,6,287161,10),[0, 2, 2, 1],[0, 2, 2, 1, 1, 1]),
   ((4,6,287166,10),[0, 1, 1, 2],[2, 0, 0, 1, 1, 1]),
   ((4,6,290425,10),[0, 0, 2, 1],[0, 2, 2, 1, 1, 1]),
   ((4,6,290750,11),[0, 0, 1, 2],[2, 0, 0, 1, 1, 1]),
   ((4,6,291320,10),[2, 0, 0, 1],[0, 1, 1, 2, 2, 2]),
   ((4,6,320446,10),[0, 1, 1, 2],[2, 0, 0, 0, 1, 1]),
   ((4,6,323518,11),[0, 0, 1, 2],[2, 0, 0, 0, 1, 1]),
   ((3,6,4285,9),[0, 2, 1],[0, 2, 1, 1, 1, 1]),
   ((3,6,4348,9),[2, 0, 1],[0, 1, 2, 2, 2, 2]),
   ((3,6,4537,9),[0, 2, 1],[0, 2, 2, 1, 1, 1]),
   ((3,6,4542,9),[0, 1, 2],[2, 0, 0, 1, 1, 1]),
   ((3,6,5054,9),[0, 1, 2],[2, 0, 0, 0, 1, 1]),
   ((3,6,6078,9),[0, 1, 2],[2, 0, 0, 0, 0, 1]),
   ((3,6,13107,9),[0, 2, 1],[0, 0, 2, 2, 1, 1]),
   ((3,6,14140,9),[0, 1, 2],[2, 2, 0, 0, 0, 1]),
   ((4,6,389054,11),[0, 0, 1, 2],[2, 0, 0, 0, 0, 1]),
   ((4,6,799224,10),[2, 0, 1, 1],[0, 0, 1, 2, 2, 2]),
   ((4,6,799539,10),[0, 2, 1, 1],[0, 0, 2, 2, 1, 1]),
   ((4,6,799548,10),[0, 1, 2, 2],[2, 2, 0, 0, 1, 1]),
   ((4,6,800572,10),[0, 1, 2, 2],[2, 2, 0, 0, 0, 1]),
   ((4,6,815608,11),[2, 0, 0, 1],[0, 0, 1, 2, 2, 2]),
   ((4,6,838899,11),[0, 0, 2, 1],[0, 0, 2, 2, 1, 1]),
   ((4,6,902972,10),[0, 1, 1, 2],[2, 2, 0, 0, 0, 1]),
   ((4,6,905020,11),[0, 0, 1, 2],[2, 2, 0, 0, 0, 1])]

def label {d : Nat} (l : List Nat) (j : Fin d) : Fin 3 := Fin.ofNat 3 (l.getD j.val 0)
def maskG (e : Entry) (r : Fin e.1) (c : Fin e.2.1) := e.2.2.1.testBit (e.2.1*r.val+c.val)

def Valid (b : Cert) : Prop :=
  let e := b.1
  let pr := @label e.1 b.2.1
  let pc := @label e.2.1 b.2.2
  (∀ i, ∃ r, pr r = i) ∧ (∀ i, ∃ c, pc c = i) ∧
  (∀ r c, maskG e r c = graph pr pc r c) ∧
    e.1+e.2.1+min (classCard pr 0) (classCard pc 0) = e.2.2.2+1 ∧ 0 < e.1+e.2.1

instance (b : Cert) : Decidable (Valid b) := by unfold Valid; infer_instance

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
theorem checked : ∀ b ∈ certs, Valid b := by decide

def Cost (e : Entry) :=
  RepSizeAtMost (maskG e) (e.1+e.2.1) ∧
  (¬ RepSizeAtMost (maskG e) (e.1+e.2.1-1)) ∧
  ∀ k : Nat, (∃ f : DMFormula (e.1+e.2.1), TwinReduction_aux.pos f ∧
    (∀ r c, f.eval (FormulaGap_aux.bits (r,c)) = maskG e r c) ∧ f.leaves ≤ k) ↔ e.2.2.2+1 ≤ k

theorem cost_of_cert {b : Cert} (h : Valid b) : Cost b.1 := by
  let e := b.1
  let pr := @label e.1 b.2.1
  let pc := @label e.2.1 b.2.2
  obtain ⟨hr,hc,eq,num,positive⟩ := h
  have same : maskG e = graph pr pc := funext (fun r => funext (eq r))
  change e.1+e.2.1+min (classCard pr 0) (classCard pc 0) = e.2.2.2+1 at num
  change 0 < e.1+e.2.1 at positive
  change Cost e
  unfold Cost
  change RepSizeAtMost (maskG e) _ ∧ (¬ RepSizeAtMost (maskG e) _) ∧ _
  change _ ∧ _ ∧ ∀ k : Nat, (∃ f : DMFormula (e.1+e.2.1), TwinReduction_aux.pos f ∧
    (∀ r c, f.eval (FormulaGap_aux.bits (r,c)) = maskG e r c) ∧ f.leaves ≤ k) ↔ e.2.2.2+1 ≤ k
  rw [same]
  refine ⟨upper pr pc hr hc, lower pr pc hr hc _ (Nat.sub_lt positive (by decide)), fun k => ?_⟩
  simpa only [num] using formula pr pc hr hc k

theorem allCosts : ∀ e ∈ certs.map Prod.fst, Cost e := by
  intro e he
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp he
  exact cost_of_cert (checked b hb)

end PEqualNP.Outside.TwinDeskBatch_aux

theorem PEqualNP.Outside.TwinDeskBatch :
  let Pos := fun {d : Nat} (f : PEqualNP.MetaComplexity.DMFormula d) =>
    PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => Prop) (fun _ b => b = true)
      (fun _ _ l r => l ∧ r) (fun _ _ l r => l ∧ r) f
  ∀ e ∈ ([
    (3,4,301,7), (3,4,316,7), (3,4,366,7), (4,5,33886,9),
    (4,5,33916,9), (4,5,34009,9), (4,5,34014,9), (4,5,35773,9),
    (4,5,35964,9), (4,5,39129,9), (4,5,39134,9), (4,5,39737,9),
    (4,5,39902,10), (4,5,47582,9), (4,5,48094,10), (4,5,101624,9),
    (4,5,101788,9), (4,5,105720,10), (4,6,266429,10), (4,6,266430,10),
    (4,6,266686,10), (4,6,266744,10), (4,6,267198,10), (4,6,268222,10),
    (4,6,274301,10), (4,6,287161,10), (4,6,287166,10), (4,6,290425,10),
    (4,6,290750,11), (4,6,291320,10), (4,6,320446,10), (4,6,323518,11),
    (3,6,4285,9), (3,6,4348,9), (3,6,4537,9), (3,6,4542,9),
    (3,6,5054,9), (3,6,6078,9), (3,6,13107,9), (3,6,14140,9),
    (4,6,389054,11), (4,6,799224,10), (4,6,799539,10), (4,6,799548,10),
    (4,6,800572,10), (4,6,815608,11), (4,6,838899,11), (4,6,902972,10),
    (4,6,905020,11)] : List (Nat × Nat × Nat × Nat)),
    let R := e.1
    let C := e.2.1
    let G := fun (r : Fin R) (c : Fin C) => e.2.2.1.testBit (C*r.val+c.val)
    PEqualNP.Represents.RepSizeAtMost G (R+C) ∧
    (¬ PEqualNP.Represents.RepSizeAtMost G (R+C-1)) ∧
    ∀ k : Nat,
      (∃ f : PEqualNP.MetaComplexity.DMFormula (R+C), Pos f ∧
        (∀ r c, f.eval (Fin.addCases (fun i => decide (i = r)) (fun j => decide (j = c))) = G r c) ∧
        f.leaves ≤ k) ↔ e.2.2.2 + 1 ≤ k :=
  TwinDeskBatch_aux.allCosts
