import FusionFanoCertificateOrder

/-!
A finite Boolean checker whose soundness is proved once for arbitrary cases.
Only the 35 increasing triples are visited. Star witnesses are checked using
structural list recursion, avoiding repeated finite-quantifier elaboration.
-/
noncomputable section

namespace FusionFanoFastCheck

open FusionFanoCertificates
open scoped BigOperators

abbrev Triple := Fin 7 × Fin 7 × Fin 7

def triples : List Triple :=
  [(0,1,2), (0,1,3), (0,1,4), (0,1,5), (0,1,6),
   (0,2,3), (0,2,4), (0,2,5), (0,2,6),
   (0,3,4), (0,3,5), (0,3,6), (0,4,5), (0,4,6), (0,5,6),
   (1,2,3), (1,2,4), (1,2,5), (1,2,6),
   (1,3,4), (1,3,5), (1,3,6), (1,4,5), (1,4,6), (1,5,6),
   (2,3,4), (2,3,5), (2,3,6), (2,4,5), (2,4,6), (2,5,6),
   (3,4,5), (3,4,6), (3,5,6), (4,5,6)]

theorem triples_complete : ∀ i j k : Fin 7, i < j → j < k →
    (i,j,k) ∈ triples := by
  decide +kernel

def checkTriple (c : Case) (t : Triple) : Bool :=
  let i := t.1
  let j := t.2.1
  let k := t.2.2
  if 0 < weights c i j + weights c i k + weights c j k then
    (FusionCube.stars (255 ^^^
      (FusionCube.face (rows c i) ||| FusionCube.face (rows c j) |||
        FusionCube.face (rows c k)))).all fun s =>
      (List.finRange 7).any fun a => decide
        (a ≠ i ∧ a ≠ j ∧ a ≠ k ∧ FusionCube.face (rows c a) &&& s = 0)
  else true

def fastCheck (c : Case) : Bool :=
  decide (0 < ∑ i : Fin 7, ∑ j : Fin 7, weights c i j) &&
    triples.all (checkTriple c)

theorem checkTriple_sound (c : Case) {i j k : Fin 7}
    (hcheck : checkTriple c (i,j,k) = true)
    (hpos : 0 < weights c i j + weights c i k + weights c j k) :
    ∀ s ∈ FusionCube.stars (255 ^^^
      (FusionCube.face (rows c i) ||| FusionCube.face (rows c j) |||
        FusionCube.face (rows c k))),
      ∃ a : Fin 7, a ≠ i ∧ a ≠ j ∧ a ≠ k ∧
        FusionCube.face (rows c a) &&& s = 0 := by
  simp only [checkTriple, hpos, ↓reduceIte] at hcheck
  intro s hs
  have ha := List.all_eq_true.mp hcheck s hs
  obtain ⟨a,_,ha⟩ := List.any_eq_true.mp ha
  exact ⟨a,of_decide_eq_true ha⟩

theorem fastCheck_goodAsc (c : Case) (h : fastCheck c = true) : GoodAsc c := by
  obtain ⟨htotal,htriples⟩ := Bool.and_eq_true_iff.mp h
  refine ⟨of_decide_eq_true htotal, ?_⟩
  intro i j k hij hjk hpos
  exact checkTriple_sound c
    (List.all_eq_true.mp htriples (i,j,k) (triples_complete i j k hij hjk)) hpos

theorem fastCheck_sound (c : Case) (h : fastCheck c = true) : Good c :=
  good_of_ascending c (fastCheck_goodAsc c h)

#print axioms triples_complete
#print axioms fastCheck_goodAsc
#print axioms fastCheck_sound

end FusionFanoFastCheck
