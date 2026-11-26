import PEqualNP.SixSharing.SixFinite

/-! Exact 3 versus 4 on a 6 by 6 graph in the free-union star model.
We work with zero sets, using pjscruggs's two-gate classification and
the three-gate classification and formula definitions of the 8 by 8 hand-back. -/
namespace SixSharing
open Set TwoIntersections ThreeIntersectionsFormula ThreeIntersectionsSharingGap
open SixFormulaCheck (Shape Code value masks no_representation)
abbrev Cell := Fin 6 × Fin 6

def zero : Set Cell := {p | (masks p.1).getLsbD p.2.val = true}

def rowSides : Fin 6 → Code := ![26,36,57,46,15,48]
def colSides : Fin 6 → Code := ![54,61,44,31,63,58]
def rect (i : Fin 6) : Set Cell :=
  {r : Fin 6 | (rowSides i).getLsbD r.val = true} ×ˢ
  {c : Fin 6 | (colSides i).getLsbD c.val = true}

theorem rect_ok (i : Fin 6) : Rectangle (rect i) := ⟨_,_,rfl⟩

theorem construction : zero = (rect 2 ∪ (rect 3 ∩ (rect 0 ∪ rect 1))) ∩
    (rect 4 ∪ (rect 5 ∩ (rect 0 ∪ rect 1))) := by
  ext p
  revert p
  unfold zero masks rect rowSides colSides
  decide +kernel

theorem circuit_three : ThreeIntersections.Three Rectangle zero := by
  apply (ThreeIntersections.rectangle_normal_iff zero).mpr
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_,_,_,_,_,_, rect_ok 0, rect_ok 1,
    rect_ok 2, rect_ok 3, rect_ok 4, rect_ok 5, construction⟩)))

theorem formula_four : Formula Rectangle 4 zero := by
  rw [construction]
  exact diamond_four_formula (rect_ok 0) (rect_ok 1) (rect_ok 2) (rect_ok 3) (rect_ok 4) (rect_ok 5)

private def form (s : Shape) (t : Fin 6 → Set Cell) : Set Cell :=
  match s with
  | .four => (t 0 ∪ t 1) ∪ (t 2 ∪ t 3)
  | .threeTwo => ((t 0 ∪ t 1) ∪ t 2) ∩ (t 3 ∪ t 4)
  | .cube => ((t 0 ∪ t 1) ∩ (t 2 ∪ t 3)) ∩ (t 4 ∪ t 5)
  | .outside => t 0 ∪ ((t 1 ∪ t 2) ∩ (t 3 ∪ t 4))

private noncomputable def pack (side : Fin 6 → Set (Fin 6)) (i : Fin 6) : Code := by
  classical
  exact BitVec.ofBoolListLE [decide (i ∈ side 0), decide (i ∈ side 1), decide (i ∈ side 2),
    decide (i ∈ side 3), decide (i ∈ side 4), decide (i ∈ side 5)]

private theorem no_form (s : Shape) (t : Fin 6 → Set Cell) (hr : ∀ i, Rectangle (t i))
    (hz : zero = form s t) : False := by
  classical
  choose R C hRC using hr
  apply no_representation s (pack R) (pack C)
  intro i j
  have hmem : (masks i).getLsbD j.val = true ↔ (i,j) ∈ form s t := by
    change (i,j) ∈ zero ↔ _
    rw [hz]
  have hv : value s (pack R i &&& pack C j) = true ↔ (i,j) ∈ form s t := by
    cases s <;> simp only [value,pack,BitVec.getLsbD_and,BitVec.getLsbD_ofBoolListLE] <;>
      simp [form,hRC,List.getD]
  exact Bool.eq_iff_iff.mpr (hv.trans hmem.symm)

theorem no_first_four : ¬ FirstFour Rectangle zero := by
  rintro (⟨a,b,c,d,ha,hb,hc,hd,hz⟩ | ⟨a,b,c,d,e,ha,hb,hc,hd,he,hz⟩ |
    ⟨a,b,c,d,e,f,ha,hb,hc,hd,he,hf,hz⟩ | ⟨a,b,c,d,e,ha,hb,hc,hd,he,hz⟩)
  · apply no_form .four ![a,b,c,d,a,b] _ hz
    intro i
    fin_cases i <;> assumption
  · apply no_form .threeTwo ![a,b,c,d,e,a] _ hz
    intro i
    fin_cases i <;> assumption
  · apply no_form .cube ![a,b,c,d,e,f] _ hz
    intro i
    fin_cases i <;> assumption
  · apply no_form .outside ![a,b,c,d,e,a] _ hz
    intro i
    fin_cases i <;> assumption

private theorem rect_closed : Closed (@Rectangle (Fin 6) (Fin 6)) := by
  rintro _ _ ⟨a,b,rfl⟩ ⟨c,d,rfl⟩
  exact ⟨a ∩ c,b ∩ d,by ext p; simp; tauto⟩

theorem formula_lower {n : Nat} (hn : n < 4) : ¬ Formula Rectangle n zero :=
  fun h => no_first_four (formula_first_four rect_closed h (by omega))

theorem circuit_lower : ¬ Two Rectangle zero := by
  intro h
  rcases (TwoIntersections.rectangle_normal_iff zero).mp h with
      ⟨a,b,c,ha,hb,hc,hz⟩ | ⟨a,b,c,d,ha,hb,hc,hd,hz⟩
  · apply formula_lower (n := 2) (by decide)
    rw [hz]
    exact .join (.join (.base ha) (.base hb)) (.base hc)
  · apply formula_lower (n := 2) (by decide)
    rw [hz]
    exact .meet (.join (.base ha) (.base hb)) (.join (.base hc) (.base hd))

theorem exact_circuit_formula_gap :
    ThreeIntersections.Three Rectangle zero ∧ ¬ Two Rectangle zero ∧
    Formula Rectangle 4 zero ∧ ∀ n, n < 4 → ¬ Formula Rectangle n zero :=
  ⟨circuit_three, circuit_lower, formula_four, fun _ => formula_lower⟩

#print axioms exact_circuit_formula_gap
end SixSharing
