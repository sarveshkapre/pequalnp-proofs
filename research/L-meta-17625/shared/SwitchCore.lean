import PEqualNP.Outside.L_meta_7465

/-! Lower bounds from shared dirty ANDs and independently selectable negative inputs. -/
namespace SwitchCore
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_7465_aux
open PEqualNP.Outside.L_meta_7465_aux.Routing

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

abbrev value (C : Circuit) (x : Fin n → Bool) (w : ℕ) := val C (List.ofFn x) w

/-- Wires reached along ORs from an operand of an AND. Descending past an AND
starts a new such segment. -/
def belowAnd (n : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  ∃ a, a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
    ∃ i : Fin 2, Relation.ReflTransGen (OrStep n C) (opnd C a i) w

/-- Along with the dirty gates, some top ANDs can be switched directly. -/
def observed (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (E : Finset ℕ)
    (w : ℕ) := belowAnd n C w ∨ ∃ h ∈ E, w = n+h

abbrev gates (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (E : Finset ℕ) :=
  junk G C ∪ E

def valid (C : Circuit) (E : Finset ℕ) := ∀ h ∈ E, h < C.gates.length ∧ (gateAt C h).op = GateOp.and

theorem gate_data {E : Finset ℕ} (ve : valid C E) (j : gates G C E) :
    j.val < C.gates.length ∧ (gateAt C j.val).op = GateOp.and := by
  rcases Finset.mem_union.mp j.2 with hj | he
  · exact ⟨(junkData hj).1,(junkData hj).2.1⟩
  · exact ve j he

variable {E : Finset ℕ}

/-- On a negative assignment, choose a false input for every false AND.
An AND which is on may choose either input. -/
def switches (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (E : Finset ℕ) (x : Fin n → Bool) (j : gates G C E) : Bool :=
  value C x (opnd C j.val 0)

theorem selected_on (ao : IsAO2 n C) (ve : valid C E) (x : Fin n → Bool) (j : gates G C E) :
    value C x (opnd C j.val (if switches G C E x j then 1 else 0)) = true →
      gateVal n C j.val x = true := by
  intro h
  apply (andValBoth ao (gate_data ve j).1 (gate_data ve j).2 x).mpr
  cases he : switches G C E x j with
  | false =>
    change value C x (opnd C j.val 0) = false at he
    simp [switches,he] at h
  | true =>
    have first : value C x (opnd C j.val 0) = true := he
    exact ⟨first, by simpa [he] using h⟩

/-- A choice is compatible with an assignment if every false AND selects a false operand. -/
def compatible (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (E : Finset ℕ) (x : Fin n → Bool) (code : gates G C E → Bool) : Prop :=
  ∀ j, value C x (opnd C j.val (if code j then 1 else 0)) = true → gateVal n C j.val x = true

/-- Two compatible assignments may be joined coordinatewise below an AND.
The chosen wire can be shared without limit. -/
theorem union_compatible (ao : IsAO2 n C) (top : TopForm G C) (ve : valid C E)
    {x y z : Fin n → Bool} (sub : ∀ i, x i = true → y i = true ∨ z i = true)
    {code : gates G C E → Bool} (left : compatible G C E y code) (right : compatible G C E z code)
    (w : ℕ) (under : observed G C E w)
    (yes : value C x w = true) : value C y w = true ∨ value C z w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases input : w < n
    · let v : Fin n := ⟨w,input⟩
      have h := sub v ((val_ofFn C x v).symm ▸ yes)
      change value C y v.val = true ∨ value C z v.val = true
      simpa only [value,val_ofFn] using h
    · obtain ⟨j,rfl⟩ : ∃ j, w = n + j := ⟨w-n,by omega⟩
      have len : j < C.gates.length := by
        rcases under with ⟨a,alen,_,i,path⟩ | ⟨h,hm,eq⟩
        · have := orStep_le path
          have := opndBound ao alen i
          omega
        · have := (ve h hm).1
          omega
      rcases ao.1 _ (gateAt_mem len) with andOp | orOp
      · have m : j ∈ gates G C E := by
          rcases under with ⟨a,alen,aAnd,i,path⟩ | ⟨h,hm,eq⟩
          · exact Finset.mem_union_left _ (operandOrAndJunk ao top alen aAnd (reach_orReaches path j rfl len) andOp)
          · exact Finset.mem_union_right _ ((show h = j by omega) ▸ hm)
        let k : gates G C E := ⟨j,m⟩
        let b : Fin 2 := if code k then 1 else 0
        have xp := (andValOperands ao len andOp x).mp yes b
        have u : belowAnd n C (opnd C j b) := ⟨j,len,andOp,b,.refl⟩
        rcases ih _ (opndBound ao len b) (Or.inl u) xp with yp | zp
        · exact Or.inl (left k yp)
        · exact Or.inr (right k zp)
      · obtain ⟨u,memu,ub,ux⟩ := (val_or (n := n) (by simp) len orOp).mp yes
        have step : OrStep n C (n+j) u := ⟨j,len,rfl,orOp,memu,ub⟩
        have child : observed G C E u := by
          rcases under with ⟨a,alen,aAnd,i,path⟩ | ⟨h,hm,eq⟩
          · exact Or.inl ⟨a,alen,aAnd,i,path.tail step⟩
          · have same : h = j := by omega
            subst h
            rw [(ve j hm).2] at orOp
            cases orOp
        rcases ih u ub child ux with uy | uz
        · exact Or.inl ((val_or (n := n) (by simp) len orOp).mpr ⟨u,memu,ub,uy⟩)
        · exact Or.inr ((val_or (n := n) (by simp) len orOp).mpr ⟨u,memu,ub,uz⟩)

/-- One switch pattern can cover at most one of the protected negative transversals. -/
theorem compatible_transversals_equal {I : Type*} [Fintype I] (ao : IsAO2 n C) (top : TopForm G C) (ve : valid C E)
    (e : I → Bool → Fin n) (neg : (I → Bool) → Fin n → Bool) (W : Set ℕ)
    (under : ∀ w ∈ W, observed G C E w) (contains : ∀ b i, neg b (e i (b i)) = true)
    (hit : ∀ i, ∃ w ∈ W, value C (pairInput (e i false) (e i true)) w = true)
    (quiet : ∀ b w, w ∈ W → value C (neg b) w = false)
    {b c : I → Bool} {code : gates G C E → Bool}
    (left : compatible G C E (neg b) code) (right : compatible G C E (neg c) code) : b = c := by
  funext i
  by_contra diff
  have covered : ∀ t, pairInput (e i false) (e i true) t = true →
      neg b t = true ∨ neg c t = true := by
    intro t on
    have two := (pairInput_true _ _ _).mp on
    have hb := contains b i
    have hh := contains c i
    rcases two with rfl | rfl <;> cases hbi : b i <;> cases hci : c i <;> simp_all
  obtain ⟨w,hw,on⟩ := hit i
  rcases union_compatible ao top ve covered left right w (under w hw) on with h | h
  · exact Bool.false_ne_true ((quiet b w hw).symm.trans h)
  · exact Bool.false_ne_true ((quiet c w hw).symm.trans h)

/-- Each independently switchable matched pair requires a distinct bit of AND
capacity, even when all pairs use the same OR gates or conditional filters. -/
theorem matched_pairs_le_gates {I : Type*} [Fintype I] (ao : IsAO2 n C) (top : TopForm G C) (ve : valid C E)
    (e : I → Bool → Fin n) (neg : (I → Bool) → Fin n → Bool) (W : Set ℕ)
    (under : ∀ w ∈ W, observed G C E w) (contains : ∀ b i, neg b (e i (b i)) = true)
    (hit : ∀ i, ∃ w ∈ W, value C (pairInput (e i false) (e i true)) w = true)
    (quiet : ∀ b w, w ∈ W → value C (neg b) w = false) :
    Fintype.card I ≤ (gates G C E).card := by
  classical
  let code (b : I → Bool) := switches G C E (neg b)
  have inj : Function.Injective code := by
    intro b c hc
    exact compatible_transversals_equal ao top ve e neg W under contains hit quiet
      (selected_on ao ve (neg b)) (by change compatible G C E (neg c) (code b); rw [hc]; exact selected_on ao ve _)
  have sizes := Fintype.card_le_of_injective _ inj
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] at sizes
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp sizes

/-- Equality forces opposite operands at every dirty AND on every protected
negative assignment. A single gate with equal operands costs one additional AND. -/
theorem equal_budget_forces_opposite {I : Type*} [Fintype I] (ao : IsAO2 n C) (top : TopForm G C) (ve : valid C E)
    (e : I → Bool → Fin n) (neg : (I → Bool) → Fin n → Bool) (W : Set ℕ)
    (under : ∀ w ∈ W, observed G C E w) (contains : ∀ b i, neg b (e i (b i)) = true)
    (hit : ∀ i, ∃ w ∈ W, value C (pairInput (e i false) (e i true)) w = true)
    (quiet : ∀ b w, w ∈ W → value C (neg b) w = false)
    (exactSize : Fintype.card I = (gates G C E).card) (b : I → Bool) (j : gates G C E) :
    value C (neg b) (opnd C j.val 0) ≠ value C (neg b) (opnd C j.val 1) := by
  classical
  let f (b : I → Bool) := switches G C E (neg b)
  have inj : Function.Injective f := by
    intro b c eq
    exact compatible_transversals_equal ao top ve e neg W under contains hit quiet
      (selected_on ao ve (neg b)) (by change compatible G C E (neg c) (f b); rw [eq]; exact selected_on ao ve _)
  have surj : Function.Surjective f :=
    ((Fintype.bijective_iff_injective_and_card f).mpr
      ⟨inj, by simp only [Fintype.card_fun,Fintype.card_coe]; rw [exactSize]⟩).2
  intro tied
  let flip := Function.update (f b) j (!(f b j))
  have feasible : compatible G C E (neg b) flip := by
    intro q on
    by_cases eq : q = j
    · subst q
      have both := andValBoth ao (gate_data ve j).1 (gate_data ve j).2 (neg b)
      apply both.mpr
      cases choice : flip j <;> simp only [choice, Bool.false_eq_true, ite_false, ite_true] at on
      · exact ⟨on, tied.symm.trans on⟩
      · exact ⟨tied.trans on, on⟩
    · have stay : flip q = f b q := Function.update_of_ne eq _ _
      rw [stay] at on
      exact selected_on ao ve (neg b) q on
  obtain ⟨c,hc⟩ := surj flip
  have same : c = b := compatible_transversals_equal ao top ve e neg W under contains hit quiet
    (hc ▸ selected_on ao ve (neg c)) feasible
  have bit := congrFun (same ▸ hc) j
  change f b j = Function.update (f b) j (!(f b j)) j at bit
  simp at bit

#print axioms equal_budget_forces_opposite
#print axioms matched_pairs_le_gates
end SwitchCore
