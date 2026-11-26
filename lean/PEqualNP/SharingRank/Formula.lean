import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-! The strict rank loss of every formula with a paid union below another paid union
in the rectangle (zero-cell) model. Every finite sum below is a rank-one decomposition. -/
namespace SharingRank.Formulas
open Set
open scoped BigOperators Classical

inductive Expr (X Y : Type) where
  | rect (r : Set X) (c : Set Y)
  | meet (a b : Expr X Y)
  | join (a b : Expr X Y)

namespace Expr
variable {X Y : Type}

def cell : Expr X Y → X → Y → Prop
  | .rect r c, x,y => x ∈ r ∧ y ∈ c
  | .meet a b, x,y => cell a x y ∧ cell b x y
  | .join a b, x,y => cell a x y ∨ cell b x y

def cost : Expr X Y → Nat
  | .rect _ _ => 0
  | .meet a b => cost a + cost b
  | .join a b => cost a + cost b + 1

def Flat : Expr X Y → Prop
  | .rect _ _ => True
  | .meet a b => Flat a ∧ Flat b
  | .join a b => cost a = 0 ∧ cost b = 0

def Term : Expr X Y → Type
  | .rect _ _ => Unit
  | .meet a b => Term a × Term b
  | .join a b => Term a ⊕ (Term b ⊕ (Term a × Term b))

instance finiteTerm : (e : Expr X Y) → Fintype (Term e)
  | .rect _ _ => inferInstanceAs (Fintype Unit)
  | .meet a b => @instFintypeProd _ _ (finiteTerm a) (finiteTerm b)
  | .join a b =>
    letI := finiteTerm a
    letI := finiteTerm b
    inferInstanceAs (Fintype (Term a ⊕ (Term b ⊕ (Term a × Term b))))

noncomputable def rowTerm : (e : Expr X Y) → Term e → X → ℝ
  | .rect r _, _, x => if x ∈ r then 1 else 0
  | .meet a b, (i,j), x => rowTerm a i x * rowTerm b j x
  | .join a b, t, x => match t with
    | .inl i => rowTerm a i x
    | .inr (.inl j) => rowTerm b j x
    | .inr (.inr (i,j)) => -(rowTerm a i x * rowTerm b j x)

noncomputable def colTerm : (e : Expr X Y) → Term e → Y → ℝ
  | .rect _ c, _, y => if y ∈ c then 1 else 0
  | .meet a b, (i,j), y => colTerm a i y * colTerm b j y
  | .join a b, t, y => match t with
    | .inl i => colTerm a i y
    | .inr (.inl j) => colTerm b j y
    | .inr (.inr (i,j)) => colTerm a i y * colTerm b j y

private theorem product_sum {I J : Type} [Fintype I] [Fintype J]
    (a c : I → ℝ) (b d : J → ℝ) :
    (∑ u : I × J, (a u.1 * b u.2) * (c u.1 * d u.2)) =
      (∑ i, a i * c i) * ∑ j, b j * d j := by
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem expansion (e : Expr X Y) (x : X) (y : Y) :
    (∑ i : e.Term, e.rowTerm i x * e.colTerm i y) = if e.cell x y then 1 else 0 := by
  classical
  induction e with
  | rect r c =>
    change (∑ _ : Unit, (if x ∈ r then (1:ℝ) else 0) * (if y ∈ c then 1 else 0)) = _
    by_cases h : x ∈ r <;> by_cases j : y ∈ c <;> simp [cell,h,j]
  | meet a b ha hb =>
    change (∑ t : a.Term × b.Term, (a.rowTerm t.1 x * b.rowTerm t.2 x) *
      (a.colTerm t.1 y * b.colTerm t.2 y)) = _
    rw [product_sum (fun i => a.rowTerm i x) (fun i => a.colTerm i y)
      (fun i => b.rowTerm i x) (fun i => b.colTerm i y),ha,hb]
    by_cases h : a.cell x y <;> by_cases j : b.cell x y <;> simp [cell,h,j]
  | join a b ha hb =>
    change (∑ t : a.Term ⊕ (b.Term ⊕ (a.Term × b.Term)),
      (a.join b).rowTerm t x * (a.join b).colTerm t y) = _
    simp only [Fintype.sum_sum_type,rowTerm,colTerm,neg_mul,Finset.sum_neg_distrib]
    rw [product_sum (fun i => a.rowTerm i x) (fun i => a.colTerm i y)
      (fun i => b.rowTerm i x) (fun i => b.colTerm i y),ha,hb]
    by_cases h : a.cell x y <;> by_cases j : b.cell x y <;> simp [cell,h,j]

noncomputable def matrix (e : Expr X Y) : Matrix X Y ℝ :=
  fun x y => if e.cell x y then 1 else 0

theorem rank_terms [Fintype Y] (e : Expr X Y) : e.matrix.rank ≤ Fintype.card e.Term := by
  let A : Matrix X e.Term ℝ := fun x i => e.rowTerm i x
  let B : Matrix e.Term Y ℝ := fun i y => e.colTerm i y
  have eq : A * B = e.matrix := Matrix.ext (fun x y => expansion e x y)
  rw [← eq]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)

private theorem join_bound (a b : Nat) :
    3^a + 3^b + 3^a*3^b ≤ 3^(a+b+1) := by
  rw [pow_succ,pow_add]
  have h : 1 ≤ 3^a := Nat.one_le_pow _ _ (by decide)
  have j : 1 ≤ 3^b := Nat.one_le_pow _ _ (by decide)
  have x := Nat.mul_le_mul_left (3^a) j
  have y := Nat.mul_le_mul_right (3^b) h
  nlinarith only [x,y]

private theorem strict_join (a b : Nat) (ha : 0 < a ∨ 0 < b) :
    9*(3^a + 3^b + 3^a*3^b) ≤ 7*3^(a+b+1) := by
  rw [pow_succ,pow_add]
  have positive (n : Nat) : 1 ≤ 3^n := Nat.one_le_pow _ _ (by decide)
  rcases ha with h|h
  · have big : 3 ≤ 3^a := (show 3^1 ≤ 3^a from Nat.pow_le_pow_right (by decide) h)
    have x := Nat.mul_le_mul_left (3^a) (positive b)
    have y := Nat.mul_le_mul_right (3^b) big
    nlinarith only [x,y]
  · have big : 3 ≤ 3^b := (show 3^1 ≤ 3^b from Nat.pow_le_pow_right (by decide) h)
    have x := Nat.mul_le_mul_right (3^b) (positive a)
    have y := Nat.mul_le_mul_left (3^a) big
    nlinarith only [x,y]

theorem counts (e : Expr X Y) : Fintype.card e.Term ≤ 3^e.cost ∧
    (¬ e.Flat → 9 * Fintype.card e.Term ≤ 7 * 3^e.cost) := by
  induction e with
  | rect r c =>
    constructor
    · exact (show Fintype.card Unit ≤ 1 by decide)
    · exact fun h => (h trivial).elim
  | meet a b ha hb =>
    simp only [Term,Fintype.card_prod,cost,Flat,pow_add]
    refine ⟨Nat.mul_le_mul ha.1 hb.1,?_⟩
    intro hn
    by_cases h : a.Flat
    · have small := hb.2 (fun h' => hn ⟨h,h'⟩)
      simpa [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using Nat.mul_le_mul ha.1 small
    · simpa [Nat.mul_assoc] using Nat.mul_le_mul (ha.2 h) hb.1
  | join a b ha hb =>
    have card : Fintype.card (a.join b).Term = Fintype.card a.Term +
        (Fintype.card b.Term + Fintype.card a.Term * Fintype.card b.Term) := by
      trans Fintype.card (a.Term ⊕ (b.Term ⊕ (a.Term × b.Term)))
      · exact Fintype.card_congr (Equiv.refl _)
      · simp only [Fintype.card_sum,Fintype.card_prod]
    simp only [card,cost,Flat]
    have base := Nat.add_le_add ha.1 (Nat.add_le_add hb.1 (Nat.mul_le_mul ha.1 hb.1))
    simp only [← Nat.add_assoc] at base ⊢
    refine ⟨base.trans (join_bound _ _),?_⟩
    intro hn
    have pos : 0 < a.cost ∨ 0 < b.cost := by omega
    exact (Nat.mul_le_mul_left 9 base).trans (strict_join _ _ pos)

theorem nested_rank [Fintype Y] (e : Expr X Y) (h : ¬ e.Flat) :
    9 * e.matrix.rank ≤ 7 * 3^e.cost :=
  (Nat.mul_le_mul_left _ (rank_terms e)).trans ((counts e).2 h)
end Expr
end SharingRank.Formulas
