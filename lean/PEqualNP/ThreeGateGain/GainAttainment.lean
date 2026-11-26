import PEqualNP.ThreeGateGain.PencilWords
import PEqualNP.ThreeGateGain.FiniteValue
import PEqualNP.ThreeGateGain.GainGeometry
namespace GainAttainment
open GainFinite GainGeometry FixedBudgetGain TriangleOptimality Finset Configuration
open scoped Classical

variable {P L : Type*} [Fintype P] [Fintype L] [Membership P L] [ProjectivePlane P L]

/-- Four points on a line and an exterior apex form the witness in every plane
of order at least three, without coordinates. -/
theorem frame (hq : 3 ≤ ProjectivePlane.order P L) :
    ∃ (p : Fin 5 → P) (l : Fin 5 → L), Function.Injective p ∧ Function.Injective l ∧
      ∀ i j, p i ∈ l j ↔ cross i j = true := by
  classical
  obtain ⟨o,_,_,_,b,_,ho,_⟩ := @ProjectivePlane.exists_config P L _ _
  have n : 4 ≤ Fintype.card {x : P // x∈b} := by
    have := ProjectivePlane.pointCount_eq P b
    rw [pointCount,Nat.card_eq_fintype_card] at this; omega
  let e : Fin 4 ↪ {x : P // x∈b} := (Fin.castLEEmb n).trans (Fintype.equivFin _).symm.toEmbedding
  let x (i : Fin 4) := (e i).val
  have xi : Function.Injective x := fun _ _ h => e.injective (Subtype.ext h)
  have xb (i : Fin 4) : x i ∈ b := (e i).property
  have ox (i : Fin 4) : o ≠ x i := fun h => ho (h ▸ xb i)
  choose y hy using fun i => (HasLines.existsUnique_line P L o (x i) (ox i)).exists
  have yb (i : Fin 4) : y i ≠ b := fun h => ho (h ▸ (hy i).1)
  have xy (i j : Fin 4) : x i ∈ y j ↔ i=j := by
    constructor
    · intro h
      apply xi
      exact (Nondegenerate.eq_or_eq (xb i) (xb j) h (hy j).2).resolve_right (Ne.symm (yb j))
    · rintro rfl; exact (hy i).2
  have yi : Function.Injective y := fun i j h => (xy i j).mp (h ▸ (hy i).2)
  let p : Fin 5 → P := Fin.lastCases (motive:=fun _ => P) o x
  let l : Fin 5 → L := Fin.lastCases (motive:=fun _ => L) b y
  have p4 : p 4 = o := rfl
  have l4 : l 4 = b := rfl
  have pc (i : Fin 4) : p i.castSucc = x i := Fin.lastCases_castSucc ..
  have lc (i : Fin 4) : l i.castSucc = y i := Fin.lastCases_castSucc ..
  have apart (i : Fin 4) : i.castSucc ≠ (4 : Fin 5) := Fin.castSucc_ne_last i
  have pcross (i j : Fin 4) : cross i.castSucc j.castSucc = true ↔ i = j := by
    simp [cross,apart,eq_comm]
  have bcase (i : Fin 4) : cross i.castSucc 4 = true := by simp [cross,apart]
  have acase (j : Fin 4) : cross 4 j.castSucc = true := by simp [cross,apart]
  refine ⟨p,l,?_,?_,?_⟩
  · intro i; induction i using Fin.lastCases <;> intro j <;> induction j using Fin.lastCases
    · exact fun _ => rfl
    · rename_i j; intro h; exact (ox j (p4.symm.trans (h.trans (pc j)))).elim
    · rename_i i; intro h; exact (ox i (p4.symm.trans (h.symm.trans (pc i)))).elim
    · rename_i i j; intro h; exact congrArg Fin.castSucc (xi ((pc i).symm.trans (h.trans (pc j))))
  · intro i; induction i using Fin.lastCases <;> intro j <;> induction j using Fin.lastCases
    · exact fun _ => rfl
    · rename_i j; intro h; exact (yb j ((lc j).symm.trans (h.symm.trans l4))).elim
    · rename_i i; intro h; exact (yb i ((lc i).symm.trans (h.trans l4))).elim
    · rename_i i j; intro h; exact congrArg Fin.castSucc (yi ((lc i).symm.trans (h.trans (lc j))))
  · intro i; induction i using Fin.lastCases <;> intro j <;> induction j using Fin.lastCases
    · change o ∈ b ↔ false = true; simp [ho]
    · rename_i j; change p 4 ∈ l j.castSucc ↔ cross 4 j.castSucc = true; rw [p4,lc,acase]; simp [(hy j).1]
    · rename_i i; change p i.castSucc ∈ l 4 ↔ cross i.castSucc 4 = true; rw [pc,l4,bcase]; simp [xb]
    · rename_i i j; rw [pc,lc,pcross,xy]

private theorem bits : ∀ (a b : Site),
    threeValue 304 ((BitVec.ofNat 6 (pointWord a)) ||| (BitVec.ofNat 6 (lineWord b))) = wanted a b := by
  decide +kernel

private theorem extract {V : Type*} [Fintype V] [DecidableEq V] (s : Finset V) (f : V → ℤ) :
      (∑ v : V, if v∈s then f v else 0) = ∑ v ∈ s, f v := by rw [← sum_filter]; simp
private theorem pull {V : Type*} [Fintype V] (h : Prop) [Decidable h] (f : V → ℤ) :
      (∑ v : V, if h then f v else 0) = if h then ∑ v : V, f v else 0 := by
    by_cases t : h <;> simp [t]

private theorem count (x : Fin 5 → P) (y : Fin 5 → L) (ix : Function.Injective x)
    (iy : Function.Injective y) (frame' : ∀ i j, x i ∈ y j ↔ cross i j = true)
    (Q : P → L → Prop) (hQ : ∀ p l, Q p l ↔ p∈l ∧ ((∃ i, p = x i) ∨ (∃ j, l = y j))) :
    score (fun p l => p∈l) Q univ univ = 10 * (ProjectivePlane.order P L : ℤ) - 2 := by
  classical
  let G (p : P) (l : L) := p ∈ l
  let X := univ.image x
  let Y := univ.image y
  have cell (p : P) (l : L) : weight G Q p l =
      (if p∈X then hit G p l else 0) + (if l∈Y then hit G p l else 0) -
      (if p∈X then (if l∈Y then hit G p l else 0) else 0) := by
    have q : Q p l ↔ G p l ∧ (p∈X ∨ l∈Y) := by simpa [G,X,Y,eq_comm] using hQ p l
    by_cases g : G p l <;> by_cases a : p∈X <;> by_cases b : l∈Y <;> simp_all [weight,signedCell,hit]
  have rows (p:P) : ∑ l : L, hit G p l = (ProjectivePlane.order P L : ℤ)+1 := row_total p
  have cols (l:L) : ∑ p : P, hit G p l = (ProjectivePlane.order P L : ℤ)+1 := col_total l
  have xy : (∑ p ∈ X, ∑ l ∈ Y, hit G p l) = 12 := by
    dsimp only [X,Y]
    rw [sum_image (fun _ _ _ _ h => ix h)]
    simp_rw [sum_image (fun _ _ _ _ h => iy h)]
    have eq (i j : Fin 5) : hit G (x i) (y j) = if cross i j then 1 else 0 := by simp [hit,G,frame']
    simp_rw [eq]
    decide +kernel
  change score G Q _ _ = _
  simp only [score,cell,sum_add_distrib,sum_sub_distrib]
  rw [sum_comm (f:=fun p l => if l∈Y then hit G p l else 0)]
  simp_rw [pull,extract]
  rw [xy]
  simp_rw [rows,cols]
  simp [X,Y,card_image_of_injective _ ix,card_image_of_injective _ iy]; ring

theorem attained (hq : 3 ≤ ProjectivePlane.order P L) :
    ∃ (w : BitVec 9) (r : P → BitVec 6) (c : L → BitVec 6),
      score (fun p l => p∈l) (fun p l => threeValue w (r p ||| c l) = true) univ univ =
        10 * (ProjectivePlane.order P L : ℤ) - 2 ∧
      ∀ p l, threeValue w (r p ||| c l) = true → p∈l := by
  obtain ⟨x,y,ix,iy,hxy⟩ := frame hq
  let a := site x (fun p j => p ∈ y j)
  let b := site y (fun l i => x i ∈ l)
  let r (p:P) := BitVec.ofNat 6 (pointWord (a p))
  let c (l:L) := BitVec.ofNat 6 (lineWord (b l))
  have sq : FixedBudgetGain.NoSquare (fun (p:P) (l:L) => p∈l) := fun _ _ _ _ u v s t =>
    Nondegenerate.eq_or_eq u s v t
  have pred (p:P) (l:L) : threeValue 304 (r p ||| c l) = true ↔
      p ∈ l ∧ ((∃ i, p = x i) ∨ ∃ i, l = y i) := by
    rw [show threeValue 304 (r p ||| c l) = three (pointWord (a p)) (lineWord (b l)) by
      rw [bits (a p) (b l), table]]
    exact recognizes sq x y ix iy hxy p l
  exact ⟨304,r,c,count x y ix iy hxy _ pred, fun p l h => ((pred p l).mp h).1⟩

#print axioms attained
end GainAttainment
