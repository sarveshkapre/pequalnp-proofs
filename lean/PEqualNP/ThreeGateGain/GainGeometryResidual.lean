import PEqualNP.ThreeGateGain.GainGeometry

namespace GainGeometry
open Finset TriangleOptimality
open scoped Classical

variable {P L I J : Type*}

noncomputable def fiber (A : Finset P) (r : P → I) (i : I) : Finset P :=
  A.filter (r · = i)

theorem score_le_edges (G Q : P → L → Prop) (A : Finset P) (B : Finset L) :
    score G Q A B ≤ edges G A B := by
  apply sum_le_sum; intro p _
  apply sum_le_sum; intro l _
  by_cases g : G p l <;> by_cases h : Q p l <;> simp [weight, signedCell, hit, g, h]

private theorem card_bound (G : P → L → Prop) (A : Finset P) (B : Finset L) :
    gain G A B ≤ (A.card : ℤ) * B.card := by
  rw [gain_sum]
  have h := sum_le_sum (s:=A) (fun p _ => sum_le_sum (s:=B) (g:=fun _ => (1:ℤ))
    (fun l _ => show signedCell G p l ≤ 1 by by_cases z : G p l <;> simp [signedCell, hit, z]))
  simpa using h

private theorem thin_bound (G : P → L → Prop) (hs : NoSquare G) (A : Finset P) (B : Finset L)
    (a₂ : 2 ≤ A.card) (a₃ : A.card ≤ 3) : gain G A B ≤ 3 := by
  rcases le_or_gt 2 B.card with b | b
  · exact signed_rectangle G hs A B a₂ b
  · have x := card_bound G A B
    nlinarith [mul_nonneg (show 0 ≤ (A.card:ℤ) by positivity) (show 0 ≤ 1-(B.card:ℤ) by omega)]

private theorem small_block (G : P → L → Prop) (hs : NoSquare G) (A : Finset P) (B : Finset L)
    (a : A.card ≤ 3) (b : B.card ≤ 3) : gain G A B ≤ 3 := by
  rcases le_or_gt 2 A.card with ha | ha
  · exact thin_bound G hs A B ha a
  · have x := card_bound G A B
    nlinarith [mul_nonneg (show 0 ≤ (B.card:ℤ) by positivity) (show 0 ≤ 1-(A.card:ℤ) by omega)]

theorem class_score (G : P → L → Prop) (r : P → I) (Q : I → L → Prop)
    (A : Finset P) (B : Finset L) (i : I) :
    score G (fun p l => Q (r p) l) (fiber A r i) B =
    gain G (fiber A r i) (B.filter (Q i)) := by
  rw [score,gain_sum]
  apply sum_congr rfl; intro p hp
  have hi : r p = i := (mem_filter.mp hp).2
  simp [sum_filter, weight, hi]

/-- Remove every nonsingleton row type. Its entire rectangle costs at most
three, even when it sees only one column. Singleton rows are kept exactly. -/
theorem peel_classes (G : P → L → Prop) (hs : NoSquare G) (r : P → I) (Q : I → L → Prop)
    (A : Finset P) (B : Finset L) (types : Finset I)
    (maps : ∀ p ∈ A, r p ∈ types) (small : ∀ i ∈ types, (fiber A r i).card ≤ 3) :
    ∃ A' ⊆ A, A'.card ≤ types.card ∧
      score G (fun p l => Q (r p) l) A B ≤
        3*((types.card:ℤ)-A'.card) + score G (fun p l => Q (r p) l) A' B := by
  classical
  let M := types.filter (fun i => 2 ≤ (fiber A r i).card)
  let U := A.filter (fun p => r p ∉ M)
  let Q' := fun p l => Q (r p) l
  let v := fun p => ∑ l ∈ B, weight G Q' p l
  have part := sum_fiberwise_of_maps_to maps v
  have hm : M ⊆ types := filter_subset _ _
  have cap (i : I) (hi : i ∈ M) : (∑ p ∈ fiber A r i, v p) ≤ 3 := by
    change score G (fun p l => Q (r p) l) _ B ≤ 3
    rw [class_score]
    exact thin_bound G hs _ _ (mem_filter.mp hi).2 (small _ (hm hi))
  have outside : (∑ i ∈ types \ M, ∑ p ∈ fiber A r i, v p) = ∑ p ∈ U, v p := by
    have mpU (p : P) (hp : p ∈ U) : r p ∈ types \ M :=
      mem_sdiff.mpr ⟨maps _ (mem_filter.mp hp).1, (mem_filter.mp hp).2⟩
    rw [← sum_fiberwise_of_maps_to mpU v]
    apply sum_congr rfl; intro i hi
    apply sum_congr _ (fun _ _ => rfl)
    ext p; simp [fiber,U]; grind
  have single : Set.InjOn r ↑U := by
    intro p hp p' hp' he
    by_contra ne
    have hpA := (mem_filter.mp hp).1
    have hpA' := (mem_filter.mp hp').1
    have big : 1 < (fiber A r (r p)).card :=
      one_lt_card.mpr ⟨p, by simp [fiber,hpA], p', by simp [fiber,hpA',he], ne⟩
    exact (mem_filter.mp hp).2 (mem_filter.mpr ⟨maps _ hpA,big⟩)
  have subset : U.image r ⊆ types \ M := by
    intro i hi; obtain ⟨p,hp,rfl⟩ := mem_image.mp hi
    exact mem_sdiff.mpr ⟨maps _ (mem_filter.mp hp).1,(mem_filter.mp hp).2⟩
  have count := card_le_card subset
  rw [card_image_of_injOn single,card_sdiff_of_subset hm] at count
  have counted := card_le_card hm
  have split := sum_sdiff hm (f:=fun i => ∑ p ∈ fiber A r i, v p)
  rw [outside] at split
  change (∑ i ∈ types, ∑ p ∈ fiber A r i, v p) = ∑ p ∈ A, v p at part
  have mBound := sum_le_sum (s:=M) (g:=fun _ => (3:ℤ)) cap
  simp only [sum_const,nsmul_eq_mul] at mBound
  refine ⟨U,filter_subset _ _,by omega,?_⟩
  change (∑ p ∈ A, v p) ≤ _ + ∑ p ∈ U, v p
  omega

/-- Bound the entire residual by the number of its live types, grouping in
both directions and then applying the square-free incidence bound. -/
theorem residual_types (G : P → L → Prop) (hs : NoSquare G) (H : I → J → Prop)
    (r : P → I) (c : L → J) (A : Finset P) (B : Finset L) (X : Finset I) (Y : Finset J)
    (rx : ∀ p ∈ A, r p ∈ X) (cy : ∀ l ∈ B, c l ∈ Y)
    (sr : ∀ i ∈ X, (fiber A r i).card ≤ 3) (sc : ∀ j ∈ Y, (fiber B c j).card ≤ 3)
    (limit : X.card ≤ 28) :
    score G (fun p l => H (r p) (c l)) A B ≤ 3*((X.card:ℤ)+Y.card) := by
  obtain ⟨U,_,hu,hrow⟩ := peel_classes G hs r (fun i l => H i (c l)) A B X rx sr
  have sq : NoSquare (fun l p => G p l) := fun l m p z a b h k => (hs p z l m a h b k).symm
  obtain ⟨V,_,hv,hcol⟩ := peel_classes (fun l p => G p l) sq c (fun j p => H (r p) j) B U Y cy sc
  have tr (S : Finset P) (T : Finset L) :
      score (fun l p => G p l) (fun l p => H (r p) (c l)) T S = score G (fun p l => H (r p) (c l)) S T :=
    score_transpose _ _ S T
  rw [tr,tr] at hcol
  have rem := (score_le_edges G (fun p l => H (r p) (c l)) U V).trans
    (singleton_edges G hs U V (hu.trans limit))
  linarith

/-- An alternative residual bound charges three per predicted type pair. -/
theorem residual_edges (G : P → L → Prop) (hs : NoSquare G) (H : I → J → Prop)
    (r : P → I) (c : L → J) (A : Finset P) (B : Finset L) (X : Finset I) (Y : Finset J)
    (rx : ∀ p ∈ A, r p ∈ X) (cy : ∀ l ∈ B, c l ∈ Y)
    (sr : ∀ i ∈ X, (fiber A r i).card ≤ 3) (sc : ∀ j ∈ Y, (fiber B c j).card ≤ 3) :
    score G (fun p l => H (r p) (c l)) A B ≤ 3 * edges H X Y := by
  classical
  let w := weight G (fun p l => H (r p) (c l))
  have block (i : I) (hi : i ∈ X) (j : J) (hj : j ∈ Y) :
      (∑ p ∈ fiber A r i, ∑ l ∈ fiber B c j, w p l) ≤ 3 * hit H i j := by
    by_cases h : H i j
    · have eq : (∑ p ∈ fiber A r i, ∑ l ∈ fiber B c j, w p l) =
          gain G (fiber A r i) (fiber B c j) := by
        rw [gain_sum]; apply sum_congr rfl; intro p hp; apply sum_congr rfl; intro l hl
        simp [w, weight, (mem_filter.mp hp).2, (mem_filter.mp hl).2, h]
      rw [eq]; simpa [hit,h] using small_block G hs _ _ (sr i hi) (sc j hj)
    · have eq (p : P) (hp : p ∈ fiber A r i) (l : L) (hl : l ∈ fiber B c j) : w p l = 0 := by
        simp [w, weight, (mem_filter.mp hp).2, (mem_filter.mp hl).2, h]
      simp [sum_eq_zero (fun p hp => sum_eq_zero (eq p hp)),hit,h]
  have bounded := sum_le_sum (s:=X) (fun i hi => sum_le_sum (s:=Y) (fun j hj => block i hi j hj))
  simp_rw [sum_comm (s:=Y) (t:=fiber A r _), fiber, sum_fiberwise_of_maps_to cy, sum_fiberwise_of_maps_to rx] at bounded
  simpa only [score, w, edges, Finset.mul_sum] using bounded

#print axioms residual_types
#print axioms residual_edges
end GainGeometry
