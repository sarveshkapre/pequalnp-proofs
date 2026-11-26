import PEqualNP.ThreeGateGain.GainFrameBridge

namespace GainFrameBridge
open GainFinite TriangleOptimality Finset

def word (h : Host) (rl : Leaves) (i : WordType) :=
  rowMask h i &&& ((2^27-1) ^^^ unionMask h rl)

def indices (h : Host) (rl cl : Leaves) : Leaves :=
  ((List.finRange 27).filter (fun i => !(unionMask h cl).testBit i.val)).filter
    ((· != 0) ∘ word h rl)

theorem live_map (h : Host) (rl cl : Leaves) :
    liveRows h rl cl = (indices h rl cl).map (word h rl) := by
  exact List.filter_map

theorem indices_nodup (h : Host) (rl cl : Leaves) : (indices h rl cl).Nodup :=
  ((List.nodup_finRange _).filter _).filter _

@[simp] theorem word_bit (h : Host) (rl : Leaves) (i j : WordType) :
    (word h rl i).testBit j.val = true ↔ hostEdge h i j = true ∧
      ∀ k ∈ rl, hostEdge h k j = false := by
  simp only [word,Nat.testBit_and,Nat.testBit_xor,Nat.testBit_two_pow_sub_one,
    j.isLt,decide_true,Bool.true_xor,Bool.and_eq_true,Bool.not_eq_true',row_bit,
    Bool.eq_false_iff,ne_eq,union_bit]
  grind

theorem fold_bits (xs : List Nat) (j : WordType) :
    (xs.foldr (· ||| ·) 0).testBit j.val = true ↔ ∃ w ∈ xs, w.testBit j.val = true := by
  induction xs with
  | nil => simp
  | cons b bs ih => simp [Nat.testBit_or,ih]

def R (h : Host) (rl cl : Leaves) := (indices h rl cl).toFinset
def C (h : Host) (rl cl : Leaves) :=
  (positions ((liveRows h rl cl).foldr (· ||| ·) 0)).toFinset

theorem col_mem (h : Host) (rl cl : Leaves) (j : WordType) :
    j ∈ C h rl cl ↔ ∃ i ∈ indices h rl cl, (word h rl i).testBit j.val = true := by
  simp [C,fold_bits,live_map]

theorem cover_live (h : Host) (rl cl : Leaves) (i j : WordType)
    (rOK : ∀ v ∈ cl, ¬ hostEdge h i v = true)
    (cOK : ∀ u ∈ rl, ¬ hostEdge h u j = true)
    (edge : hostEdge h i j = true) : i ∈ R h rl cl ∧ j ∈ C h rl cl := by
  have wb := (word_bit h rl i j).mpr ⟨edge, fun u hu => Bool.eq_false_iff.mpr (cOK u hu)⟩
  have rz : (unionMask h cl).testBit i.val = false := by
    apply Bool.eq_false_iff.mpr; intro a
    obtain ⟨v,hv,e⟩ := (union_bit h cl i).mp a
    exact rOK v hv ((edge_symm h i v).trans e)
  have ri : i ∈ indices h rl cl := by
    simp [indices,rz,Function.comp_def, witness_nonzero _ j wb]
  exact ⟨List.mem_toFinset.mpr ri,(col_mem h rl cl j).mpr ⟨i,ri,wb⟩⟩

theorem residual_score (h : Host) (rl cl : Leaves) :
    min (3*(((R h rl cl).card:ℤ)+(C h rl cl).card))
      (3*edges (fun i j => hostEdge h i j = true) (R h rl cl) (C h rl cl)) ≤ residual h rl cl := by
  classical
  let V := C h rl cl
  let X := R h rl cl
  have nc : V.card = size27 ((liveRows h rl cl).foldr (· ||| ·) 0) := positions_count _
  have nr : X.card = (liveRows h rl cl).length := by
    rw [live_map,List.length_map]
    exact List.toFinset_card_of_nodup (indices_nodup h rl cl)
  have pos (i : WordType) : V.filter (fun j => hostEdge h i j = true) ⊆
      (positions (word h rl i)).toFinset := by
    intro j hj
    obtain ⟨jc,he⟩ := Finset.mem_filter.mp hj
    obtain ⟨a,_,ha⟩ := (col_mem h rl cl j).mp jc
    exact List.mem_toFinset.mpr ((positions_mem _ _).mpr
      ((word_bit h rl i j).mpr ⟨he,((word_bit h rl a j).mp ha).2⟩))
  have row (i : WordType) : (∑ j ∈ V, hit (fun i j => hostEdge h i j = true) i j)
      ≤ (size27 (word h rl i):ℤ) := by
    have e := Finset.card_le_card (pos i)
    rw [positions_count] at e
    calc
      _ = ∑ j ∈ V, (if hostEdge h i j = true then (1:ℤ) else 0) := by
        apply sum_congr rfl; intro j _
        by_cases yes : hostEdge h i j = true <;> simp [hit,yes]
      _ = ((V.filter (fun j => hostEdge h i j = true)).card:ℤ) := by
        exact Finset.sum_boole _ _
      _ ≤ _ := Int.ofNat_le.mpr e
  have ne : edges (fun i j => hostEdge h i j = true) X V ≤ ((liveRows h rl cl).map size27).sum := by
    calc
      _ ≤ ∑ i ∈ X, (size27 (word h rl i):ℤ) := sum_le_sum (fun i _ => row i)
      _ = ((liveRows h rl cl).map size27).sum := by
        rw [live_map,List.map_map]
        have hx : X = (indices h rl cl).toFinset := by ext a; simp [X,R]
        rw [hx]
        have nr := List.sum_toFinset (size27 ∘ word h rl) (indices_nodup h rl cl)
        have integer := congrArg (fun n : ℕ => (n:ℤ)) nr
        simpa only [Nat.cast_sum,Function.comp_apply] using integer
  change min (3*((X.card:ℤ)+V.card)) (3*edges _ X V) ≤ _
  rw [nc,nr]
  unfold GainFinite.residual
  simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_min,Nat.cast_add]
  omega

end GainFrameBridge
