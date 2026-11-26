import Mathlib.Tactic

/-! Partition the 64 column-side assignments by the output of each row of the
shared three-gate shape. A nonempty block contributes one possible column. -/
namespace FiveRowPartition
abbrev Code := BitVec 6
abbrev Block := BitVec 64
def bit (h : Block) (c : Code) : Bool := h.getLsbD c.toNat

def shared (v : Code) : Bool :=
  let s := v.getLsbD 0 || v.getLsbD 1
  (v.getLsbD 2 || (v.getLsbD 3 && s)) && (v.getLsbD 4 || (v.getLsbD 5 && s))

private def stripes : Fin 6 → Block :=
  ![0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,
    0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]
private theorem stripe_bit : ∀ (j : Fin 6) (c : Code), bit (stripes j) c = c.getLsbD j.val := by
  decide +kernel
private def term (r : Code) (j : Fin 6) : Block := if r.getLsbD j.val then stripes j else 0
private theorem term_bit (r c : Code) (j : Fin 6) :
    bit (term r j) c = (r.getLsbD j.val && c.getLsbD j.val) := by
  unfold term
  cases h : r.getLsbD j.val
  · simp only [Bool.false_eq_true,ite_false,Bool.false_and]; simp [bit]
  · exact stripe_bit j c
def profile (r : Code) : Block :=
  let s := term r 0 ||| term r 1
  (term r 2 ||| (term r 3 &&& s)) &&& (term r 4 ||| (term r 5 &&& s))

theorem profile_correct (r c : Code) : bit (profile r) c = shared (r &&& c) := by
  have e (i : Fin 6) := term_bit r c i
  simp only [bit] at e ⊢
  simp [profile,shared,e]

def children (b h : Block) : List Block := [b &&& h, b &&& ~~~h].filter (· != 0)
def split (bs : List Block) (h : Block) := bs.flatMap (fun b => children b h)

def Covers (bs : List Block) : Prop := ∀ c : Code, ∃ b ∈ bs, bit b c = true
def Uniform (bs hs : List Block) : Prop := ∀ b ∈ bs, ∀ x y : Code,
  bit b x = true → bit b y = true → ∀ h ∈ hs, bit h x = bit h y

private theorem bit_and (b h : Block) (c : Code) : bit (b &&& h) c = (bit b c && bit h c) := by
  simp [bit]
private theorem bit_not (h : Block) (c : Code) : bit (~~~h) c = !bit h c := by
  simp [bit, BitVec.getLsbD_not,c.isLt]
private theorem live {b : Block} {c : Code} (h : bit b c = true) : b ≠ 0 := by
  rintro rfl
  simp [bit] at h

private theorem split_covers (bs : List Block) (h : Block) (hc : Covers bs) : Covers (split bs h) := by
  intro c
  obtain ⟨b,hm,hb⟩ := hc c
  cases eq : bit h c with
  | false =>
    have hh : bit (b &&& ~~~h) c = true := by simp [bit_and, bit_not,eq,hb]
    exact ⟨_,List.mem_flatMap.mpr ⟨b,hm,by simp [children]; exact live hh⟩,hh⟩
  | true =>
    have hh : bit (b &&& h) c = true := by simp [bit_and,eq,hb]
    exact ⟨_,List.mem_flatMap.mpr ⟨b,hm,by simp [children]; exact live hh⟩,hh⟩

private theorem split_uniform (bs hs : List Block) (h : Block) (hu : Uniform bs hs) :
    Uniform (split bs h) (h :: hs) := by
  intro d hd x y hx hy q hq
  obtain ⟨b,hb,hd⟩ := List.mem_flatMap.mp hd
  have opts := (List.mem_filter.mp hd).1
  simp only [List.mem_cons,List.not_mem_nil,or_false] at opts
  rcases opts with rfl | rfl
  · have ax := Bool.and_eq_true_iff.mp ((bit_and _ _ _).symm.trans hx)
    have ay := Bool.and_eq_true_iff.mp ((bit_and _ _ _).symm.trans hy)
    rcases List.mem_cons.mp hq with rfl | old
    · exact ax.2.trans ay.2.symm
    · exact hu b hb x y ax.1 ay.1 q old
  · have ax := Bool.and_eq_true_iff.mp ((bit_and _ _ _).symm.trans hx)
    have ay := Bool.and_eq_true_iff.mp ((bit_and _ _ _).symm.trans hy)
    rcases List.mem_cons.mp hq with rfl | old
    · have xx := ax.2
      have yy := ay.2
      simp [bit_not] at xx yy
      exact xx.trans yy.symm
    · exact hu b hb x y ax.1 ay.1 q old

theorem partition_correct (todo past bs : List Block) (hc : Covers bs) (hu : Uniform bs past) :
    Covers (todo.foldl split bs) ∧ Uniform (todo.foldl split bs) (todo.reverse ++ past) := by
  induction todo generalizing past bs with
  | nil => exact ⟨hc,hu⟩
  | cons h rest ih =>
    simpa [List.reverse_cons,List.append_assoc] using ih (h::past) (split bs h)
      (split_covers bs h hc) (split_uniform bs past h hu)

theorem distinct_bound {n : Nat} (tests : List Block) (cols : Fin n → Code)
    (sep : ∀ i j, (∀ t ∈ tests, bit t (cols i) = bit t (cols j)) → i = j)
    (small : (tests.foldl split [-1]).length ≤ 22) : n ≤ 22 := by
  classical
  let bs := tests.foldl split [-1]
  have all : ∀ c : Code, bit (-1) c = true := by decide +kernel
  obtain ⟨hc,hu⟩ := partition_correct tests [] [-1]
    (fun c => ⟨_,by simp,all c⟩) (by simp [Uniform])
  have atCol (i : Fin n) : ∃ k : Fin bs.length, bit (bs.get k) (cols i) = true := by
    obtain ⟨b,hm,hb⟩ := hc (cols i)
    change b ∈ bs at hm
    obtain ⟨k,he⟩ := List.get_of_mem hm
    exact ⟨k, (congrArg (fun v => bit v (cols i)) he).trans hb⟩
  choose idx hits using atCol
  have inj : Function.Injective idx := by
    intro i j eq
    apply sep i j
    intro t ht
    have hj : bit (bs.get (idx i)) (cols j) = true := by rw [eq]; exact hits j
    exact hu _ (List.get_mem bs (idx i)) _ _ (hits i) hj t (by simpa using ht)
  have size : n ≤ bs.length := by simpa using Fintype.card_le_of_injective idx inj
  exact size.trans small
end FiveRowPartition
