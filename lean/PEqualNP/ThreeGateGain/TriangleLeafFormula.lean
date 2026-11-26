import PEqualNP.ThreeGateGain.ParallelCenters

/-! A read-once tree of paid intersections and free unions. The raw signals are
the same pairs of star selections as in the parallel projective-plane model. -/
namespace TriangleLeafFormula

open Configuration PlaneParallel

inductive Formula (P L : Type*) where
  | raw (s : Arm P L)
  | join (a b : Formula P L)
  | meet (a b : Formula P L)

namespace Formula
variable {P L : Type*}

def eval : Formula P L → P → L → Prop
  | .raw s, p, l => s.eval p l
  | .join a b, p, l => a.eval p l ∨ b.eval p l
  | .meet a b, p, l => a.eval p l ∧ b.eval p l

def cost : Formula P L → ℕ
  | .raw _ => 0
  | .join a b => a.cost + b.cost
  | .meet a b => a.cost + b.cost + 1

/-- Zero these row/column signatures at all leaves, without changing the tree. -/
def trim (R : P → Prop) (C : L → Prop) : Formula P L → Formula P L
  | .raw s => .raw ⟨{p | p ∈ s.points ∧ ¬R p}, {l | l ∈ s.lines ∧ ¬C l}⟩
  | .join a b => .join (a.trim R C) (b.trim R C)
  | .meet a b => .meet (a.trim R C) (b.trim R C)

@[simp] theorem trim_cost (f : Formula P L) (R : P → Prop) (C : L → Prop) :
    (f.trim R C).cost = f.cost := by
  induction f <;> simp_all [trim,cost]

private theorem trim_lower (f : Formula P L) (R : P → Prop) (C : L → Prop)
    {p p' : P} {l l' : L} (hp : p=p' ∨ R p) (hl : l=l' ∨ C l) :
    (f.trim R C).eval p l → f.eval p' l' := by
  induction f with
  | raw a =>
    rintro (⟨h,n⟩ | ⟨h,n⟩)
    · exact Or.inl ((hp.resolve_right n) ▸ h)
    · exact Or.inr ((hl.resolve_right n) ▸ h)
  | join a b ha hb => exact Or.imp ha hb
  | meet a b ha hb => exact fun h => ⟨ha h.1,hb h.2⟩

private theorem trim_retains (f : Formula P L) (R : P → Prop) (C : L → Prop)
    {p : P} {l : L} (hp : ¬R p) (hl : ¬C l) : f.eval p l → (f.trim R C).eval p l := by
  induction f with
  | raw a => exact Or.imp (fun h => ⟨h,hp⟩) (fun h => ⟨h,hl⟩)
  | join a b ha hb => exact Or.imp ha hb
  | meet a b ha hb => exact fun h => ⟨ha h.1,hb h.2⟩

/-- A zero signature is below every other signature, so in a graph with a
zero in every row and column it yields an empty row or column. -/
theorem trim_eval (f : Formula P L) (R : P → Prop) (C : L → Prop)
    (zeroRow : ∀ p, ∃ l, ¬f.eval p l) (zeroCol : ∀ l, ∃ p, ¬f.eval p l)
    (p : P) (l : L) :
    (f.trim R C).eval p l ↔ f.eval p l ∧ ¬R p ∧ ¬C l := by
  constructor
  · intro h
    refine ⟨trim_lower f R C (.inl rfl) (.inl rfl) h, ?_, ?_⟩
    · intro hp
      obtain ⟨p',n⟩ := zeroCol l
      exact n (trim_lower f R C (Or.inr hp) (Or.inl rfl) h)
    · intro hl
      obtain ⟨l',n⟩ := zeroRow p
      exact n (trim_lower f R C (Or.inl rfl) (Or.inr hl) h)
  · rintro ⟨h,hp,hl⟩
    exact trim_retains f R C hp hl h

/-- Every erased positive cell has a unique positive in its row or its column.
Several erased cells may share their other endpoint. -/
def HasLeafEnds (f : Formula P L) (erase : P → L → Prop) : Prop :=
  ∀ p l, f.eval p l → erase p l →
    (∀ j, f.eval p j → j=l) ∨ (∀ i, f.eval i l → i=p)

theorem erase_leaf_ends (f : Formula P L) (erase : P → L → Prop)
    (zeroRow : ∀ p, ∃ l, ¬f.eval p l) (zeroCol : ∀ l, ∃ p, ¬f.eval p l)
    (leaves : f.HasLeafEnds erase) :
    ∃ R C, (f.trim R C).cost=f.cost ∧
      ∀ p l, (f.trim R C).eval p l ↔ f.eval p l ∧ ¬erase p l := by
  let R (p : P) := ∃ l, f.eval p l ∧ erase p l ∧ ∀ j, f.eval p j → j=l
  let C (l : L) := ∃ p, f.eval p l ∧ erase p l ∧ ∀ i, f.eval i l → i=p
  refine ⟨R,C,trim_cost ..,?_⟩
  intro p l
  rw [trim_eval f R C zeroRow zeroCol]
  constructor
  · rintro ⟨h,nr,nc⟩
    refine ⟨h,fun e => ?_⟩
    rcases leaves p l h e with unique | unique
    · exact nr ⟨l,h,e,unique⟩
    · exact nc ⟨p,h,e,unique⟩
  · rintro ⟨h,n⟩
    refine ⟨h,?_,?_⟩
    · rintro ⟨j,_,e,u⟩
      exact n ((u l h).symm ▸ e)
    · rintro ⟨i,_,e,u⟩
      exact n ((u p h).symm ▸ e)
end Formula

section Geometry
variable {P L : Type*} [Membership P L] [ProjectivePlane P L]

/-- A pair of distinct points on the opposite line, with the two joins to O. -/
structure Wedge (o : P) (h : L) where
  a : P
  b : P
  u : L
  v : L
  ab : a ≠ b
  ah : a ∈ h
  bh : b ∈ h
  ou : o ∈ u
  au : a ∈ u
  ov : o ∈ v
  bv : b ∈ v

def clause (o : P) (h : L) : Formula P L :=
  .raw ⟨{p | p∈h},{l | o∈l}⟩

def Wedge.arms {o : P} {h : L} (w : Wedge o h) : Formula P L :=
  .meet (clause w.a w.v) (clause w.b w.u)

def Wedge.center {o : P} {h : L} (w : Wedge o h) (p : P) (l : L) : Prop :=
  p=o ∨ p=w.a ∨ p=w.b ∨ l=h ∨ l=w.u ∨ l=w.v

/-- The two paid intersections for one triangle give exactly the flags incident
to its three vertices or three sides. -/
theorem triangle {o : P} {h : L} (away : o∉h) (w : Wedge o h) (p : P) (l : L) :
    ((Formula.meet (clause o h) w.arms).eval p l) ↔ p∈l ∧ w.center p l := by
  have uh : w.u ≠ h := fun eq => away (eq ▸ w.ou)
  have vh : w.v ≠ h := fun eq => away (eq ▸ w.ov)
  have av : w.a ∉ w.v := fun a =>
    ((Nondegenerate.eq_or_eq w.ah w.bh a w.bv).resolve_left w.ab) |>.symm |> vh
  have uv : w.u ≠ w.v := fun eq => av (eq ▸ w.au)
  have oa : o ≠ w.a := fun eq => away (eq.symm ▸ w.ah)
  have ob : o ≠ w.b := fun eq => away (eq.symm ▸ w.bh)
  have pA (hp : p∈h) (hu : p∈w.u) : p=w.a :=
    (Nondegenerate.eq_or_eq hp w.ah hu w.au).resolve_right uh.symm
  have pB (hp : p∈h) (hv : p∈w.v) : p=w.b :=
    (Nondegenerate.eq_or_eq hp w.bh hv w.bv).resolve_right vh.symm
  have pO (hu : p∈w.u) (hv : p∈w.v) : p=o :=
    (Nondegenerate.eq_or_eq hu w.ou hv w.ov).resolve_right uv
  have lH (ha : w.a∈l) (hb : w.b∈l) : l=h :=
    (Nondegenerate.eq_or_eq ha hb w.ah w.bh).resolve_left w.ab
  have lU (ho : o∈l) (ha : w.a∈l) : l=w.u :=
    (Nondegenerate.eq_or_eq ho ha w.ou w.au).resolve_left oa
  have lV (ho : o∈l) (hb : w.b∈l) : l=w.v :=
    (Nondegenerate.eq_or_eq ho hb w.ov w.bv).resolve_left ob
  change (p∈h ∨ o∈l) ∧ (p∈w.v ∨ w.a∈l) ∧ (p∈w.u ∨ w.b∈l) ↔ _
  unfold Wedge.center
  have ha := w.ah
  have hb := w.bh
  have hu := w.ou
  have hv := w.ov
  have hau := w.au
  have hbv := w.bv
  grind

/-- A free union of pair intersections, with an empty raw input at the end. -/
def pairUnion {o : P} {h : L} : List (Wedge o h) → Formula P L
  | [] => .raw ⟨∅,∅⟩
  | w::ws => .join w.arms (pairUnion ws)

omit [ProjectivePlane P L] in
private theorem pairUnion_eval {o : P} {h : L} (ws : List (Wedge o h)) (p : P) (l : L) :
    (pairUnion ws).eval p l ↔ ∃ w∈ws, w.arms.eval p l := by
  induction ws with
  | nil => simp [pairUnion,Formula.eval,Arm.eval]
  | cons w ws ih => simp [pairUnion,Formula.eval,ih]

omit [ProjectivePlane P L] in
private theorem pairUnion_cost {o : P} {h : L} (ws : List (Wedge o h)) :
    (pairUnion ws).cost = ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [pairUnion,Formula.cost,Wedge.arms,clause,ih,Nat.add_comm]

/-- Only one copy of the common clause is needed, regardless of overlaps
between the pairs. The formula syntax has no shared paid subtrees. -/
def factored {o : P} {h : L} (ws : List (Wedge o h)) : Formula P L :=
  .meet (clause o h) (pairUnion ws)

omit [ProjectivePlane P L] in
theorem factored_cost {o : P} {h : L} (ws : List (Wedge o h)) :
    (factored ws).cost = ws.length+1 := by simp [factored,Formula.cost,clause,pairUnion_cost]

def rowCenter (o : P) (h : L) (p : P) := p=o ∨ p∈h
def colCenter (o : P) (h : L) (l : L) := l=h ∨ o∈l
def core (o : P) (h : L) (p : P) (l : L) := p∈l ∧ (rowCenter o h p ∨ colCenter o h l)

def Covers {o : P} {h : L} (ws : List (Wedge o h)) : Prop :=
  ∀ p : P, p∈h → ∃ w∈ws, p=w.a ∨ p=w.b

/-- Exact common-clause construction. A paired endpoint can occur more than
once, allowing an odd number of points on the opposite line. -/
theorem factored_eval {o : P} {h : L} (away : o∉h) (ws : List (Wedge o h))
    (used : ws ≠ []) (allPts : Covers ws) (p : P) (l : L) :
    (factored ws).eval p l ↔ core o h p l := by
  have expand : (factored ws).eval p l ↔
      ∃ w∈ws, p∈l ∧ w.center p l := by
    change (clause o h).eval p l ∧ (pairUnion ws).eval p l ↔ _
    rw [pairUnion_eval]
    constructor
    · rintro ⟨common,w,hw,hw'⟩
      exact ⟨w,hw,(triangle away w p l).mp ⟨common,hw'⟩⟩
    · rintro ⟨w,hw,hc⟩
      have both := (triangle away w p l).mpr hc
      exact ⟨both.1,w,hw,both.2⟩
  rw [expand]
  obtain ⟨w₀,hw₀⟩ := List.exists_mem_of_ne_nil ws used
  constructor
  · rintro ⟨w,_,inc,ctr⟩
    refine ⟨inc,?_⟩
    rcases ctr with po|pa|pb|lh|lu|lv
    · exact Or.inl (.inl po)
    · exact Or.inl (.inr (pa.symm ▸ w.ah))
    · exact Or.inl (.inr (pb.symm ▸ w.bh))
    · exact Or.inr (.inl lh)
    · exact Or.inr (.inr (lu.symm ▸ w.ou))
    · exact Or.inr (.inr (lv.symm ▸ w.ov))
  · rintro ⟨inc, (po|ph) | (lh|ol)⟩
    · exact ⟨w₀,hw₀,inc,Or.inl po⟩
    · obtain ⟨w,hw,e|e⟩ := allPts p ph
      · exact ⟨w,hw,inc,Or.inr (.inl e)⟩
      · exact ⟨w,hw,inc,Or.inr (.inr (.inl e))⟩
    · exact ⟨w₀,hw₀,inc,Or.inr (.inr (.inr (.inl lh)))⟩
    · have diff : l≠h := fun e => away (e ▸ ol)
      obtain ⟨z,⟨zl,zh⟩,_⟩ := HasPoints.existsUnique_point P L l h diff
      have oz : o≠z := fun e => away (e.symm ▸ zh)
      obtain ⟨w,hw,e|e⟩ := allPts z zh
      · have eq := (Nondegenerate.eq_or_eq ol zl w.ou (e.symm ▸ w.au)).resolve_left oz
        exact ⟨w,hw,inc,Or.inr (.inr (.inr (.inr (.inl eq))))⟩
      · have eq := (Nondegenerate.eq_or_eq ol zl w.ov (e.symm ▸ w.bv)).resolve_left oz
        exact ⟨w,hw,inc,Or.inr (.inr (.inr (.inr (.inr eq))))⟩

/-- In the core, a point outside all row centers has just one possible
incident column, and dually for a line outside all column centers. -/
theorem core_leaf_ends {o : P} {h : L} {p : P} {l : L} (e : core o h p l)
    (outside : ¬(rowCenter o h p ∧ colCenter o h l)) :
    (∀ j, core o h p j → j=l) ∨ (∀ i, core o h i l → i=p) := by
  by_cases pr : rowCenter o h p
  · have lc : ¬ colCenter o h l := fun z => outside ⟨pr,z⟩
    right
    have get (x : P) (cx : core o h x l) : x∈h := by
      rcases cx.2.resolve_right lc with eq|inc
      · exact (lc (.inr (eq ▸ cx.1))).elim
      · exact inc
    intro i hi
    exact (Nondegenerate.eq_or_eq hi.1 e.1 (get i hi) (get p e)).resolve_right
      (fun z => lc (.inl z))
  · left
    have get (j : L) (cx : core o h p j) : o∈j := by
      rcases cx.2.resolve_left pr with eq|inc
      · exact (pr (.inr (eq ▸ cx.1))).elim
      · exact inc
    intro j hj
    exact (Nondegenerate.eq_or_eq hj.1 (get j hj) e.1 (get l e)).resolve_left
      (fun z => pr (.inl z))

/-- Joint scope: actual star selections on the triangle constructor, all
retained and erased entries, and exactly the original number of paid gates. -/
theorem trimmed_factored_core {o : P} {h : L} (away : o∉h) (ws : List (Wedge o h))
    (used : ws ≠ []) (allPts : Covers ws) (erase : P → L → Prop)
    (unblocked : ∀ p l, p∈l → erase p l → ¬(rowCenter o h p ∧ colCenter o h l)) :
    ∃ R C, ((factored ws).trim R C).cost = ws.length+1 ∧
      ∀ p l, ((factored ws).trim R C).eval p l ↔ core o h p l ∧ ¬erase p l := by
  have ev := factored_eval away ws used allPts
  obtain ⟨R,C,cost,run⟩ := (factored ws).erase_leaf_ends erase
    (fun p => by
      obtain ⟨l,miss⟩ := Nondegenerate.exists_line (L:=L) p
      exact ⟨l,fun hit => miss ((ev p l).mp hit).1⟩)
    (fun l => by
      obtain ⟨p,miss⟩ := Nondegenerate.exists_point (P:=P) l
      exact ⟨p,fun hit => miss ((ev p l).mp hit).1⟩)
    (fun p l hit del => by
      have c := (ev p l).mp hit
      rcases core_leaf_ends c (unblocked p l c.1 del) with row|col
      · exact Or.inl (fun j k => row j ((ev p j).mp k))
      · exact Or.inr (fun i k => col i ((ev i l).mp k)))
  exact ⟨R,C,cost.trans (factored_cost ws),fun p l => (run p l).trans (and_congr_left' (ev p l))⟩

end Geometry

#print axioms Formula.erase_leaf_ends
#print axioms triangle
#print axioms factored_eval
#print axioms factored_cost
#print axioms trimmed_factored_core
end TriangleLeafFormula
