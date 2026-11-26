import PEqualNP.SixSharing.ThreeIntersectionsFormula

/-! Circuit-to-formula simulation from a cover by bipartite disjoint-biclique graphs.
We use the project's zero-set model. Rectangles and meets are free; joins cost one. -/
namespace SparseSharing

open Set TwoIntersections ThreeIntersectionsFormula

/-- Topologically ordered paid joins with arbitrary free meets and reusable wires. -/
inductive Circuit {α : Type*} : Family α → Nat → Set α → Prop where
  | output {F z} : Free F z → Circuit F 0 z
  | gate {F a b z n} : Free F a → Free F b →
      Circuit (With F (a ∪ b)) n z → Circuit F (n+1) z

/-- At three gates the circuit syntax agrees with the project's existing definition. -/
theorem circuit_three_iff {α : Type*} {F : Family α} {z} :
    Circuit F 3 z ↔ ThreeIntersections.Three F z := by
  constructor
  · intro h
    cases h with
    | gate a b h =>
      cases h with
      | gate c d h =>
        cases h with
        | gate e f h =>
          cases h with
          | output g => exact ⟨_,_,a,b,_,_,c,d,_,_,e,f,g⟩
  · rintro ⟨a,b,ha,hb,c,d,hc,hd,e,f,he,hf,h⟩
    exact .gate ha hb (.gate hc hd (.gate he hf (.output h)))

variable {R C : Type*}

private def Agree (tests : List (Set R)) (r s : R) : Prop :=
  ∀ f ∈ tests, r ∈ f ↔ s ∈ f

private def Stable (tests : List (Set R)) (z : Set (R × C)) : Prop :=
  ∀ r s, Agree tests r s → ∀ c, (r,c) ∈ z ↔ (s,c) ∈ z

/-- A free operand has one raw row mask and a residual part determined by prior tests. -/
private def Factor (tests : List (Set R)) (z : Set (R × C)) : Prop :=
  ∃ A : Set R, ∃ t : Set (R × C), Stable tests t ∧
    ∀ r c, (r,c) ∈ z ↔ r ∈ A ∧ (r,c) ∈ t

private theorem tail_agree {f : Set R} {t : List (Set R)} {r s : R}
    (h : Agree (f::t) r s) : Agree t r s :=
  fun g hg => h g (List.mem_cons_of_mem _ hg)

private theorem free_factor {F : Family (R × C)} {tests : List (Set R)}
    (hf : ∀ z, F z → Factor tests z) {z} (hz : Free F z) : Factor tests z := by
  induction hz with
  | input h => exact hf _ h
  | meet _ _ ih jh =>
    obtain ⟨a,u,hu,eu⟩ := ih
    obtain ⟨b,v,hv,ev⟩ := jh
    refine ⟨a ∩ b,u ∩ v,?_,?_⟩
    · intro r s h c
      exact and_congr (hu r s h c) (hv r s h c)
    · intro r c
      simp only [Set.mem_inter_iff, eu, ev]
      tauto

private theorem add_mask {tests : List (Set R)} {a : Set R} {u z : Set (R × C)}
    (hu : Stable tests u) (e : ∀ r c, (r,c) ∈ z ↔ r ∈ a ∧ (r,c) ∈ u) :
    Stable (a::tests) z := by
  intro r s h c
  exact (e r c).trans ((and_congr (h a (by simp)) (hu _ _ (tail_agree h) c)).trans (e s c).symm)

private theorem test_count {F : Family (R × C)} {k z} (hc : Circuit F k z) :
    ∀ (t : List (Set R)), (∀ u, F u → Factor t u) →
      ∃ tests : List (Set R), tests.length = 2*k+1+t.length ∧ Stable tests z := by
  induction hc with
  | output hz =>
    intro t hf
    obtain ⟨a,u,hu,e⟩ := free_factor hf hz
    exact ⟨a::t, by simp; omega, add_mask hu e⟩
  | @gate F a b z n ha hb _ ih =>
    intro t hf
    obtain ⟨p,u,hu,eu⟩ := free_factor hf ha
    obtain ⟨q,v,hv,ev⟩ := free_factor hf hb
    let t' := p::q::t
    have back {r s : R} (h : Agree t' r s) : Agree t r s := tail_agree (tail_agree h)
    have hab : Stable t' (a ∪ b) := by
      intro r s h c
      apply or_congr
      · exact (eu r c).trans ((and_congr (h p (by simp [t'])) (hu _ _ (back h) c)).trans (eu s c).symm)
      · exact (ev r c).trans ((and_congr (h q (by simp [t'])) (hv _ _ (back h) c)).trans (ev s c).symm)
    obtain ⟨l,hl,hs⟩ := ih t' (by
      intro w hw
      rcases hw with hw | rfl
      · obtain ⟨x,y,hy,e⟩ := hf w hw
        exact ⟨x,y,fun r s h c => hy r s (back h) c,e⟩
      · exact ⟨univ,_,hab,by simp⟩)
    exact ⟨l, by simp [t'] at hl; omega, hs⟩

private theorem row_tests {k z} (hc : Circuit (@Rectangle R C) k z) :
    ∃ tests : List (Set R), tests.length = 2*k+1 ∧ Stable tests z := by
  apply test_count hc []
  rintro u ⟨a,b,rfl⟩
  exact ⟨a, univ ×ˢ b, fun _ _ _ _ => Iff.rfl, by simp⟩

/-- Equal nonempty labels specify disjoint complete bipartite components. -/
structure Layer (R C : Type*) where
  row : R → Option Nat
  col : C → Option Nat

def Layer.edge (L : Layer R C) (r : R) (c : C) : Prop :=
  ∃ i, L.row r = some i ∧ L.col c = some i

def zeros (layers : List (Layer R C)) : Set (R × C) :=
  {p | ∀ L ∈ layers, ¬ L.edge p.1 p.2}

private def Reads (t : List (Set R)) (a b : Option R) : Prop :=
  ∃ x y, a = some x ∧ b = some y ∧ Agree t x y

private def diff {X Y : Type*} (t : List (Set R)) (a : X → Option R) (b : Y → Option R) :
    Set (X × Y) := {p | ¬ Reads t (a p.1) (b p.2)}

private def cuts {X Y : Type*} (f : Set R) (a : X → Option R) (b : Y → Option R) :
    Set (X × Y) :=
  ({r | ∀ x, a r = some x → x ∈ f} ×ˢ {c | ∀ y, b c = some y → y ∉ f}) ∪
  ({r | ∀ x, a r = some x → x ∉ f} ×ˢ {c | ∀ y, b c = some y → y ∈ f})

private theorem cuts_one {X Y : Type*} (f : Set R) (a : X → Option R) (b : Y → Option R) :
    Formula Rectangle 1 (cuts f a b) :=
  .join (.base ⟨_,_,rfl⟩) (.base ⟨_,_,rfl⟩)

private theorem singleton_diff {X Y : Type*} (f : Set R) (a : X → Option R) (b : Y → Option R) :
    diff [f] a b = cuts f a b := by
  classical
  ext ⟨r,c⟩
  cases h : a r <;> cases j : b c <;>
    simp [diff,Reads,Agree,cuts,h,j] <;> tauto

private theorem cons_diff {X Y : Type*} (f : Set R) (t : List (Set R))
    (a : X → Option R) (b : Y → Option R) :
    diff (f::t) a b = cuts f a b ∪ diff t a b := by
  classical
  rw [← singleton_diff]
  ext ⟨r,c⟩
  cases h : a r <;> cases j : b c <;>
    simp [diff,Reads,Agree,h,j]
  exact Decidable.imp_iff_not_or

private theorem diff_formula {X Y : Type*} (t : List (Set R)) (ht : t ≠ [])
    (a : X → Option R) (b : Y → Option R) :
    Formula Rectangle (2*t.length-1) (diff t a b) := by
  induction t with
  | nil => contradiction
  | cons f t ih =>
    rcases t with _ | ⟨g,l⟩
    · rw [singleton_diff]
      exact cuts_one f a b
    · rw [cons_diff]
      have h := Formula.join (cuts_one f a b) (ih (by simp))
      convert h using 1
      simp
      omega

private def signature (t : List (Set R)) (r : R) : Set (Set R) :=
  {f | f ∈ t ∧ r ∈ f}

private theorem key_iff (t : List (Set R)) (r s : R) :
    signature t r = signature t s ↔ Agree t r s := by
  constructor
  · intro h f hf
    have := Set.ext_iff.mp h f
    simpa [signature,hf] using this
  · intro h
    ext f
    by_cases hf : f ∈ t
    · simpa [signature,hf] using h f hf
    · simp [signature,hf]

private noncomputable def representative (t : List (Set R)) (r : R) : R :=
  (fun q : Set.range (signature t) => q.property.choose) ⟨signature t r, r, rfl⟩

private theorem rep_agrees (t : List (Set R)) (r : R) : Agree t (representative t r) r :=
  (key_iff _ _ _).mp (Classical.choose_spec (show ∃ s, signature t s = signature t r from ⟨r,rfl⟩))

private theorem rep_eq (t : List (Set R)) {r s : R} (h : Agree t r s) :
    representative t r = representative t s :=
  congrArg (fun q : Set.range (signature t) => q.property.choose)
    (Subtype.ext ((key_iff _ _ _).mpr h))

private theorem code_layer (t : List (Set R)) (L : Layer R C) :
    ∃ (a : R → Option R) (b : C → Option R), ∀ r c,
      L.edge (representative t r) c ↔ Reads t (a r) (b c) := by
  classical
  let left (r : R) := L.row (representative t r)
  let code (i : Nat) : Option R :=
    if h : ∃ r, left r = some i then some h.choose else none
  have sound {i : Nat} {x : R} (h : code i = some x) : left x = some i := by
    dsimp only [code] at h
    split at h
    next yes => cases h; exact yes.choose_spec
    next => contradiction
  have complete {i : Nat} (h : ∃ r, left r = some i) : ∃ x, code i = some x := by
    exact ⟨h.choose, by simp [code,h]⟩
  refine ⟨fun r => (left r).bind code, fun c => (L.col c).bind code, ?_⟩
  intro r c
  constructor
  · rintro ⟨i,hr,hc⟩
    change left r = some i at hr
    obtain ⟨x,hx⟩ := complete ⟨r,hr⟩
    exact ⟨x,x,by simp [hr,hx],by simp [hc,hx],fun _ _ => Iff.rfl⟩
  · rintro ⟨x,y,hx,hy,hxy⟩
    cases hr : left r with
    | none => simp [hr] at hx
    | some i =>
      cases hc : L.col c with
      | none => simp [hc] at hy
      | some j =>
        have hi := sound (by simpa [hr] using hx : code i = some x)
        have hj := sound (by simpa [hc] using hy : code j = some y)
        have eqL : left x = left y := congrArg L.row (rep_eq t hxy)
        have hij := hi.symm.trans (eqL.trans hj)
        exact ⟨i,hr,hc.trans hij.symm⟩

private def repZeros (t : List (Set R)) (layers : List (Layer R C)) : Set (R × C) :=
  {p | (representative t p.1, p.2) ∈ zeros layers}

private theorem layers_formula (t : List (Set R)) (ht : t ≠ []) (ls : List (Layer R C)) :
    Formula Rectangle (ls.length * (2*t.length-1)) (repZeros t ls) := by
  induction ls with
  | nil =>
    have e : repZeros t ([] : List (Layer R C)) = univ ×ˢ univ := by ext ⟨r,c⟩; simp [repZeros,zeros]
    rw [e]
    simpa using Formula.base (show Rectangle (univ ×ˢ univ : Set (R × C)) from ⟨_,_,rfl⟩)
  | cons L ls ih =>
    obtain ⟨a,b,h⟩ := code_layer t L
    have e : repZeros t (L::ls) = diff t a b ∩ repZeros t ls := by
      ext ⟨r,c⟩
      simp [repZeros,zeros,diff,h]
    rw [e]
    rw [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm (ls.length * _) _]
    exact Formula.meet (diff_formula t ht a b) ih

/-- A circuit with k paid gates on a graph covered by t disjoint-biclique
layers has a formula of cost t(4k+1). Smaller formulas can be used when available. -/
theorem cover_simulation (ls : List (Layer R C)) {k : Nat}
    (h : Circuit Rectangle k (zeros ls)) :
    Formula Rectangle (ls.length * (4*k+1)) (zeros ls) := by
  obtain ⟨t,ht,hs⟩ := row_tests h
  have hn : t ≠ [] := by intro e; simp [e] at ht
  have e : repZeros t ls = zeros ls := by
    ext ⟨r,c⟩
    exact hs _ _ (rep_agrees t r) c
  have hd : 2*t.length-1 = 4*k+1 := by omega
  simpa only [e,hd] using layers_formula t hn ls

#print axioms SparseSharing.cover_simulation
end SparseSharing
