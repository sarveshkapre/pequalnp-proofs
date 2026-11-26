import SixEdgeAudit

namespace SixEdge.Formula

set_option maxHeartbeats 2000000

def Denotes (v : Values) (bit : Bool) (t : Lit) : Prop := t ≠ 0 ∧ literalValue v t = bit

theorem Denotes.constant (v : Values) (one : v 1 = true) (b : Bool) : Denotes v b (if b then 1 else -1) := by
  cases b <;> simp [Denotes,literalValue,one]

theorem Denotes.neg {v : Values} {b : Bool} {t : Lit} (h : Denotes v b t) : Denotes v (!b) (-t) :=
  ⟨neg_ne_zero.mpr h.1, by rw [literal_neg_of_ne _ h.1, h.2]⟩

theorem Denotes.unit {v : Values} {t : Lit} (h : Denotes v true t) : ClauseTrue v [t] :=
  ⟨t,List.mem_cons_self,h.2⟩

theorem denote_pair {primary : Input → Bool} (v : Values) (a b : Lit) (x y : Bool) :
    Audited primary v (v 1 = true ∧ Denotes v x a ∧ Denotes v y b) (makeAnd [a,b])
      (Denotes v (x && y)) := by
  refine (audit_and primary v [a,b]).mono ?_ ?_
  · rintro ⟨one,hx,hy⟩
    refine ⟨one,?_⟩
    intro t ht
    rcases List.mem_cons.mp ht with rfl | tail
    · exact hx.1
    · rw [List.mem_singleton.mp tail]; exact hy.1
  · rintro ⟨_,hx,hy⟩ t ⟨nz,eval⟩
    refine ⟨nz,?_⟩
    simpa only [List.all_cons,List.all_nil,Bool.and_true,hx.2,hy.2] using eval

theorem denote_or_pair {primary : Input → Bool} (v : Values) (a b : Lit) (x y : Bool) :
    Audited primary v (v 1 = true ∧ Denotes v x a ∧ Denotes v y b) (makeOr [a,b])
      (Denotes v (x || y)) := by
  refine (audit_or primary v [a,b]).mono ?_ ?_
  · rintro ⟨one,hx,hy⟩
    refine ⟨one,?_⟩
    intro t ht
    rcases List.mem_cons.mp ht with rfl | tail
    · exact hx.1
    · rw [List.mem_singleton.mp tail]; exact hy.1
  · rintro ⟨_,hx,hy⟩ t ⟨nz,eval⟩
    refine ⟨nz,?_⟩
    simpa only [List.any_cons,List.any_nil,Bool.or_false,hx.2,hy.2] using eval

abbrev DenotesList (v : Values) := List.Forall₂ (Denotes v)

theorem DenotesList.nonzero {v : Values} {bs : List Bool} {ts : List Lit} (meaning : DenotesList v bs ts) :
    ∀ t ∈ ts, t ≠ 0 := by
  induction meaning with
  | nil => simp
  | cons hd _ ih =>
    intro t ht
    rcases List.mem_cons.mp ht with rfl | next
    · exact hd.1
    · exact ih t next

theorem DenotesList.any {v : Values} {bs : List Bool} {ts : List Lit} (meaning : DenotesList v bs ts) :
    ts.any (literalValue v) = bs.any id := by
  induction meaning with
  | nil => rfl
  | cons hd _ ih => simp only [List.any_cons,hd.2,ih,id_eq]

theorem DenotesList.append {v : Values} {bs cs : List Bool} {ts us : List Lit}
    (a : DenotesList v bs ts) (b : DenotesList v cs us) : DenotesList v (bs++cs) (ts++us) := by
  induction a with
  | nil => exact b
  | cons head _ ih => exact List.Forall₂.cons head ih

theorem denote_any {primary : Input → Bool} (v : Values) (values : List Bool) (ts : List Lit) :
    Audited primary v (v 1 = true ∧ DenotesList v values ts) (makeOr ts) (Denotes v (values.any id)) := by
  refine (audit_or primary v ts).mono (fun h => ⟨h.1,h.2.nonzero⟩) ?_
  rintro ⟨_,meaning⟩ t ⟨nz,eval⟩
  exact ⟨nz,eval.trans meaning.any⟩

def selectedBits (v : Values) (read : Nat → Lit) (pick : TopSelector → Lit)
    (selectors : List TopSelector) : List Bool :=
  selectors.map fun slot => literalValue v (pick slot) && literalValue v (read slot.1)

private theorem audit_selected_bits (primary : Input → Bool) (v : Values) (read : Nat → Lit)
    (pick : TopSelector → Lit) (selectors : List TopSelector) :
    Audited primary v (v 1 = true ∧ ∀ s ∈ selectors, pick s ≠ 0 ∧ read s.1 ≠ 0)
      (selectors.mapM fun s => makeAnd [pick s,read s.1])
      (DenotesList v (selectedBits v read pick selectors)) := by
  let rel (s : TopSelector) := Denotes v (literalValue v (pick s) && literalValue v (read s.1))
  have each (s : TopSelector) :
      Audited primary v ((v 1 = true ∧ ∀ s ∈ selectors, pick s ≠ 0 ∧ read s.1 ≠ 0) ∧ s ∈ selectors)
        (makeAnd [pick s,read s.1]) (rel s) := by
    apply (denote_pair _ _ _ _ _).mono ?_ (fun _ _ h => h)
    rintro ⟨⟨one,valid⟩,mem⟩
    exact ⟨one,⟨(valid s mem).1,rfl⟩,⟨(valid s mem).2,rfl⟩⟩
  have lift {ss : List TopSelector} {ts : List Lit} (h : List.Forall₂ rel ss ts) :
      DenotesList v (selectedBits v read pick ss) ts := by
    induction h with
    | nil => exact List.Forall₂.nil
    | cons head _ ih => exact List.Forall₂.cons head ih
  exact (Audited.mapM selectors each).mono id (fun _ _ h => lift h)

structure HitInputs (v : Values) (read : Nat → Lit) (leaf : Leaf) (selectors : List TopSelector)
    (input : List Nat) : Prop where
  one : v 1 = true
  selected : ∀ s ∈ selectors, s.2.1 ≠ 0 ∧ s.2.2 ≠ 0 ∧ read s.1 ≠ 0
  raw : ∀ t ∈ input.filterMap (fun n => leaf.lookup n), t ≠ 0

def decodedHit (v : Values) (line : Nat) (leaf : Leaf) (selectors : List TopSelector)
    (read : Nat → Lit) (input : List Nat) : Bool :=
  (input.contains line || (selectedBits v read (·.2.1) selectors).any id) &&
  ((input.filterMap (fun n => leaf.lookup n)).any (literalValue v) || (selectedBits v read (·.2.2) selectors).any id)

private theorem audit_centre_bit (primary : Input → Bool) (v : Values) (line : Nat)
    (leaf : Leaf) (selectors : List TopSelector) (read : Nat → Lit) (input : List Nat) :
    Audited primary v (HitInputs v read leaf selectors input)
      (topCentreLit line selectors read input)
      (Denotes v (input.contains line || (selectedBits v read (·.2.1) selectors).any id)) := by
  unfold topCentreLit
  split
  · rename_i incl
    apply Audited.pure
    intro data
    rw [incl, Bool.true_or]
    exact Denotes.constant v data.one true
  · rename_i notIncl
    have eq : input.contains line = false := Bool.eq_false_iff.mpr notIncl
    rw [eq,Bool.false_or]
    apply Audited.bind ((audit_selected_bits primary v read (·.2.1) selectors).mono
      (fun h => ⟨h.one,fun s hs => ⟨(h.selected s hs).1,(h.selected s hs).2.2⟩⟩) (fun _ _ h => h))
    intro zs
    exact (denote_any v _ zs).mono (fun h => ⟨h.1.one,h.2⟩) (fun _ _ h => h)

theorem audit_top_hit (primary : Input → Bool) (v : Values) (line : Nat) (leaf : Leaf)
    (selectors : List TopSelector) (read : Nat → Lit) (input : List Nat) :
    Audited primary v (HitInputs v read leaf selectors input) (topHit line leaf selectors read input)
      (Denotes v (decodedHit v line leaf selectors read input)) := by
  unfold topHit decodedHit
  apply Audited.bind (audit_centre_bit primary v line leaf selectors read input)
  intro c
  apply Audited.bind ((audit_selected_bits primary v read (·.2.2) selectors).mono
    (fun h => ⟨h.1.one,fun s hs => (h.1.selected s hs).2⟩) (fun _ _ h => h))
  intro ls
  let raw := input.filterMap (fun n => leaf.lookup n)
  let bits := selectedBits v read (·.2.2) selectors
  have leafOr : Audited primary v
      ((HitInputs v read leaf selectors input ∧ Denotes v (input.contains line || (selectedBits v read (·.2.1) selectors).any id) c) ∧
        DenotesList v bits ls) (makeOr (raw ++ ls))
      (Denotes v (raw.any (literalValue v) || bits.any id)) := by
    refine (denote_any v (raw.map (literalValue v) ++ bits) (raw ++ ls)).mono ?_ ?_
    · rintro ⟨⟨pre,_⟩,rel⟩
      have rawMatches : DenotesList v (raw.map (literalValue v)) raw := by
        have go (ts : List Lit) (nonzero : ∀ t ∈ ts, t ≠ 0) : DenotesList v (ts.map (literalValue v)) ts := by
          induction ts with
          | nil => exact List.Forall₂.nil
          | cons hd _ ih =>
            exact List.Forall₂.cons ⟨nonzero hd List.mem_cons_self,rfl⟩
              (ih (fun t ht => nonzero t (List.mem_cons_of_mem _ ht)))
        exact go raw pre.raw
      exact ⟨pre.one,rawMatches.append rel⟩
    · intro _ _ meaning
      simpa [List.any_append, List.any_map, Function.comp_def] using meaning
  apply Audited.bind leafOr
  intro d
  exact (denote_pair v c d _ _).mono (fun h => ⟨h.1.1.1.one,h.1.1.2,h.2⟩) (fun _ _ h => h)

def RowDenotes (v : Values) (f : Nat → Bool) (xs : List Lit) : Prop :=
  List.Forall₂ (fun k t => Denotes v (f k) t) (List.range samples.size) xs

theorem RowDenotes.get {v : Values} {f : Nat → Bool} {xs : List Lit} (h : RowDenotes v f xs)
    {k : Nat} (hk : k < samples.size) : Denotes v (f k) xs[k]! := by
  have len : xs.length = samples.size := by simpa using h.length_eq.symm
  have kx : k < xs.length := by rwa [len]
  rw [getElem!_pos xs k kx]
  simpa using List.Forall₂.get h (i := k) (by simpa) kx

def ArrayDenotes (v : Values) (length : Nat) (bits : Nat → Bool) (xs : Array Lit) : Prop :=
  xs.size = length ∧ ∀ j < length, Denotes v (bits j) xs[j]!

theorem list_to_array_denotes {v : Values} {n : Nat} {f : Nat → Bool} {xs : List Lit}
    (h : List.Forall₂ (fun j t => Denotes v (f j) t) (List.range n) xs) : ArrayDenotes v n f xs.toArray := by
  have len : xs.length = n := by simpa using h.length_eq.symm
  refine ⟨by simpa,?_⟩
  intro j hj
  have jx : j < xs.length := by rwa [len]
  have ja : j < xs.toArray.size := by simpa
  rw [getElem!_pos xs.toArray j ja]
  simpa using List.Forall₂.get h (i := j) (by simpa) jx

theorem audit_combine_samples (primary : Input → Bool) (v : Values) (dirty : Bool)
    (a b : Array Lit) (x y : Nat → Bool) :
    Audited primary v (v 1 = true ∧ ∀ k < samples.size, Denotes v (x k) a[k]! ∧ Denotes v (y k) b[k]!)
      (combineSampleValues dirty a b)
      (ArrayDenotes v samples.size (fun k => if dirty then x k && y k else x k || y k)) := by
  let pre := v 1 = true ∧ ∀ k < samples.size, Denotes v (x k) a[k]! ∧ Denotes v (y k) b[k]!
  let bit := fun k => if dirty then x k && y k else x k || y k
  have each k : Audited primary v (pre ∧ k ∈ List.range samples.size)
      ((if dirty then makeAnd else makeOr) [a[k]!,b[k]!]) (Denotes v (bit k)) := by
    have ready : (pre ∧ k ∈ List.range samples.size) →
        v 1 = true ∧ Denotes v (x k) a[k]! ∧ Denotes v (y k) b[k]! :=
      fun h => ⟨h.1.1,h.1.2 k (List.mem_range.mp h.2)⟩
    cases dirty with
    | false => exact (denote_or_pair v _ _ _ _).mono ready (fun _ _ h => h)
    | true => exact (denote_pair v _ _ _ _).mono ready (fun _ _ h => h)
  unfold combineSampleValues
  refine Audited.bind (Audited.mapM (List.range samples.size) each) (fun vals => ?_)
  exact Audited.pure _ _ _ (fun h => list_to_array_denotes h.2)

theorem audit_combine_raw (primary : Input → Bool) (v : Values) (dirty : Bool)
    (a b : Array Lit) (x y : Nat → Bool) :
    Audited primary v (v 1 = true ∧ ∀ j < 26, Denotes v (x j) a[j]! ∧ Denotes v (y j) b[j]!)
      (combineRawSupport dirty a b) (ArrayDenotes v 26 (fun j => if dirty then false else x j || y j)) := by
  let pre := v 1 = true ∧ ∀ j < 26, Denotes v (x j) a[j]! ∧ Denotes v (y j) b[j]!
  let bit := fun j => if dirty then false else x j || y j
  have each j : Audited primary v (pre ∧ j ∈ List.range 26)
      (if dirty then pure (-1) else makeOr [a[j]!,b[j]!]) (Denotes v (bit j)) := by
    cases dirty with
    | false =>
      exact (denote_or_pair v _ _ _ _).mono
        (fun h => ⟨h.1.1,h.1.2 j (List.mem_range.mp h.2)⟩) (fun _ _ h => h)
    | true => exact Audited.pure _ _ _ (fun h => Denotes.constant v h.1.1 false)
  unfold combineRawSupport
  refine Audited.bind (Audited.mapM (List.range 26) each) (fun vals => ?_)
  exact Audited.pure _ _ _ (fun h => list_to_array_denotes h.2)

def FirstActivity (active : Bool) (extra : BitVec 5) (retained on : Nat → Bool) : Prop :=
  if active then
    if extra = 0 then on 0 = true else ∃ k < 52, (!retained k && on k) = true
  else ∀ k < 52, (!retained k && on k) = false

theorem audit_first_activity (primary : Input → Bool) (v : Values) (extra : BitVec 5) (active : Bool)
    (retained values : Array Lit) (keep on : Nat → Bool) :
    Audited primary v (v 1 = true ∧ ArrayDenotes v 52 keep retained ∧ ArrayDenotes v samples.size on values ∧
        FirstActivity active extra keep on)
      (constrainFirstActivity extra active retained values)
      (ArrayDenotes v samples.size (fun k => if active then on k else false)) := by
  let pre := v 1 = true ∧ ArrayDenotes v 52 keep retained ∧ ArrayDenotes v samples.size on values ∧
    FirstActivity active extra keep on
  let bit := fun k => !keep k && on k
  have len : samples.size = 132 := by decide +kernel
  have each k : Audited primary v (pre ∧ k ∈ List.range 52)
      (makeAnd [-retained[k]!,values[k]!]) (Denotes v (bit k)) := by
    refine (denote_pair v _ _ _ _).mono ?_ (fun _ _ h => h)
    intro h
    have bound : k < 52 := List.mem_range.mp h.2
    exact ⟨h.1.1,(h.1.2.1.2 k bound).neg,h.1.2.2.1.2 k (by omega)⟩
  unfold constrainFirstActivity
  refine Audited.bind (Audited.mapM (List.range 52) each) ?_
  intro terms
  have get (same : List.Forall₂ (fun k t => Denotes v (bit k) t) (List.range 52) terms) {k} (bound : k < 52) :
      ∃ kt : k < terms.length, Denotes v (bit k) terms[k] := by
    have ht : k < terms.length := by simpa [← same.length_eq] using bound
    exact ⟨ht,by simpa using same.get (i := k) (by simp [bound]) ht⟩
  cases active with
  | true =>
    simp only [↓reduceIte]
    apply Audited.bind ((audit_require primary v .firstActivity _).mono ?_ (fun _ _ h => h))
    · intro _
      exact Audited.pure _ _ _ (fun h => h.1.1.2.2.1)
    · rintro ⟨before,same⟩
      have signal := before.2.2.2
      by_cases anchor : extra = 0
      · have bitOn : on 0 = true := by simpa [FirstActivity,anchor] using signal
        simpa only [beq_iff_eq,ite_eq_left anchor] using
          (Denotes.unit (bitOn ▸ before.2.2.1.2 0 (by omega)))
      · change (if extra = (0 : BitVec 5) then on 0 = true else ∃ k < 52, bit k = true) at signal
        rw [ite_eq_right anchor] at signal
        obtain ⟨k,bound,bitOn⟩ := signal
        obtain ⟨ht,matchBit⟩ := get same bound
        rw [show (extra == 0) = false from Bool.eq_false_iff.mpr (fun h => anchor (beq_iff_eq.mp h))]
        exact ⟨_,List.getElem_mem ht,matchBit.2.trans bitOn⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    let ready := pre ∧ List.Forall₂ (fun k t => Denotes v (bit k) t) (List.range 52) terms
    have eachOff (lit : Lit) : Audited primary v (ready ∧ lit ∈ terms)
        (require .firstActivity [-lit]) (fun _ => True) := by
      refine (audit_require primary v _ _).mono ?_ (fun _ _ h => h)
      rintro ⟨⟨before,same⟩,mem⟩
      obtain ⟨k,hk,eq⟩ := List.mem_iff_getElem.mp mem
      have bound : k < 52 := by rw [← same.length_eq] at hk; simpa using hk
      obtain ⟨_,matchBit⟩ := get same bound
      rw [eq] at matchBit
      have off : bit k = false := before.2.2.2 k bound
      exact Denotes.unit (by simpa only [off,Bool.not_false] using matchBit.neg)
    refine Audited.bind (Audited.forM terms eachOff) ?_
    intro _
    apply Audited.pure
    intro h
    have size := h.1.1.2.2.1.1
    refine ⟨by simpa using size,?_⟩
    intro k bound
    have index : k < (Array.replicate values.size (-1 : Lit)).size := by simpa [size] using bound
    rw [getElem!_pos (Array.replicate values.size (-1 : Lit)) k index]
    simpa using Denotes.constant v h.1.1.1 false

theorem audit_port_order (primary : Input → Bool) (v : Values) (a b : List Lit) (left right : Nat) :
    Audited primary v (left ≤ right ∧ (∀ i < a.length, Denotes v (i == left) a[i]!) ∧
        ∀ j < b.length, Denotes v (j == right) b[j]!)
      (orderPortModes a b) (fun _ => True) := by
  unfold orderPortModes
  apply Audited.forM
  intro i
  apply Audited.forM
  intro mode
  apply (audit_require _ _ _ _).mono ?_ (fun _ _ h => h)
  rintro ⟨⟨⟨sorted,leftBits,rightBits⟩,hi⟩,mem⟩
  by_cases leftOn : i = left
  · obtain ⟨j,jtake,eq⟩ := List.mem_iff_getElem.mp mem
    have bounds : j < i ∧ j < b.length := by simpa using jtake
    have off : (j == right) = false := Bool.eq_false_iff.mpr (fun h => by have := beq_iff_eq.mp h; omega)
    have value := rightBits j bounds.2
    rw [getElem!_pos b j bounds.2, ← List.getElem_take (h := jtake), eq,off] at value
    exact ⟨-mode,by simp,(value.neg).2⟩
  · have off : (i == left) = false := Bool.eq_false_iff.mpr (fun h => leftOn (beq_iff_eq.mp h))
    have value := leftBits i (List.mem_range.mp hi)
    rw [off] at value
    exact ⟨-a[i]!,List.mem_cons_self,(value.neg).2⟩

theorem audit_line_hits (primary : Input → Bool) (v : Values) (line : Nat) (leaf : Leaf)
    (selectors : List TopSelector) (stages : Array Stage) (answer : Nat → Bool) :
    Audited primary v
      (∀ k < samples.size,
        HitInputs v (fun i => stages[i]!.values[k]!) leaf selectors samples[k]! ∧
        decodedHit v line leaf selectors (fun i => stages[i]!.values[k]!) samples[k]! = answer k ∧
        (52 ≤ k → answer k = false))
      (lineHits line leaf selectors stages) (RowDenotes v answer) := by
  unfold RowDenotes lineHits
  apply Audited.mapM
  intro k
  let lookup := fun i : Nat => stages[i]!.values[k]!
  let pre := (∀ j < samples.size, HitInputs v (fun i => stages[i]!.values[j]!) leaf selectors samples[j]! ∧
      decodedHit v line leaf selectors (fun i => stages[i]!.values[j]!) samples[j]! = answer j ∧
      (52 ≤ j → answer j = false)) ∧ k ∈ List.range samples.size
  have top : Audited primary v pre (topHit line leaf selectors lookup samples[k]!) (Denotes v (answer k)) := by
    refine (audit_top_hit primary v line leaf selectors lookup samples[k]!).mono
      (fun h => (h.1 k (List.mem_range.mp h.2)).1) ?_
    rintro h t ⟨nz,eval⟩
    exact ⟨nz, eval.trans (h.1 k (List.mem_range.mp h.2)).2.1⟩
  apply Audited.bind top
  intro hit
  by_cases negative : 52 ≤ k
  · simp only [ite_eq_left negative]
    apply Audited.bind ((audit_require primary v .negativeTest [-hit]).mono ?_ (fun _ _ h => h))
    · intro _
      exact Audited.pure _ _ _ (fun h => h.1.2)
    · rintro ⟨h,value⟩
      have falseAnswer := (h.1 k (List.mem_range.mp h.2)).2.2 negative
      exact Denotes.unit (by simpa only [falseAnswer, Bool.not_false] using value.neg)
  · simp only [ite_eq_right negative]
    exact Audited.pure _ _ _ And.right

theorem audit_positive_tests (primary : Input → Bool) (v : Values) (hits : List (List Lit)) :
    Audited primary v (∀ k < 52, ∃ row ∈ hits, literalValue v row[k]! = true)
      (positiveTests hits) (fun _ => True) := by
  unfold positiveTests
  apply Audited.forM
  intro k
  refine (audit_require primary v .positiveTest _).mono ?_ (fun _ _ h => h)
  rintro ⟨found,hk⟩
  obtain ⟨row,mem,on⟩ := found k (List.mem_range.mp hk)
  exact ⟨_,List.mem_map_of_mem mem,on⟩

def RawSubset (v : Values) (source target : Array Lit) : Prop :=
  ClauseTrue v source.toList ∧ ∀ pair ∈ source.toList.zip target.toList,
    literalValue v pair.1 = true → literalValue v pair.2 = true

theorem ArrayDenotes.nonzero {v : Values} {length : Nat} {bits : Nat → Bool} {xs : Array Lit}
    (values : ArrayDenotes v length bits xs) : ∀ t ∈ xs.toList, t ≠ 0 := by
  intro t ht
  obtain ⟨j, h, eq⟩ := List.mem_iff_getElem.mp ht
  have index : j < xs.size := by simpa using h
  have known := (values.2 j (values.1 ▸ index)).1
  rw [getElem!_pos xs j index, ← Array.getElem_toList h, eq] at known
  exact known

theorem raw_subset_of_denotes {v : Values} {length : Nat} {src tgt : Array Lit} {a b : Nat → Bool}
    (source : ArrayDenotes v length a src) (target : ArrayDenotes v length b tgt)
    (nonempty : ∃ j < length, a j = true) (subset : ∀ j < length, a j = true → b j = true) :
    RawSubset v src tgt := by
  constructor
  · obtain ⟨j,bound,on⟩ := nonempty
    have h : j < src.toList.length := by simpa [source.1] using bound
    refine ⟨src.toList[j],List.getElem_mem h,?_⟩
    rw [Array.getElem_toList h, ← getElem!_pos]
    exact (source.2 j bound).2.trans on
  · intro t ht on
    obtain ⟨j,h,rfl⟩ := List.mem_iff_getElem.mp ht
    have bound : j < length := by simpa [List.length_zip,source.1,target.1] using h
    have sj : j < src.size := source.1.symm ▸ bound
    have tj : j < tgt.size := target.1.symm ▸ bound
    rw [List.getElem_zip] at on ⊢
    change literalValue v src.toList[j] = true at on
    change literalValue v tgt.toList[j] = true
    rw [Array.getElem_toList, ← getElem!_pos src j sj] at on
    rw [Array.getElem_toList, ← getElem!_pos tgt j tj, (target.2 j bound).2]
    exact subset j bound ((source.2 j bound).2.symm.trans on)

def CentreMaskBit (extra : BitVec 5) (line i : Nat) (bit : Bool) : Prop :=
  (extra.getLsbD i = false → bit = false) ∧
    (extra.getLsbD i = true → i = firstBit extra → line = 13 → bit = true)

theorem audit_top_centre_rule (primary : Input → Bool) (v : Values) (extra : BitVec 5)
    (line i : Nat) (bit : Bool) (select : Lit) :
    Audited primary v (Denotes v bit select ∧ CentreMaskBit extra line i bit)
      (topCentreRule extra line i select) (fun _ => True) := by
  unfold topCentreRule
  split
  · rename_i allowed
    split
    · rename_i anchor
      apply (audit_require _ _ _ _).mono ?_ (fun _ _ h => h)
      rintro ⟨meaning,mask⟩
      have cond : i = firstBit extra ∧ line = 13 := by simpa using anchor
      exact Denotes.unit (mask.2 allowed cond.1 cond.2 ▸ meaning)
    · exact Audited.pure _ _ _ (fun _ => trivial)
  · rename_i forbidden
    apply (audit_require _ _ _ _).mono ?_ (fun _ _ h => h)
    rintro ⟨meaning,mask⟩
    have off := mask.1 (Bool.eq_false_iff.mpr forbidden)
    exact Denotes.unit (by simpa only [off,Bool.not_false] using meaning.neg)

theorem audit_record_use (primary : Input → Bool) (v : Values) (i : Nat) (select : Lit) :
    Audited primary v True (recordUse i select) (fun _ => True) := by
  intro s
  exact ⟨[],by simp,fun _ _ => ⟨by simp,trivial⟩⟩

def topCentreRaw (line : Nat) : Array Lit :=
  (Array.range 26).map fun p => if p == line then 1 else -1

def topLeafRaw (leaf : Leaf) : Array Lit := (Array.range 26).map (rawAt leaf)

def TopChoiceDenotes (primary : Input → Bool) (v : Values) (line i : Nat) (s : TopSelector) : Prop :=
  s.1 = i ∧ Denotes v (primary (.topCentre line i)) s.2.1 ∧ Denotes v (primary (.topLeaf line i)) s.2.2

def TopChoices (primary : Input → Bool) (v : Values) (line : Nat) (slots : List Nat)
    (ss : List TopSelector) : Prop :=
  List.Forall₂ (TopChoiceDenotes primary v line) slots ss

structure TopAllowed (primary : Input → Bool) (v : Values) (extra : BitVec 5)
    (line : Nat) (leaf : Leaf) (stages : Array Stage) (i : Nat) : Prop where
  source : ∀ t ∈ stages[i]!.raw.toList, t ≠ 0
  centre : primary (.topCentre line i) = true → RawSubset v stages[i]!.raw (topCentreRaw line)
  leaf : primary (.topLeaf line i) = true → RawSubset v stages[i]!.raw (topLeafRaw leaf)
  mask : CentreMaskBit extra line i (primary (.topCentre line i))

theorem audit_select_top (primary : Input → Bool) (v : Values) (stages : Array Stage)
    (firstAnd : Nat) (extra : BitVec 5) (line : Nat) (leaf : Leaf) :
    Audited primary v (∀ i ∈ topSlots stages firstAnd, TopAllowed primary v extra line leaf stages i)
      (selectTop stages firstAnd extra line leaf) (TopChoices primary v line (topSlots stages firstAnd)) := by
  unfold selectTop TopChoices
  apply Audited.mapM
  intro i
  let pre := (∀ j ∈ topSlots stages firstAnd, TopAllowed primary v extra line leaf stages j) ∧
    i ∈ topSlots stages firstAnd
  apply Audited.bind ((audit_choose primary v (.topCentre line i)).mono (fun _ : pre => trivial) (fun _ _ h => h))
  intro z
  let withZ := pre ∧ Denotes v (primary (.topCentre line i)) z
  apply Audited.bind ((audit_choose primary v (.topLeaf line i)).mono (fun _ : withZ => trivial) (fun _ _ h => h))
  intro l
  let picked := withZ ∧ Denotes v (primary (.topLeaf line i)) l
  apply Audited.bind ((audit_record_use primary v i z).mono (fun _ : picked => trivial) (fun _ _ h => h))
  intro _
  apply Audited.bind ((audit_record_use primary v i l).mono (fun _ : picked ∧ True => trivial) (fun _ _ h => h))
  intro _
  have centre : Audited primary v ((picked ∧ True) ∧ True)
      (eligible stages[i]!.raw (topCentreRaw line) z) (fun _ => True) := by
    apply (audit_eligible _ _ _ _ _).mono ?_ (fun _ _ h => h)
    rintro ⟨⟨⟨⟨⟨valid,mem⟩,sz⟩,_⟩,_⟩,_⟩
    exact ⟨sz.1,(valid i mem).source,fun on => (valid i mem).centre (sz.2.symm.trans on)⟩
  apply Audited.bind centre
  intro _
  have leafRoute : Audited primary v (((picked ∧ True) ∧ True) ∧ True)
      (eligible stages[i]!.raw (topLeafRaw leaf) l) (fun _ => True) := by
    apply (audit_eligible _ _ _ _ _).mono ?_ (fun _ _ h => h)
    rintro ⟨⟨⟨⟨⟨⟨valid,mem⟩,_⟩,sl⟩,_⟩,_⟩,_⟩
    exact ⟨sl.1,(valid i mem).source,fun on => (valid i mem).leaf (sl.2.symm.trans on)⟩
  apply Audited.bind leafRoute
  intro _
  apply Audited.bind ((audit_top_centre_rule primary v extra line i (primary (.topCentre line i)) z).mono ?_ (fun _ _ h => h))
  · intro _
    apply Audited.pure
    intro h
    have hp : picked := h.1.1.1.1.1
    exact ⟨rfl,hp.1.2,hp.2⟩
  · intro h
    have hp : picked := h.1.1.1.1
    exact ⟨hp.1.2,(hp.1.1.1 i hp.1.1.2).mask⟩

theorem TopChoices.mem {primary : Input → Bool} {v : Values} {line : Nat} {slots : List Nat}
    {ss : List TopSelector} (rel : TopChoices primary v line slots ss) :
    ∀ s ∈ ss, s.1 ∈ slots ∧ TopChoiceDenotes primary v line s.1 s := by
  induction rel with
  | nil => simp
  | cons matchHead _ ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | tail
    · exact ⟨by simp [matchHead.1],rfl,matchHead.1 ▸ matchHead.2⟩
    · obtain ⟨mem,meaning⟩ := ih q tail
      exact ⟨List.mem_cons_of_mem _ mem,meaning⟩

theorem TopChoices.for_slot {primary : Input → Bool} {v : Values} {line : Nat} {slots : List Nat}
    {ss : List TopSelector} (rel : TopChoices primary v line slots ss) {i : Nat} (mem : i ∈ slots) :
    ∃ s ∈ ss, TopChoiceDenotes primary v line i s := by
  induction rel with
  | nil => simp at mem
  | cons head _ ih =>
    rcases List.mem_cons.mp mem with rfl | tail
    · exact ⟨_,List.mem_cons_self,head⟩
    · obtain ⟨s,hs,meaning⟩ := ih tail
      exact ⟨s,List.mem_cons_of_mem _ hs,meaning⟩

theorem selectedBits_on {primary : Input → Bool} {v : Values} {line : Nat} {slots : List Nat}
    {ss : List TopSelector} (rel : TopChoices primary v line slots ss)
    (read : Nat → Lit) (value : Nat → Bool) (bank : ∀ i ∈ slots, Denotes v (value i) (read i))
    {pick : TopSelector → Lit} {tag : Nat → Input}
    (which : ∀ i s, TopChoiceDenotes primary v line i s → Denotes v (primary (tag i)) (pick s)) :
    (selectedBits v read pick ss).any id = true ↔ ∃ i ∈ slots, primary (tag i) = true ∧ value i = true := by
  simp only [selectedBits,List.any_map,Function.comp_apply,id_eq,List.any_eq_true,Bool.and_eq_true]
  constructor
  · rintro ⟨s,hs,chosen,on⟩
    obtain ⟨mem,meaning⟩ := rel.mem s hs
    exact ⟨s.1,mem,(which _ _ meaning).2.symm.trans chosen,(bank _ mem).2.symm.trans on⟩
  · rintro ⟨i,hi,chosen,on⟩
    obtain ⟨s,hs,meaning⟩ := rel.for_slot hi
    refine ⟨s,hs,(which _ _ meaning).2.trans chosen,?_⟩
    rw [meaning.1]
    exact (bank _ hi).2.trans on

theorem leaf_terms_value (v : Values) (one : v 1 = true) (leaf : Leaf) (input : List Nat) :
    (input.filterMap (fun n => leaf.lookup n)).any (literalValue v) =
      input.any (fun n => literalValue v (rawAt leaf n)) := by
  induction input with
  | nil => rfl
  | cons x xs ih =>
    cases found : leaf.lookup x <;> simp [found,rawAt,literalValue,one,ih]

structure OutputTestsReady (primary : Input → Bool) (v : Values) (dirty extra : BitVec 5)
    (leaves : Array Leaf) (stages : Array Stage) (answer : Nat → Nat → Bool) : Prop where
  routes : ∀ line ∈ List.range' 13 13, ∀ i ∈ topSlots stages (firstBit dirty),
    TopAllowed primary v extra line leaves[line-13]! stages i
  hits : ∀ line ∈ List.range' 13 13, ∀ selectors,
    TopChoices primary v line (topSlots stages (firstBit dirty)) selectors → ∀ k < samples.size,
      HitInputs v (fun i => stages[i]!.values[k]!) leaves[line-13]! selectors samples[k]! ∧
      decodedHit v line leaves[line-13]! selectors (fun i => stages[i]!.values[k]!) samples[k]! = answer line k ∧
      (52 ≤ k → answer line k = false)
  positives : ∀ k < 52, ∃ line ∈ List.range' 13 13, answer line k = true

def OutputRow (primary : Input → Bool) (v : Values) (dirty : BitVec 5) (stages : Array Stage)
    (answer : Nat → Nat → Bool) (line : Nat) (row : List TopSelector × List Lit) : Prop :=
  TopChoices primary v line (topSlots stages (firstBit dirty)) row.1 ∧ RowDenotes v (answer line) row.2

private theorem audit_collect_line (primary : Input → Bool) (v : Values) (dirty extra : BitVec 5)
    (leaves : Array Leaf) (stages : Array Stage) (answer : Nat → Nat → Bool) (line : Nat) :
    Audited primary v (OutputTestsReady primary v dirty extra leaves stages answer ∧ line ∈ List.range' 13 13)
      (collectLineTests dirty extra line leaves[line-13]! stages) (OutputRow primary v dirty stages answer line) := by
  let pre := OutputTestsReady primary v dirty extra leaves stages answer
  let picked := TopChoices primary v line (topSlots stages (firstBit dirty))
  unfold collectLineTests
  refine Audited.bind (p := picked) ((audit_select_top primary v stages (firstBit dirty) extra line leaves[line-13]!).mono
    (fun h : pre ∧ line ∈ List.range' 13 13 => h.1.routes line h.2) (fun _ _ h => h)) ?_
  intro selectors
  refine Audited.bind (p := RowDenotes v (answer line))
    ((audit_line_hits primary v line leaves[line-13]! selectors stages (answer line)).mono
      (fun h : (pre ∧ line ∈ List.range' 13 13) ∧ picked selectors => h.1.1.hits line h.1.2 selectors h.2)
      (fun _ _ h => h)) ?_
  intro hits
  exact Audited.pure _ _ _ (fun h => ⟨h.1.2,h.2⟩)

private theorem positive_rows {v : Values} {rel : Nat → (List TopSelector × List Lit) → Prop}
    {lines : List Nat} {rows : List (List TopSelector × List Lit)} {answer : Nat → Nat → Bool}
    (same : List.Forall₂ rel lines rows) (valid : ∀ l row, rel l row → RowDenotes v (answer l) row.2)
    (positives : ∀ k < 52, ∃ l ∈ lines, answer l k = true) :
    ∀ k < 52, ∃ row ∈ rows.map Prod.snd, literalValue v row[k]! = true := by
  intro k hk
  obtain ⟨l,mem,on⟩ := positives k hk
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp mem
  have inRows : i < rows.length := same.length_eq ▸ hi
  have get : RowDenotes v (answer lines[i]) rows[i].2 := valid _ _ (same.get hi inRows)
  rw [eq] at get
  have len : samples.size = 132 := by decide +kernel
  have bound : k < samples.size := by omega
  exact ⟨_,List.mem_map_of_mem (List.getElem_mem inRows),(get.get bound).2.trans on⟩

private theorem audit_test_rows (primary : Input → Bool) (v : Values)
    (lines : List Nat) (write : Nat → Build (List TopSelector × List Lit))
    (pre : Prop) (rel : Nat → List TopSelector × List Lit → Prop) (answer : Nat → Nat → Bool)
    (each : ∀ line, Audited primary v (pre ∧ line ∈ lines) (write line) (rel line))
    (known : ∀ line row, rel line row → RowDenotes v (answer line) row.2)
    (hits : pre → ∀ k < 52, ∃ line ∈ lines, answer line k = true) :
    Audited primary v pre
      (do let rows ← lines.mapM write; positiveTests (rows.map Prod.snd); pure rows)
      (List.Forall₂ rel lines) := by
  refine Audited.bind (Audited.mapM lines each) ?_
  intro rows
  change Audited primary v (pre ∧ List.Forall₂ rel lines rows)
    (positiveTests (rows.map Prod.snd) >>= fun _ => pure rows) (List.Forall₂ rel lines)
  refine Audited.bind (m := positiveTests (rows.map Prod.snd)) (f := fun _ => pure rows) (p := fun _ => True)
    ((audit_positive_tests primary v (rows.map Prod.snd)).mono
    (fun h : pre ∧ List.Forall₂ rel lines rows => positive_rows h.2 known (hits h.1))
    (fun _ _ h => h)) ?_
  intro _
  exact Audited.pure _ _ _ (fun h => h.1.2)

attribute [local irreducible] collectLineTests positiveTests

theorem audit_collect_output_tests (primary : Input → Bool) (v : Values) (dirty extra : BitVec 5)
    (leaves : Array Leaf) (stages : Array Stage) (answer : Nat → Nat → Bool) :
    Audited primary v (OutputTestsReady primary v dirty extra leaves stages answer)
      (collectOutputTests dirty extra leaves stages)
      (List.Forall₂ (OutputRow primary v dirty stages answer) (List.range' 13 13)) := by
  unfold collectOutputTests
  exact audit_test_rows primary v (List.range' 13 13)
    (fun line => collectLineTests dirty extra line leaves[line-13]! stages)
    (OutputTestsReady primary v dirty extra leaves stages answer) (OutputRow primary v dirty stages answer) answer
    (audit_collect_line primary v dirty extra leaves stages answer) (fun _ _ h => h.2) OutputTestsReady.positives

theorem centre_terms_on {primary : Input → Bool} {v : Values} {dirty : BitVec 5} {stages : Array Stage}
    {answer : Nat → Nat → Bool} {lines : List Nat} {rows : List (List TopSelector × List Lit)}
    (rel : List.Forall₂ (OutputRow primary v dirty stages answer) lines rows)
    {i line : Nat} (hl : line ∈ lines) (hi : i ∈ topSlots stages (firstBit dirty))
    (on : primary (.topCentre line i) = true) : ClauseTrue v (centreTerms rows i) := by
  obtain ⟨j,bound,eq⟩ := List.mem_iff_getElem.mp hl
  have hr : j < rows.length := rel.length_eq ▸ bound
  have chosen : TopChoices primary v lines[j] (topSlots stages (firstBit dirty)) rows[j].1 :=
    (rel.get bound hr).1
  rw [eq] at chosen
  obtain ⟨s,hs,meaning⟩ := chosen.for_slot hi
  refine ⟨s.2.1, List.mem_flatMap.mpr ⟨rows[j],List.getElem_mem hr,?_⟩, meaning.2.1.2.trans on⟩
  exact List.mem_filterMap.mpr ⟨s,hs,by simp [meaning.1]⟩

#print axioms audit_top_hit
#print axioms audit_line_hits
#print axioms audit_positive_tests
#print axioms audit_collect_output_tests
#print axioms audit_combine_samples
#print axioms audit_combine_raw
#print axioms audit_first_activity
#print axioms audit_port_order

end SixEdge.Formula
