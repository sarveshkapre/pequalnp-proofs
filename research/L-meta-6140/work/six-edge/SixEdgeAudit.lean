import SixEdgeTrace

namespace SixEdge.Formula

/-- Values fixed by the trace. Requirements are checked separately. -/
def Interprets (primary : Input → Bool) (v : Values) : Event → Prop
  | .choice i name => v i = primary name
  | .defineOr i ts => v i = ts.any (literalValue v)
  | .require .. => True

def Meets (v : Values) : Event → Prop
  | .require _ ts => ClauseTrue v ts
  | _ => True

theorem assignment_interprets (primary : Input → Bool) (s : BuildState)
    (wf : TraceValid 1 s.events.toList) :
    ∀ e ∈ s.events.toList, Interprets primary (assignment primary initial s.events.toList) e := by
  intro e he
  cases e with
  | choice => exact chosen_value _ _ _ _ wf he
  | defineOr => exact defined_value _ _ _ _ wf he
  | require => trivial

/-- An encoder segment appends events. With their definitions interpreted, its
    new requirements hold and its return value meets the stated postcondition. -/
def Audited (primary : Input → Bool) (v : Values) {α : Type}
    (pre : Prop) (m : Build α) (post : α → Prop) : Prop :=
  ∀ s,
    let (a,t) := m.run s
    ∃ suffix, t.events.toList = s.events.toList ++ suffix ∧
      ((∀ e ∈ suffix, Interprets primary v e) → pre → (∀ e ∈ suffix, Meets v e) ∧ post a)

theorem Audited.pure (primary : Input → Bool) (v : Values) {α : Type} (a : α)
    {pre : Prop} {post : α → Prop} (h : pre → post a) : Audited primary v pre (pure a) post := by
  intro s
  exact ⟨[], by simp, fun _ hp => ⟨by simp,h hp⟩⟩

theorem Audited.bind {primary : Input → Bool} {v : Values} {α β : Type}
    {pre : Prop} {m : Build α} {f : α → Build β} {p : α → Prop} {q : β → Prop}
    (first : Audited primary v pre m p) (next : ∀ a, Audited primary v (pre ∧ p a) (f a) q) :
    Audited primary v pre (m >>= f) q := by
  intro s
  obtain ⟨es, firstAppended, conditions⟩ := first s
  let mid := (m.run s).2
  let a := (m.run s).1
  let t := ((f a).run mid).2
  change ∃ suffix, t.events.toList = s.events.toList ++ suffix ∧ _
  obtain ⟨fs, appended, hf⟩ := next a mid
  refine ⟨es ++ fs, ?_, ?_⟩
  · rw [show t.events.toList = mid.events.toList ++ fs from appended,
      show mid.events.toList = s.events.toList ++ es from firstAppended, List.append_assoc]
  · intro defs hp
    obtain ⟨verified,ha⟩ := conditions (fun e he => defs e (List.mem_append_left _ he)) hp
    obtain ⟨rest,result⟩ := hf (fun e he => defs e (List.mem_append_right _ he)) ⟨hp, ha⟩
    refine ⟨?_, result⟩
    intro e he
    rcases List.mem_append.mp he with h | h
    · exact verified e h
    · exact rest e h

theorem Audited.mono {primary : Input → Bool} {v : Values} {α : Type}
    {pre stronger : Prop} {m : Build α} {p q : α → Prop}
    (audit : Audited primary v pre m p) (hs : stronger → pre) (hq : stronger → ∀ a, p a → q a) :
    Audited primary v stronger m q := by
  intro s
  obtain ⟨es, appended, verify⟩ := audit s
  refine ⟨es, appended, ?_⟩
  intro defs h
  obtain ⟨met, after⟩ := verify defs (hs h)
  exact ⟨met, hq h _ after⟩

theorem audit_require (primary : Input → Bool) (v : Values) (rule : Rule) (ts : List Lit) :
    Audited primary v (ClauseTrue v ts) (require rule ts) (fun _ => True) := by
  intro s
  refine ⟨[.require rule ts], by simp, ?_⟩
  intro _ correct
  exact ⟨by simpa [Meets],trivial⟩

theorem audit_choose (primary : Input → Bool) (v : Values) (name : Input) :
    Audited primary v True (choose name) (fun t => t ≠ 0 ∧ literalValue v t = primary name) := by
  intro s
  let i := s.variableCount + 1
  refine ⟨[.choice i name], by simp [i], ?_⟩
  intro defs _
  have val : v i = primary name := defs _ List.mem_cons_self
  have pos : 0 < i := by simp [i]
  refine ⟨by simp [Meets], ?_⟩
  change (i : Int) ≠ 0 ∧ literalValue v (i : Int) = primary name
  simp [literalValue, pos, Nat.ne_of_gt pos, val]

theorem literal_neg_of_ne (v : Values) {t : Lit} (nz : t ≠ 0) :
    literalValue v (-t) = !(literalValue v t) :=
  literal_neg v (Nat.pos_of_ne_zero (by simpa using nz))

private theorem trimmed_value (v : Values) (oneTrue : v 1 = true) (terms : List Lit) :
    ((terms.filter (· != -1)).eraseDups).any (literalValue v) = terms.any (literalValue v) := by
  have falseLit : literalValue v (-1) = false := by simp [literalValue, oneTrue]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_eraseDups, List.mem_filter, bne_iff_ne]
  constructor
  · rintro ⟨t, ⟨ht,_⟩, on⟩
    exact ⟨t,ht,on⟩
  · rintro ⟨t,ht,on⟩
    refine ⟨t,⟨ht,?_⟩,on⟩
    rintro rfl
    simp [falseLit] at on

theorem audit_or (primary : Input → Bool) (v : Values) (terms : List Lit) :
    Audited primary v (v 1 = true ∧ ∀ t ∈ terms, t ≠ 0) (makeOr terms)
      (fun t => t ≠ 0 ∧ literalValue v t = terms.any (literalValue v)) := by
  change Audited primary v _ (if terms.contains 1 then pure 1 else _) _
  split
  · rename_i oneIn
    apply Audited.pure
    intro h
    have member : (1 : Lit) ∈ terms := List.contains_iff_mem.mp oneIn
    have yes : literalValue v 1 = true := by simp [literalValue, h.1]
    exact ⟨by decide, yes.trans (List.any_eq_true.mpr ⟨1,member,yes⟩).symm⟩
  · dsimp only
    have subset : ∀ t ∈ (terms.filter (· != -1)).eraseDups, t ∈ terms := fun t ht =>
      (List.mem_filter.mp (List.mem_eraseDups.mp ht)).1
    have evalTrim (h : v 1 = true) := trimmed_value v h terms
    generalize clean : (terms.filter (· != -1)).eraseDups = ts at *
    cases ts with
    | nil =>
      apply Audited.pure
      intro h
      exact ⟨by decide, by simpa [literalValue, h.1] using evalTrim h.1⟩
    | cons t rest =>
      cases rest with
      | nil =>
        apply Audited.pure
        intro h
        exact ⟨h.2 _ (subset _ List.mem_cons_self), by simpa using evalTrim h.1⟩
      | cons u more =>
        intro s
        let i := s.variableCount + 1
        refine ⟨[.defineOr i (t::u::more)], by simp [i], ?_⟩
        intro defs h
        have val : v i = (t::u::more).any (literalValue v) := defs _ List.mem_cons_self
        have pos : 0 < i := by simp [i]
        refine ⟨by simp [Meets], ?_⟩
        change (i : Int) ≠ 0 ∧ literalValue v (i : Int) = _
        simpa [literalValue, pos, Nat.ne_of_gt pos, val] using evalTrim h.1

theorem audit_and (primary : Input → Bool) (v : Values) (terms : List Lit) :
    Audited primary v (v 1 = true ∧ ∀ t ∈ terms, t ≠ 0) (makeAnd terms)
      (fun t => t ≠ 0 ∧ literalValue v t = terms.all (literalValue v)) := by
  unfold makeAnd
  apply Audited.bind ((audit_or primary v (terms.map Neg.neg)).mono ?_ (fun _ _ h => h))
  · intro t
    apply Audited.pure
    rintro ⟨⟨_, nonzero⟩, nz, value⟩
    refine ⟨neg_ne_zero.mpr nz, ?_⟩
    rw [literal_neg_of_ne _ nz, value]
    clear value nz
    induction terms with
    | nil => rfl
    | cons x xs ih =>
      have tail := ih (fun y hy => nonzero y (List.mem_cons_of_mem _ hy))
      simp only [List.map_cons, List.any_cons, List.all_cons,
        literal_neg_of_ne _ (nonzero x List.mem_cons_self), Bool.not_or, Bool.not_not, tail]
  · rintro ⟨oneTrue,nonzero⟩
    refine ⟨oneTrue,?_⟩
    rintro t ht
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ht
    exact neg_ne_zero.mpr (nonzero x hx)

theorem Audited.mapM {primary : Input → Bool} {v : Values} {α β : Type}
    (xs : List α) {pre : Prop} {f : α → Build β} {r : α → β → Prop}
    (each : ∀ a, Audited primary v (pre ∧ a ∈ xs) (f a) (r a)) :
    Audited primary v pre (xs.mapM f) (List.Forall₂ r xs) := by
  induction xs with
  | nil => exact Audited.pure _ _ _ (fun _ => List.Forall₂.nil)
  | cons x xs ih =>
    rw [List.mapM_cons]
    apply Audited.bind ((each x).mono (fun h => ⟨h,List.mem_cons_self⟩) (fun _ _ h => h))
    intro y
    have checked := ih (fun a => (each a).mono
      (fun ⟨hp,ha⟩ => ⟨hp,List.mem_cons_of_mem _ ha⟩) (fun _ _ h => h))
    apply Audited.bind (checked.mono And.left (fun _ _ h => h))
    intro ys
    exact Audited.pure _ _ _ (fun ⟨⟨_,h⟩,tail⟩ => List.Forall₂.cons h tail)

theorem Audited.forM {primary : Input → Bool} {v : Values} {α : Type}
    (xs : List α) {pre : Prop} {f : α → Build Unit}
    (each : ∀ a, Audited primary v (pre ∧ a ∈ xs) (f a) (fun _ => True)) :
    Audited primary v pre (xs.forM f) (fun _ => True) := by
  induction xs with
  | nil => exact Audited.pure _ _ _ (fun _ => trivial)
  | cons x xs ih =>
    change Audited primary v _ (f x >>= fun _ => xs.forM f) _
    apply Audited.bind ((each x).mono (fun h => ⟨h,List.mem_cons_self⟩) (fun _ _ h => h))
    intro _
    have checked := ih (fun a => (each a).mono
      (fun ⟨hp,ha⟩ => ⟨hp,List.mem_cons_of_mem _ ha⟩) (fun _ _ h => h))
    exact checked.mono And.left (fun _ _ h => h)

theorem Audited.foldlM {primary : Input → Bool} {v : Values} {α β : Type}
    (f : β → α → Build β) (invariant : List α → β → Prop)
    (admissible : α → Prop) (pre : Prop)
    (step : ∀ seen b a, Audited primary v (pre ∧ admissible a ∧ invariant seen b)
      (f b a) (invariant (a :: seen))) (xs : List α) (b : β) (seen : List α) :
    Audited primary v (pre ∧ (∀ a ∈ xs, admissible a) ∧ invariant seen b)
      (xs.foldlM f b) (invariant (xs.reverse ++ seen)) := by
  induction xs generalizing b seen with
  | nil => exact Audited.pure _ _ _ (fun h => h.2.2)
  | cons a xs ih =>
    rw [List.foldlM_cons]
    refine Audited.bind (f := xs.foldlM f)
      ((step seen b a).mono (fun h => ⟨h.1,h.2.1 a List.mem_cons_self,h.2.2⟩) (fun _ _ h => h)) ?_
    intro next
    refine (ih next (a :: seen)).mono ?_ ?_
    · rintro ⟨⟨before, valid, _⟩, inv⟩
      exact ⟨before,fun x hx => valid x (List.mem_cons_of_mem _ hx),inv⟩
    · intro _ _ h
      simpa [List.reverse_cons,List.append_assoc] using h

/-- The exact emitted routing or promotion check is satisfied when the selected
    source is nonempty and its raw support is contained in the target. -/
theorem audit_eligible (primary : Input → Bool) (v : Values)
    (previous raw : Array Lit) (select : Lit) :
    Audited primary v (select ≠ 0 ∧
      (∀ old ∈ previous.toList, old ≠ 0) ∧
      (literalValue v select = true →
        ClauseTrue v previous.toList ∧ ∀ term ∈ previous.toList.zip raw.toList,
          literalValue v term.1 = true → literalValue v term.2 = true))
      (eligible previous raw select) (fun _ => True) := by
  let pre := select ≠ 0 ∧
    (∀ old ∈ previous.toList, old ≠ 0) ∧
    (literalValue v select = true →
      ClauseTrue v previous.toList ∧ ∀ term ∈ previous.toList.zip raw.toList,
        literalValue v term.1 = true → literalValue v term.2 = true)
  have head : Audited primary v pre (require .rawNonempty (-select :: previous.toList)) (fun _ => True) := by
    apply (audit_require _ _ _ _).mono ?_ (fun _ _ h => h)
    rintro ⟨nz,_,valid⟩
    cases h : literalValue v select with
    | false => exact ⟨-select,List.mem_cons_self,by rw [literal_neg_of_ne _ nz,h]; rfl⟩
    | true =>
      obtain ⟨t,ht,on⟩ := (valid h).1
      exact ⟨t,List.mem_cons_of_mem _ ht,on⟩
  unfold eligible
  refine Audited.bind head (fun _ => ?_)
  change Audited primary v _ ((previous.toList.zip raw.toList).forM
    (fun (old,new) => require .rawSubset [-select,-old,new])) _
  apply Audited.forM
  rintro ⟨old,new⟩
  apply (audit_require _ _ _ _).mono ?_ (fun _ _ h => h)
  rintro ⟨⟨⟨nz,oldNZ,valid⟩,_⟩,term⟩
  cases h : literalValue v select with
  | false => exact ⟨-select,List.mem_cons_self,by rw [literal_neg_of_ne _ nz,h]; rfl⟩
  | true =>
    cases on : literalValue v old with
    | false =>
      have oc := oldNZ old (List.of_mem_zip term).1
      exact ⟨-old,by simp,by rw [literal_neg_of_ne _ oc,on]; rfl⟩
    | true => exact ⟨new,by simp,(valid h).2 (old,new) term on⟩

theorem audit_program {primary : Input → Bool} {pre : Prop} {α : Type} {p : α → Prop} (m : Build α)
    (correct : ∀ v, v 1 = true → Audited primary v pre m p) (hp : pre)
    (wf : TraceValid 1 (m.run {}).2.events.toList) :
    Requirements primary initial (m.run {}).2.events.toList := by
  let s := (m.run {}).2
  let v := assignment primary initial s.events.toList
  have one : v 1 = true := (assignment_keeps _ _ _ _ wf 1 (by decide)).trans rfl
  obtain ⟨es, appended, audited⟩ := correct v one {}
  have eq : s.events.toList = es := appended
  have defs e (he : e ∈ es) : Interprets primary v e := assignment_interprets _ _ wf e (eq.symm ▸ he)
  obtain ⟨allMet,_⟩ := audited defs hp
  apply (requirements_iff_final _ _ _ _ wf).mpr
  intro rule ts he
  exact allMet (.require rule ts) (eq ▸ he)

end SixEdge.Formula
