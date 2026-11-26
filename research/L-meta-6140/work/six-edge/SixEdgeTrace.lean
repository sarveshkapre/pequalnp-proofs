import SixEdgeFormula
import SixEdgeCNF
import Std.Sat.CNF.Dimacs

namespace SixEdge.Formula

open Std.Sat

abbrev Values := Nat → Bool

def literalValue (values : Values) (t : Lit) : Bool :=
  values t.natAbs == decide (0 < t)

def ClauseTrue (values : Values) (c : List Lit) : Prop :=
  ∃ t ∈ c, literalValue values t = true

def validAt (bound : Nat) (t : Lit) : Prop :=
  0 < t.natAbs ∧ t.natAbs ≤ bound

theorem advance_literal {a b : Values} {n : Nat} {t : Lit}
    (keep : ∀ i ≤ n, b i = a i) (valid : validAt n t) :
    literalValue b t = literalValue a t := by
  unfold literalValue
  rw [keep _ valid.2]

theorem literal_neg (a : Values) {t : Lit} (nonzero : 0 < t.natAbs) :
    literalValue a (-t) = !(literalValue a t) := by
  have nz : t ≠ 0 := by
    intro h
    simp [h] at nonzero
  by_cases p : 0 < t
  · have z : 0 ≤ t := le_of_lt p
    cases b : a t.natAbs <;> simp [literalValue, p, z, b]
  · have z : t < 0 := lt_of_le_of_ne (le_of_not_gt p) nz
    cases b : a t.natAbs <;> simp [literalValue, p, z, b]

def Event.bound (e : Event) (old : Nat) : Nat :=
  match e with
  | .choice i _ | .defineOr i _ => i
  | .require .. => old

def Event.valid (e : Event) (old : Nat) : Prop :=
  match e with
  | .choice i _ => i = old+1
  | .defineOr i terms => i = old+1 ∧ ∀ t ∈ terms, validAt old t
  | .require _ terms => ∀ t ∈ terms, validAt old t

def TraceValid (old : Nat) : List Event → Prop
  | [] => True
  | e :: rest => e.valid old ∧ TraceValid (e.bound old) rest

def Event.validBool (e : Event) (old : Nat) : Bool :=
  let bounded (terms : List Lit) := terms.all fun t => decide (0 < t.natAbs ∧ t.natAbs ≤ old)
  match e with
  | .choice i _ => decide (i = old+1)
  | .defineOr i terms => decide (i = old+1) && bounded terms
  | .require _ terms => bounded terms

theorem Event.validBool_spec (e : Event) (n : Nat) : e.validBool n = true ↔ e.valid n := by
  cases e <;> simp [Event.validBool, Event.valid, List.all_eq_true, validAt]

def traceValidBool (old : Nat) (events : List Event) : Bool :=
  (events.foldl (fun (n,ok) e => (e.bound n, ok && e.validBool n)) (old,true)).2

theorem traceValidBool_spec (old : Nat) (events : List Event) :
    traceValidBool old events = true ↔ TraceValid old events := by
  have fold (xs : List Event) (n : Nat) (good : Bool) :
      (xs.foldl (fun (n,ok) e => (e.bound n, ok && e.validBool n)) (n,good)).2 = true ↔
        good = true ∧ TraceValid n xs := by
    induction xs generalizing n good with
    | nil => simp [TraceValid]
    | cons e rest ih =>
      rw [List.foldl_cons, ih]
      simp [Event.validBool_spec, TraceValid, and_assoc]
  simpa [traceValidBool] using fold events old true

def advance (primary : Input → Bool) (a : Values) (e : Event) : Values :=
  match e with
  | .choice i name => Function.update a i (primary name)
  | .defineOr i terms => Function.update a i (terms.any (literalValue a))
  | .require .. => a

def assignment (primary : Input → Bool) (a : Values) (events : List Event) : Values :=
  events.foldl (advance primary) a

def Requirements (primary : Input → Bool) (a : Values) : List Event → Prop
  | [] => True
  | .require _ terms :: rest => ClauseTrue a terms ∧ Requirements primary a rest
  | e :: rest => Requirements primary (advance primary a e) rest

def initial : Values := fun i => i == 1

theorem kept_one (primary : Input → Bool) (a : Values) {n : Nat} {e : Event}
    (wf : e.valid n) (i : Nat) (hi : i ≤ n) : advance primary a e i = a i := by
  cases e with
  | choice j name =>
    have lt : i ≠ j := by have : j = n+1 := wf; omega
    exact Function.update_of_ne lt _ _
  | defineOr j terms =>
    have lt : i ≠ j := by have : j = n+1 := wf.1; omega
    exact Function.update_of_ne lt _ _
  | require => rfl

theorem Event.bound_ge {n : Nat} {e : Event} (wf : e.valid n) : n ≤ e.bound n := by
  cases e <;> simp_all [Event.valid, Event.bound]

theorem assignment_keeps (primary : Input → Bool) (events : List Event) (n : Nat)
    (a : Values) (wf : TraceValid n events) : ∀ i ≤ n, assignment primary a events i = a i := by
  induction events generalizing n a with
  | nil => intro i hi; rfl
  | cons e rest ih =>
    intro i hi
    obtain ⟨valid, tail⟩ := wf
    change assignment primary (advance primary a e) rest i = a i
    exact (ih _ _ tail i (hi.trans (Event.bound_ge valid))).trans (kept_one _ _ valid _ hi)

private theorem assignment_clause {a b : Values} {bound : Nat} {terms : List Lit}
    (keep : ∀ i ≤ bound, b i = a i) (valid : ∀ t ∈ terms, validAt bound t)
    (h : ClauseTrue a terms) : ClauseTrue b terms := by
  obtain ⟨t, ht, yes⟩ := h
  exact ⟨t, ht, (advance_literal keep (valid t ht)).trans yes⟩

theorem Event.clause_valid {n : Nat} {e : Event} (wf : e.valid n) :
    ∀ c ∈ e.rawClauses, ∀ t ∈ c, validAt (e.bound n) t := by
  cases e with
  | choice => simp [Event.rawClauses]
  | require rule terms => simpa [Event.rawClauses, Event.bound, Event.valid] using wf
  | defineOr i terms =>
    obtain ⟨next, bound⟩ := wf
    have iPos : 0 < i := by omega
    have lift t (h : t ∈ terms) : validAt i t := by
      exact ⟨(bound t h).1, (bound t h).2.trans (by omega)⟩
    intro c hc t ht
    rcases List.mem_cons.mp hc with rfl | other
    · rcases List.mem_cons.mp ht with rfl | h
      · simpa [validAt, Event.bound] using iPos
      · exact lift t h
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp other
      rcases List.mem_cons.mp ht with rfl | h
      · simpa [validAt, Event.bound] using lift u hu
      · rw [List.mem_singleton.mp h]
        simpa [validAt, Event.bound] using iPos

theorem or_defines (primary : Input → Bool) (a : Values) {i n : Nat} {terms : List Lit}
    (wf : (Event.defineOr i terms).valid n) :
    ∀ c ∈ (Event.defineOr i terms).rawClauses,
      ClauseTrue (advance primary a (.defineOr i terms)) c := by
  let b := advance primary a (.defineOr i terms)
  have v : b i = terms.any (literalValue a) := Function.update_self _ _ _
  have iPos : 0 < i := by have : i = n+1 := wf.1; omega
  have out : literalValue b i = terms.any (literalValue a) := by simp [literalValue, iPos, v]
  have outOff : literalValue b (-(i : Int)) = !(terms.any (literalValue a)) := by
    rw [literal_neg b (by simpa using iPos), out]
  have keep : ∀ t ∈ terms, literalValue b t = literalValue a t := fun t ht =>
    advance_literal (kept_one primary a wf) (wf.2 t ht)
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hRest
  · by_cases h : terms.any (literalValue a) = true
    · obtain ⟨t, ht, fire⟩ := List.any_eq_true.mp h
      exact ⟨t, List.mem_cons_of_mem _ ht, (keep _ ht).trans fire⟩
    · have off : terms.any (literalValue a) = false := Bool.eq_false_iff.mpr h
      exact ⟨-(i : Int), List.mem_cons_self, by rw [outOff, off]; rfl⟩
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hRest
    by_cases h : literalValue a t = true
    · exact ⟨(i : Int), by simp, out.trans (List.any_eq_true.mpr ⟨t,ht,h⟩)⟩
    · have off : literalValue a t = false := Bool.eq_false_iff.mpr h
      exact ⟨-t, List.mem_cons_self, by rw [literal_neg b (wf.2 t ht).1, keep _ ht, off]; rfl⟩

theorem trace_clauses (primary : Input → Bool) (events : List Event) (n : Nat) (a : Values)
    (wf : TraceValid n events) (h : Requirements primary a events) :
    ∀ e ∈ events, ∀ c ∈ e.rawClauses, ClauseTrue (assignment primary a events) c := by
  induction events generalizing n a with
  | nil => simp
  | cons step rest ih =>
    obtain ⟨valid, tail⟩ := wf
    have tailReq : Requirements primary (advance primary a step) rest := by
      cases step
      · exact h
      · exact h
      · exact h.2
    intro e he c hc
    change ClauseTrue (assignment primary (advance primary a step) rest) c
    rcases List.mem_cons.mp he with rfl | later
    · refine assignment_clause (assignment_keeps _ _ _ _ tail) (Event.clause_valid valid c hc) ?_
      cases e with
      | choice => simp [Event.rawClauses] at hc
      | defineOr => exact or_defines _ _ valid c hc
      | require =>
        have eq := List.mem_singleton.mp hc
        exact eq.symm ▸ h.1
    · exact ih _ _ tail tailReq e later c hc

theorem chosen_value (primary : Input → Bool) (events : List Event) (n : Nat) (a : Values)
    (wf : TraceValid n events) {i : Nat} {name : Input} (selected : .choice i name ∈ events) :
    assignment primary a events i = primary name := by
  induction events generalizing n a with
  | nil => simp at selected
  | cons step rest ih =>
    obtain ⟨valid, tail⟩ := wf
    change assignment primary (advance primary a step) rest i = _
    rcases List.mem_cons.mp selected with here | later
    · subst step
      rw [assignment_keeps _ _ _ _ tail i (by rfl)]
      exact Function.update_self _ _ _
    · exact ih _ _ tail later

theorem defined_value (primary : Input → Bool) (events : List Event) (n : Nat) (a : Values)
    (wf : TraceValid n events) {i : Nat} {terms : List Lit} (allocated : .defineOr i terms ∈ events) :
    let v := assignment primary a events
    v i = terms.any (literalValue v) := by
  induction events generalizing n a with
  | nil => simp at allocated
  | cons step rest ih =>
    obtain ⟨valid, tail⟩ := wf
    let current := advance primary a step
    change assignment primary current rest i = terms.any (literalValue (assignment primary current rest))
    rcases List.mem_cons.mp allocated with here | later
    · subst step
      calc
        _ = current i := assignment_keeps _ _ _ _ tail i (by rfl)
        _ = terms.any (literalValue a) := Function.update_self _ _ _
        _ = _ := by
          have same t (ht : t ∈ terms) :
              literalValue (assignment primary current rest) t = literalValue a t :=
            advance_literal (n := n) (fun j hj =>
              (assignment_keeps _ _ _ _ tail j (hj.trans (Event.bound_ge valid))).trans
                (kept_one _ _ valid j hj)) (valid.2 t ht)
          apply Bool.eq_iff_iff.mpr
          simp only [List.any_eq_true]
          exact ⟨fun ⟨t,ht,h⟩ => ⟨t,ht,(same t ht).trans h⟩,
            fun ⟨t,ht,h⟩ => ⟨t,ht,(same t ht).symm.trans h⟩⟩
    · exact ih _ _ tail later

theorem requirements_iff_final (primary : Input → Bool) (events : List Event) (n : Nat) (a : Values)
    (wf : TraceValid n events) : Requirements primary a events ↔
      ∀ rule terms, .require rule terms ∈ events → ClauseTrue (assignment primary a events) terms := by
  constructor
  · intro h rule terms mem
    apply trace_clauses _ _ _ _ wf h (.require rule terms) mem
    simp [Event.rawClauses]
  · intro h
    induction events generalizing n a with
    | nil => trivial
    | cons step rest ih =>
      obtain ⟨valid, tail⟩ := wf
      have next : Requirements primary (advance primary a step) rest :=
        ih _ _ tail (fun rule terms mem => h rule terms (List.mem_cons_of_mem _ mem))
      cases step with
      | choice => exact next
      | defineOr => exact next
      | require rule terms =>
        refine ⟨?_, next⟩
        have ht := h rule terms List.mem_cons_self
        change ClauseTrue (assignment primary a rest) terms at ht
        exact assignment_clause (fun j hj => (assignment_keeps _ _ _ _ tail j hj).symm) valid ht

theorem normalize_sound {v : Values} {c out : List Lit} (one : v 1 = true)
    (norm : normalizeClause c = some out) (h : ClauseTrue v c) :
    ClauseTrue v out := by
  unfold normalizeClause at norm
  dsimp only at norm
  split at norm
  · contradiction
  · injection norm with eq
    obtain ⟨t, mem, yes⟩ := h
    rw [← eq]
    refine ⟨t, ?_, yes⟩
    have keep : t ≠ -1 := by
      rintro rfl
      simp [literalValue, one] at yes
    exact List.mem_mergeSort.mpr (by simp [mem, keep])

theorem normalize_mem {c out : List Lit} (norm : normalizeClause c = some out)
    {t : Lit} (mem : t ∈ out) : t ∈ c := by
  unfold normalizeClause at norm
  dsimp only at norm
  split at norm
  · contradiction
  · injection norm with eq
    rw [← eq] at mem
    exact (List.mem_filter.mp (List.mem_eraseDups.mp (List.mem_mergeSort.mp mem))).1

/-- DIMACS numbering starts at one. The LRAT checker uses zero-based names. -/
def satLiteral (t : Lit) : Std.Sat.Literal Nat := (t.natAbs-1,decide (0<t))

def exactCNF (state : BuildState) : CNF Nat :=
  ⟨(state.clauses.map fun c => CNF.Clause.ofLiterals (c.map satLiteral)).toArray⟩

theorem normalized_clauses (primary : Input → Bool) (state : BuildState)
    (wf : TraceValid 1 state.events.toList)
    (h : Requirements primary initial state.events.toList) :
    ∀ c ∈ state.clauses, ClauseTrue (assignment primary initial state.events.toList) c := by
  have one : assignment primary initial state.events.toList 1 = true :=
    (assignment_keeps _ _ _ _ wf 1 (by decide)).trans rfl
  intro c hc
  rcases List.mem_cons.mp hc with rfl | fromTrace
  · exact ⟨1,by simp,by simp [literalValue,one]⟩
  · obtain ⟨e, he, raw⟩ := List.mem_flatMap.mp fromTrace
    obtain ⟨terms, hterms, norm⟩ := List.mem_filterMap.mp raw
    exact normalize_sound one norm (trace_clauses _ _ _ _ wf h e he terms hterms)

theorem raw_nonzero {n : Nat} {events : List Event} (wf : TraceValid n events)
    {e : Event} (he : e ∈ events) {c : List Lit} (hc : c ∈ e.rawClauses)
    {t : Lit} (ht : t ∈ c) : 0 < t.natAbs := by
  induction events generalizing n with
  | nil => simp at he
  | cons x xs ih =>
    obtain ⟨valid, tail⟩ := wf
    rcases List.mem_cons.mp he with rfl | later
    · exact (Event.clause_valid valid c hc t ht).1
    · exact ih tail later

theorem normalized_nonzero (state : BuildState) (wf : TraceValid 1 state.events.toList)
    {c : List Lit} (hc : c ∈ state.clauses) {t : Lit} (ht : t ∈ c) : 0 < t.natAbs := by
  rcases List.mem_cons.mp hc with rfl | fromTrace
  · rw [List.mem_singleton.mp ht]; decide
  · obtain ⟨e, he, raw⟩ := List.mem_flatMap.mp fromTrace
    obtain ⟨terms, hterms, norm⟩ := List.mem_filterMap.mp raw
    exact raw_nonzero wf he hterms (normalize_mem norm ht)

/-- Given the circuit's primary choices, the remaining variables can be assigned in
    generator order. Only clauses tagged `require` need a circuit-specific proof. -/
theorem assignment_satisfies (primary : Input → Bool) (state : BuildState)
    (wf : TraceValid 1 state.events.toList)
    (h : Requirements primary initial state.events.toList) :
    (exactCNF state).Sat (fun i => assignment primary initial state.events.toList (i+1)) := by
  apply CNF.sat_iff_all_mem_sat.mpr
  intro c hc
  change c ∈ (state.clauses.map fun r => CNF.Clause.ofLiterals (r.map satLiteral)).toArray at hc
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (by simpa using hc)
  obtain ⟨t, ht, valid⟩ := normalized_clauses primary state wf h r hr
  have nonzero := normalized_nonzero state wf hr ht
  apply CNF.Clause.sat_iff_exists_mem_eq.mpr
  refine ⟨satLiteral t, ?_, ?_⟩
  · rw [← CNF.Clause.mem_literals_iff, CNF.Clause.literals_ofLiterals]
    exact List.mem_map_of_mem (f := satLiteral) ht
  · change assignment primary initial state.events.toList (t.natAbs-1+1) = decide (0<t)
    rw [show t.natAbs - 1 + 1 = t.natAbs by omega]
    exact beq_iff_eq.mp valid

/-- Export the actual `CNF` used by the satisfaction theorem. The replay can
    compare this serialization to its original inputs before checking LRAT. -/
def writeReplayInputs (dir : System.FilePath) : IO Unit := do
  for k in keys do
    let filename := s!"{k.1.order}-{k.1.2.toNat}-{k.2.label}.cnf"
    let state := build k
    unless traceValidBool 1 state.events.toList do
      throw (IO.userError s!"invalid variable trace for {filename}")
    IO.FS.writeFile (dir / filename) (exactCNF state).dimacs

#print axioms assignment_satisfies

end SixEdge.Formula
