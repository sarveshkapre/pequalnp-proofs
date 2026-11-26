import SixEdgeOutputProof

namespace SixEdge.Formula

set_option maxHeartbeats 2000000

/-- Evaluate returned literals using the interpreted trace. Required clauses
    do not determine their values and are handled by a separate audit. -/
def BuildDefines (primary : Input → Bool) (v : Values) {α : Type}
    (pre : Prop) (m : Build α) (post : α → Prop) : Prop :=
  ∀ s, let (a,t) := m.run s
    s.events.toList ⊆ t.events.toList ∧
      ((∀ e ∈ t.events.toList, Interprets primary v e) → pre → post a)

namespace BuildDefines

theorem pure (primary : Input → Bool) (v : Values) {α : Type} {pre : Prop} {post : α → Prop}
    (a : α) (h : pre → post a) : BuildDefines primary v pre (Pure.pure a) post :=
  fun _ => ⟨List.Subset.refl _,fun _ => h⟩

theorem bind {primary : Input → Bool} {v : Values} {α β : Type}
    {pre : Prop} {m : Build α} {f : α → Build β} {p : α → Prop} {q : β → Prop}
    (first : BuildDefines primary v pre m p) (next : ∀ a, BuildDefines primary v (pre ∧ p a) (f a) q) :
    BuildDefines primary v pre (m >>= f) q := by
  intro s
  have h := first s
  have k := next (m.run s).1 (m.run s).2
  exact ⟨List.Subset.trans h.1 k.1,fun defs ready =>
    k.2 defs ⟨ready,h.2 (fun e he => defs e (k.1 he)) ready⟩⟩

theorem mono {primary : Input → Bool} {v : Values} {α : Type}
    {pre ready : Prop} {m : Build α} {p q : α → Prop}
    (first : BuildDefines primary v pre m p) (before : ready → pre) (after : ready → ∀ a, p a → q a) :
    BuildDefines primary v ready m q := fun s =>
  ⟨(first s).1,fun defs h => after h _ ((first s).2 defs (before h))⟩

theorem bind_without_post {primary : Input → Bool} {v : Values} {α β : Type}
    {pre : Prop} {m : Build α} {f : α → Build β} {q : β → Prop}
    (first : BuildDefines primary v True m (fun _ => True))
    (next : ∀ a, BuildDefines primary v pre (f a) q) :
    BuildDefines primary v pre (m >>= f) q :=
  bind (first.mono (fun _ => trivial) (fun _ _ h => h))
    (fun a => (next a).mono And.left (fun _ _ h => h))

theorem mapM {primary : Input → Bool} {v : Values} {α β : Type}
    (xs : List α) {pre : Prop} {f : α → Build β} {r : α → β → Prop}
    (each : ∀ a, BuildDefines primary v (pre ∧ a ∈ xs) (f a) (r a)) :
    BuildDefines primary v pre (xs.mapM f) (List.Forall₂ r xs) := by
  induction xs with
  | nil => exact pure _ _ _ (fun _ => List.Forall₂.nil)
  | cons x xs ih =>
    rw [List.mapM_cons]
    refine bind ((each x).mono (fun h => ⟨h,List.mem_cons_self⟩) (fun _ _ h => h)) ?_
    intro y
    have checked := ih (fun a => (each a).mono
      (fun ⟨hp,ha⟩ => ⟨hp,List.mem_cons_of_mem _ ha⟩) (fun _ _ h => h))
    refine bind (checked.mono And.left (fun _ _ h => h)) ?_
    intro ys
    exact pure _ _ _ (fun ⟨⟨_,h⟩,tail⟩ => List.Forall₂.cons h tail)

theorem forM {primary : Input → Bool} {v : Values} {α : Type}
    (xs : List α) {f : α → Build Unit}
    (each : ∀ a, BuildDefines primary v True (f a) (fun _ => True)) :
    BuildDefines primary v True (xs.forM f) (fun _ => True) := by
  induction xs with
  | nil => exact pure _ _ _ (fun _ => trivial)
  | cons x xs ih =>
    change BuildDefines primary v _ (f x >>= fun _ => xs.forM f) _
    exact bind (each x) (fun _ => ih.mono (fun _ => trivial) (fun _ _ h => h))

end BuildDefines

theorem Audited.defines {primary : Input → Bool} {v : Values} {α : Type}
    {pre : Prop} {m : Build α} {post : α → Prop} (audit : Audited primary v pre m post) :
    BuildDefines primary v pre m post := by
  intro s
  obtain ⟨suffix,appended,checked⟩ := audit s
  constructor
  · intro e he
    rw [appended]
    exact List.mem_append_left _ he
  · intro defs ready
    exact (checked (fun e he => defs e (appended ▸ List.mem_append_right _ he)) ready).2

private theorem defines_require (p : Input → Bool) (v : Values) (r : Rule) (ts : List Lit) :
    BuildDefines p v True (require r ts) (fun _ => True) := by
  intro s
  refine ⟨?_,fun _ _ => trivial⟩
  intro e he
  change e ∈ (s.events.push (.require r ts)).toList
  rw [Array.toList_push]
  exact List.mem_append_left _ he

private theorem or_keeps_events (ts : List Lit) (s : BuildState) :
    s.events.toList ⊆ ((makeOr ts).run s).2.events.toList := by
  unfold makeOr
  split
  · exact List.Subset.refl _
  · dsimp only
    generalize ((ts.filter (· != -1)).eraseDups) = kept
    cases kept with
    | nil => exact List.Subset.refl _
    | cons x rest =>
      cases rest with
      | nil => exact List.Subset.refl _
      | cons y more =>
        intro e he
        change e ∈ (s.events.push _).toList
        rw [Array.toList_push]
        exact List.mem_append_left _ he

private theorem defines_and_prefix (p : Input → Bool) (v : Values) (ts : List Lit) :
    BuildDefines p v True (makeAnd ts) (fun _ => True) := by
  intro s
  exact ⟨or_keeps_events (ts.map Neg.neg) s,fun _ _ => trivial⟩

private theorem defines_one (p : Input → Bool) (v : Values) (r : Rule) (ts : List Lit) :
    BuildDefines p v True (one r ts) (fun _ => True) := by
  unfold one
  refine BuildDefines.bind (defines_require p v r ts) (fun _ => ?_)
  exact (BuildDefines.forM (pairs ts) (fun x => defines_require p v r [-x.1,-x.2])).mono
    (fun _ => trivial) (fun _ _ h => h)

private theorem defines_eligible (p : Input → Bool) (v : Values) (src tgt : Array Lit) (sel : Lit) :
    BuildDefines p v True (eligible src tgt sel) (fun _ => True) := by
  unfold eligible
  refine BuildDefines.bind (defines_require p v .rawNonempty (-sel :: src.toList)) (fun _ => ?_)
  exact (BuildDefines.forM (src.toList.zip tgt.toList) (fun x =>
    defines_require p v .rawSubset [-sel,-x.1,x.2])).mono (fun _ => trivial) (fun _ _ h => h)

private theorem defines_portHost (p : Input → Bool) (v : Values) (bank : Leaf) (j : Nat)
    (h : Lit) (atom : Array Lit) : BuildDefines p v True (checkPortHost bank j h atom) (fun _ => True) := by
  unfold checkPortHost
  refine BuildDefines.bind (BuildDefines.forM (List.range 26) (fun x =>
    defines_require p v .hostSupport [-h,-atom[x]!,rawAt bank x])) (fun _ => ?_)
  split
  · refine BuildDefines.bind (BuildDefines.mapM (pairs (bank.map Prod.fst)) (fun x =>
      (defines_and_prefix p v [atom[x.1]!,atom[x.2]!]).mono (fun _ => trivial) (fun _ _ _ => trivial))) ?_
    intro ts
    exact (defines_require p v .nontrivialHost (-h :: ts)).mono (fun _ => trivial) (fun _ _ h => h)
  · exact BuildDefines.pure p v () (fun _ => trivial)

private theorem defines_portHosts (p : Input → Bool) (v : Values) (hosts : Array Leaf) (i b : Nat)
    (mode : Lit) (atom : Array Lit) : BuildDefines p v True (checkPortHosts hosts i b mode atom) (fun _ => True) := by
  unfold checkPortHosts
  refine BuildDefines.bind (defines_require p v .nonemptyAtom (-mode :: atom.toList)) (fun _ => ?_)
  refine BuildDefines.bind ((BuildDefines.forM atom.toList (fun w =>
    defines_require p v .atomMode [-w,mode])).mono (fun _ => trivial) (fun _ _ h => h)) (fun _ => ?_)
  refine BuildDefines.bind (BuildDefines.mapM (List.range hosts.size) (fun j =>
    (audit_choose p v (.host i b j)).defines.mono (fun _ => trivial) (fun _ _ _ => trivial))) ?_
  intro host
  refine BuildDefines.bind ((BuildDefines.forM host (fun h => defines_require p v .hostMode [-h,mode])).mono
    (fun _ => trivial) (fun _ _ h => h)) (fun _ => ?_)
  refine BuildDefines.bind ((defines_require p v .hostChoice (-mode :: host)).mono
    (fun _ => trivial) (fun _ _ h => h)) (fun _ => ?_)
  refine BuildDefines.bind ((BuildDefines.forM (pairs host) (fun x =>
    defines_require p v .hostChoice [-x.1,-x.2])).mono (fun _ => trivial) (fun _ _ h => h)) (fun _ => ?_)
  exact (BuildDefines.forM (List.range hosts.size) (fun j => defines_portHost p v hosts[j]! j host[j]! atom)).mono
    (fun _ => trivial) (fun _ _ h => h)


private theorem defines_record (p : Input → Bool) (v : Values) (j : Nat) (sel : Lit) :
    BuildDefines p v True (recordUse j sel) (fun _ => True) :=
  (audit_record_use p v j sel).defines

private theorem defines_or_prefix (p : Input → Bool) (v : Values) (ts : List Lit) :
    BuildDefines p v True (makeOr ts) (fun _ => True) :=
  fun s => ⟨or_keeps_events ts s,fun _ _ => trivial⟩

private theorem defines_gated_prefix (p : Input → Bool) (v : Values)
    (reads : List (Nat × Lit)) (read : Nat → Lit) :
    BuildDefines p v True (gatedReads reads read) (fun _ => True) := by
  unfold gatedReads
  exact (BuildDefines.mapM reads (fun x =>
    (defines_and_prefix p v [x.2,read x.1]).mono (fun _ => trivial) (fun _ _ _ => trivial))).mono
      id (fun _ _ _ => trivial)

private theorem defines_portAncestors (p : Input → Bool) (v : Values) (stages : Array Stage)
    (direct promoted : List (Nat × Lit)) (canonical : Bool) :
    BuildDefines p v True (portAncestors stages direct promoted canonical) (fun _ => True) := by
  unfold portAncestors
  split
  · apply BuildDefines.bind
    · apply BuildDefines.mapM
      intro q
      refine BuildDefines.bind ((defines_gated_prefix p v direct (fun j => stages[j]!.ancestors[q]!)).mono
        (fun _ => trivial) (fun _ _ h => h)) ?_
      intro ds
      refine BuildDefines.bind ((defines_gated_prefix p v promoted (fun j => stages[j]!.ancestors[q]!)).mono
        (fun _ => trivial) (fun _ _ h => h)) ?_
      intro ps
      exact (defines_or_prefix p v (ds ++ ps)).mono (fun _ => trivial) (fun _ _ h => h)
    · intro lits
      exact BuildDefines.pure p v lits.toArray (fun _ => trivial)
  · exact BuildDefines.pure p v #[] (fun _ => trivial)

private theorem defines_choices (p : Input → Bool) (v : Values) (n : Nat) (name : Nat → Input) :
    BuildDefines p v True ((List.range n).mapM fun j => choose (name j))
      (List.Forall₂ (fun j t => Denotes v (p (name j)) t) (List.range n)) :=
  BuildDefines.mapM (List.range n) (fun j => (audit_choose p v (name j)).defines.mono
    (fun _ => trivial) (fun _ _ h => h))

/-- The emitted read selectors follow the encoder's ordered list of slots. -/
structure PortReads (v : Values) (bit : Nat → Bool) (slots : List Nat) (reads : List (Nat × Lit)) : Prop where
  slots_eq : reads.map Prod.fst = slots
  selects : ∀ s ∈ reads, Denotes v (bit s.1) s.2

private theorem defines_promotion (p : Input → Bool) (v : Values) (stages : Array Stage) (i b j : Nat)
    (mode : Lit) (atom : Array Lit) :
    BuildDefines p v True (choosePromotion stages i b j mode atom)
      (fun s => s.1 = j ∧ Denotes v (p (.promotion i b j)) s.2) := by
  unfold choosePromotion
  refine BuildDefines.bind (audit_choose p v (.promotion i b j)).defines ?_
  intro sel
  refine BuildDefines.bind ((defines_require p v .promotionMode [-sel,mode]).mono
    (fun _ => trivial) (fun _ _ h => h)) (fun _ => ?_)
  refine BuildDefines.bind ((defines_eligible p v stages[j]!.raw atom sel).mono
    (fun _ => trivial) (fun _ _ h => h)) (fun _ => ?_)
  refine BuildDefines.bind ((defines_record p v j sel).mono (fun _ => trivial) (fun _ _ h => h)) (fun _ => ?_)
  exact BuildDefines.pure p v (j,sel) (fun h => ⟨rfl,h.1.1.1.2⟩)

private theorem relations_to_reads {v : Values} {bit : Nat → Bool} {xs : List Nat} {rs : List (Nat × Lit)}
    (related : List.Forall₂ (fun j s => s.1 = j ∧ Denotes v (bit j) s.2) xs rs) :
    PortReads v bit xs rs := by
  induction related with
  | nil => exact ⟨rfl,by simp⟩
  | cons head _ ih =>
    refine ⟨by simp only [List.map_cons,head.1,ih.slots_eq],?_⟩
    intro s hs
    rcases List.mem_cons.mp hs with rfl | rest
    · simpa only [head.1] using head.2
    · exact ih.selects s rest

private theorem direct_port_reads {v : Values} {n : Nat} {bit : Nat → Bool} {ds : Array Lit}
    (meaning : ArrayDenotes v n bit ds) : PortReads v bit (List.range n) (directReads ds) := by
  refine ⟨?_,?_⟩
  · rw [directReads,List.map_map,meaning.1]
    exact List.map_id _
  · intro s hs
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hs
    exact meaning.2 j (by simpa only [meaning.1] using List.mem_range.mp hj)

private theorem defines_gated_reads (p : Input → Bool) (v : Values) (reads : List (Nat × Lit))
    (read : Nat → Lit) (selector bits : Nat → Bool) :
    BuildDefines p v
      (v 1 = true ∧ ∀ s ∈ reads, Denotes v (selector s.1) s.2 ∧ Denotes v (bits s.1) (read s.1))
      (gatedReads reads read) (DenotesList v (reads.map fun s => selector s.1 && bits s.1)) := by
  unfold gatedReads
  let rel (s : Nat × Lit) (t : Lit) := Denotes v (selector s.1 && bits s.1) t
  have each s : BuildDefines p v
        ((v 1 = true ∧ ∀ t ∈ reads, Denotes v (selector t.1) t.2 ∧ Denotes v (bits t.1) (read t.1)) ∧ s ∈ reads)
        (makeAnd [s.2,read s.1]) (rel s) := by
    refine (denote_pair v s.2 (read s.1) (selector s.1) (bits s.1) (primary := p)).defines.mono ?_
      (fun _ _ h => h)
    exact fun h => ⟨h.1.1,h.1.2 _ h.2⟩
  have lift {rs ts} (h : List.Forall₂ rel rs ts) :
      DenotesList v (rs.map fun s => selector s.1 && bits s.1) ts := by
    induction h with
    | nil => exact List.Forall₂.nil
    | cons h _ ih => exact List.Forall₂.cons h ih
  exact (BuildDefines.mapM reads each).mono id (fun _ _ h => lift h)

private theorem read_bits_eq {v : Values} {select : Nat → Bool} {slots : List Nat} {reads : List (Nat × Lit)}
    (bank : PortReads v select slots reads) (bit : Nat → Bool) :
    (reads.map fun r => select r.1 && bit r.1) = slots.map (fun j => select j && bit j) := by
  rw [← bank.slots_eq,List.map_map]
  rfl

private theorem map_denotes {α : Type} (v : Values) (xs : List α) (bit : α → Bool) (lit : α → Lit)
    (meaning : ∀ a ∈ xs, Denotes v (bit a) (lit a)) : DenotesList v (xs.map bit) (xs.map lit) := by
  induction xs with
  | nil => exact List.Forall₂.nil
  | cons a as ih =>
    exact List.Forall₂.cons (meaning a List.mem_cons_self)
      (ih (fun b hb => meaning b (List.mem_cons_of_mem _ hb)))

def operandsRawBit (p : Input → Bool) (n i b : Nat) (prior : Nat → Nat → Bool) (v : Nat) : Bool :=
  p (.atom i b v) || (List.range n).any (fun j => p (.direct i b j) && prior j v)

def operandsSampleBit (p : Input → Bool) (stages : Array Stage) (i b : Nat)
    (prior : Nat → Nat → Bool) (k : Nat) : Bool :=
  ((samples[k]!).any fun v => p (.atom i b v)) ||
    ((promotionSlots stages).any (fun j => p (.promotion i b j) && prior j k) ||
      (List.range stages.size).any (fun j => p (.direct i b j) && prior j k))

private theorem defines_lit_array (primary : Input → Bool) (v : Values) (n : Nat)
    (emit : Nat → Build Lit) (bits : Nat → Bool) (pre : Prop)
    (each : ∀ j, BuildDefines primary v (pre ∧ j ∈ List.range n) (emit j) (Denotes v (bits j))) :
    BuildDefines primary v pre (buildLitArray n emit) (ArrayDenotes v n bits) := by
  unfold buildLitArray
  refine BuildDefines.bind (BuildDefines.mapM (List.range n) each) ?_
  intro lits
  exact BuildDefines.pure primary v lits.toArray (fun h => list_to_array_denotes h.2)

attribute [local irreducible] samples List.range

theorem defines_port_raw (p : Input → Bool) (v : Values) (stages : Array Stage) (i b : Nat)
    (atom : Array Lit) (reads : List (Nat × Lit)) (prior : Nat → Nat → Bool) :
    BuildDefines p v
      (v 1 = true ∧ ArrayDenotes v 26 (fun x => p (.atom i b x)) atom ∧
        PortReads v (fun j => p (.direct i b j)) (List.range stages.size) reads ∧
        ∀ j < stages.size, ArrayDenotes v 26 (prior j) stages[j]!.raw)
      (portRaw stages atom reads) (ArrayDenotes v 26 (operandsRawBit p stages.size i b prior)) := by
  unfold portRaw
  refine defines_lit_array p v 26 _ (operandsRawBit p stages.size i b prior) _ ?_
  intro x
  refine BuildDefines.bind ((defines_gated_reads p v reads (fun j => stages[j]!.raw[x]!)
      (fun j => p (.direct i b j)) (fun j => prior j x)).mono ?_ (fun _ _ h => h)) ?_
  · rintro ⟨⟨one,_,bank,raw⟩,mem⟩
    refine ⟨one,fun s hs => ⟨bank.selects s hs,?_⟩⟩
    have slot : s.1 ∈ List.range stages.size := bank.slots_eq ▸ List.mem_map_of_mem hs
    exact (raw s.1 (List.mem_range.mp slot)).2 x (List.mem_range.mp mem)
  · intro terms
    let bits := reads.map fun s => p (.direct i b s.1) && prior s.1 x
    refine (denote_any v (p (.atom i b x) :: bits) (atom[x]! :: terms) (primary := p)).defines.mono ?_ ?_
    · rintro ⟨⟨⟨one,atomBits,_,_⟩,xmem⟩,meaning⟩
      exact ⟨one,List.Forall₂.cons (atomBits.2 x (List.mem_range.mp xmem)) meaning⟩
    · rintro ⟨⟨⟨_,_,chosen,_⟩,_⟩,_⟩ t h
      dsimp only [bits] at h
      rw [read_bits_eq chosen (fun j => prior j x)] at h
      simpa only [operandsRawBit,List.any_cons,id_eq,List.any_map,Function.comp_def] using h

theorem defines_port_samples (p : Input → Bool) (v : Values) (stages : Array Stage) (i b : Nat)
    (atom : Array Lit) (direct promoted : List (Nat × Lit)) (prior : Nat → Nat → Bool) :
    BuildDefines p v
      (v 1 = true ∧ ArrayDenotes v 26 (fun x => p (.atom i b x)) atom ∧
        PortReads v (fun j => p (.direct i b j)) (List.range stages.size) direct ∧
        PortReads v (fun j => p (.promotion i b j)) (promotionSlots stages) promoted ∧
        (∀ k < samples.size, ∀ x ∈ samples[k]!, x < 26) ∧
        ∀ j < stages.size, ArrayDenotes v samples.size (prior j) stages[j]!.values)
      (portSamples stages atom direct promoted) (ArrayDenotes v samples.size (operandsSampleBit p stages i b prior)) := by
  unfold portSamples
  refine defines_lit_array p v samples.size _ (operandsSampleBit p stages i b prior) _ ?_
  intro k
  refine BuildDefines.bind ((defines_gated_reads p v promoted (fun j => stages[j]!.values[k]!)
      (fun j => p (.promotion i b j)) (fun j => prior j k)).mono ?_ (fun _ _ h => h)) ?_
  · rintro ⟨⟨one,_,_,promos,_,values⟩,kBound⟩
    refine ⟨one,fun s hs => ⟨promos.selects s hs,?_⟩⟩
    have slot : s.1 ∈ promotionSlots stages := promos.slots_eq ▸ List.mem_map_of_mem hs
    exact (values _ (List.mem_range.mp (List.mem_filter.mp slot).1)).2 k (List.mem_range.mp kBound)
  · intro ps
    refine BuildDefines.bind ((defines_gated_reads p v direct (fun j => stages[j]!.values[k]!)
      (fun j => p (.direct i b j)) (fun j => prior j k)).mono ?_ (fun _ _ h => h)) ?_
    · rintro ⟨⟨⟨one,_,chosen,_,_,values⟩,kBound⟩,_⟩
      refine ⟨one,fun s hs => ⟨chosen.selects s hs,?_⟩⟩
      have slot : s.1 ∈ List.range stages.size := chosen.slots_eq ▸ List.mem_map_of_mem hs
      exact (values _ (List.mem_range.mp slot)).2 k (List.mem_range.mp kBound)
    · intro ds
      let atomBits := samples[k]!.map fun x => p (.atom i b x)
      let promoBits := promoted.map fun s => p (.promotion i b s.1) && prior s.1 k
      let directBits := direct.map fun s => p (.direct i b s.1) && prior s.1 k
      refine (denote_any v (atomBits ++ promoBits ++ directBits)
        ((samples[k]!).map (fun x => atom[x]!) ++ ps ++ ds) (primary := p)).defines.mono ?_ ?_
      · rintro ⟨⟨⟨⟨one,atoms,_,_,bounds,_⟩,mem⟩,promoDenotes⟩,directDenotes⟩
        have raw := map_denotes v samples[k]! (fun x => p (.atom i b x)) (fun x => atom[x]!)
          (fun x hx => atoms.2 x (bounds k (List.mem_range.mp mem) x hx))
        exact ⟨one,(raw.append promoDenotes).append directDenotes⟩
      · rintro ⟨⟨⟨⟨_,_,chosen,promos,_,_⟩,_⟩,_⟩,_⟩ t h
        dsimp only [atomBits,promoBits,directBits] at h
        rw [read_bits_eq promos (fun j => prior j k),read_bits_eq chosen (fun j => prior j k)] at h
        simpa only [operandsSampleBit,List.any_append,List.any_map,Function.comp_def,id_eq,Bool.or_assoc] using h


structure PortInputs (v : Values) (stages : Array Stage) (raw vals : Nat → Nat → Bool) : Prop where
  one : v 1 = true
  vertices : ∀ k < samples.size, ∀ x ∈ samples[k]!, x < 26
  raw : ∀ j < stages.size, ArrayDenotes v 26 (raw j) stages[j]!.raw
  values : ∀ j < stages.size, ArrayDenotes v samples.size (vals j) stages[j]!.values

attribute [local irreducible] checkPortHosts choosePromotion portRaw portSamples portAncestors

def operandAncestorBit (p : Input → Bool) (stages : Array Stage) (i b : Nat)
    (prior : Nat → Nat → Bool) (q : Nat) : Bool :=
  (List.range stages.size).any (fun j => p (.direct i b j) && prior j q) ||
    (promotionSlots stages).any (fun j => p (.promotion i b j) && prior j q)

theorem defines_port_ancestors (p : Input → Bool) (v : Values) (stages : Array Stage) (i b : Nat)
    (ds ps : List (Nat × Lit)) (prior : Nat → Nat → Bool) (canonical : Bool) :
    BuildDefines p v (v 1 = true ∧
      (canonical = true → ∀ j < stages.size, ArrayDenotes v 5 (prior j) stages[j]!.ancestors) ∧
      PortReads v (fun j => p (.direct i b j)) (List.range stages.size) ds ∧
      PortReads v (fun j => p (.promotion i b j)) (promotionSlots stages) ps)
      (portAncestors stages ds ps canonical)
      (fun a => canonical = true → ArrayDenotes v 5 (operandAncestorBit p stages i b prior) a) := by
  unfold portAncestors
  cases canonical with
  | false => exact BuildDefines.pure p v #[] (fun _ h => by cases h)
  | true =>
    let pre := v 1 = true ∧ (true = true → ∀ j < stages.size, ArrayDenotes v 5 (prior j) stages[j]!.ancestors) ∧
      PortReads v (fun j => p (.direct i b j)) (List.range stages.size) ds ∧
      PortReads v (fun j => p (.promotion i b j)) (promotionSlots stages) ps
    let emit (q : Nat) : Build Lit := do
      let d ← gatedReads ds fun j => stages[j]!.ancestors[q]!
      let t ← gatedReads ps fun j => stages[j]!.ancestors[q]!
      makeOr (d ++ t)
    change BuildDefines p v pre (buildLitArray 5 emit) _
    refine (defines_lit_array p v 5 emit (operandAncestorBit p stages i b prior) pre ?_).mono id
      (fun _ _ z _ => z)
    intro q
    unfold emit
    have gated (rs : List (Nat × Lit)) (sel : Nat → Bool) (slots : List Nat)
        (get : pre → PortReads v sel slots rs) (bound : ∀ j ∈ slots, j < stages.size) :=
      (defines_gated_reads p v rs (fun j => stages[j]!.ancestors[q]!) sel (fun j => prior j q)).mono
        (fun h : pre ∧ q ∈ List.range 5 => ⟨h.1.1,fun t ht =>
          ⟨(get h.1).selects t ht,(h.1.2.1 rfl t.1 (bound _ ((get h.1).slots_eq ▸ List.mem_map_of_mem ht))).2 q
            (List.mem_range.mp h.2)⟩⟩) (fun _ _ z => z)
    refine BuildDefines.bind (gated ds _ _ (fun h => h.2.2.1) (fun _ h => List.mem_range.mp h)) ?_
    intro d
    refine BuildDefines.bind ((gated ps _ _ (fun h => h.2.2.2)
      (fun _ h => List.mem_range.mp (List.mem_filter.mp h).1)).mono And.left (fun _ _ z => z)) ?_
    intro t
    refine (denote_any v _ (d ++ t) (primary := p)).defines.mono
      (fun h => ⟨h.1.1.1.1,h.1.2.append h.2⟩) ?_
    rintro ⟨⟨⟨h,_⟩,_⟩,_⟩ lit z
    rw [read_bits_eq h.2.2.1 (fun j => prior j q),read_bits_eq h.2.2.2 (fun j => prior j q)] at z
    simpa only [operandAncestorBit,List.any_append,List.any_map,Function.comp_def,id_eq] using z

/-- The exact port emitter reads the raw support from atoms and direct wires.
    A promotion supplies a sample value but adds no new raw inputs. -/
theorem buildPort_tables (p : Input → Bool) (v : Values) (stages : Array Stage) (hosts : Array Leaf)
    (i b : Nat) (canonical : Bool) (raw vals : Nat → Nat → Bool)
    (extra : Prop) (result : Array Lit → Prop)
    (anc : ∀ ds ps, BuildDefines p v
      (v 1 = true ∧ extra ∧ PortReads v (fun j => p (.direct i b j)) (List.range stages.size) ds ∧
        PortReads v (fun j => p (.promotion i b j)) (promotionSlots stages) ps)
      (portAncestors stages ds ps canonical) result) :
    BuildDefines p v (PortInputs v stages raw vals ∧ extra) (buildPort stages hosts i b canonical)
      (fun port =>
        ArrayDenotes v 26 (operandsRawBit p stages.size i b raw) port.raw ∧
        ArrayDenotes v samples.size (operandsSampleBit p stages i b vals) port.values ∧ result port.ancestors) := by
  let pre := PortInputs v stages raw vals ∧ extra
  unfold buildPort
  have directChoice : BuildDefines p v pre ((List.range stages.size).mapM fun j => choose (.direct i b j))
      (fun ds => ArrayDenotes v stages.size (fun j => p (.direct i b j)) ds.toArray) :=
    (defines_choices p v stages.size (Input.direct i b)).mono (fun _ => trivial)
      (fun _ _ h => list_to_array_denotes h)
  refine BuildDefines.bind directChoice ?_
  intro ds
  let direct := ds.toArray
  let reads := directReads direct
  let chosen := ArrayDenotes v stages.size (fun j => p (.direct i b j)) direct
  refine BuildDefines.bind_without_post (BuildDefines.forM reads (fun x => defines_record p v x.1 x.2)) ?_
  intro _
  refine BuildDefines.bind_without_post ((audit_choose p v (.atomMode i b)).defines.mono id (fun _ _ _ => trivial)) ?_
  intro mode
  refine BuildDefines.bind_without_post (defines_one p v .portMode (mode :: direct.toList)) ?_
  intro _
  have atomChoice : BuildDefines p v (pre ∧ chosen) ((List.range 26).mapM fun j => choose (.atom i b j))
      (fun lits => ArrayDenotes v 26 (fun j => p (.atom i b j)) lits.toArray) :=
    (defines_choices p v 26 (Input.atom i b)).mono (fun _ => trivial)
      (fun _ _ h => list_to_array_denotes h)
  refine BuildDefines.bind atomChoice ?_
  intro lits
  let atom := lits.toArray
  let atoms := ArrayDenotes v 26 (fun j => p (.atom i b j)) atom
  refine BuildDefines.bind_without_post (defines_portHosts p v hosts i b mode atom) ?_
  intro _
  let haveAtoms := (pre ∧ chosen) ∧ atoms
  refine BuildDefines.bind ((BuildDefines.mapM (promotionSlots stages) (fun j =>
    (defines_promotion p v stages i b j mode atom).mono
      (fun _ : haveAtoms ∧ j ∈ promotionSlots stages => trivial) (fun _ _ h => h))).mono id
    (fun _ _ h => relations_to_reads h)) ?_
  intro promotions
  let prep := haveAtoms ∧ PortReads v (fun j => p (.promotion i b j)) (promotionSlots stages) promotions
  have data (h : prep) : pre ∧ chosen ∧ atoms :=
    ⟨h.1.1.1,h.1.1.2,h.1.2⟩
  refine BuildDefines.bind ((defines_port_raw p v stages i b atom reads raw).mono
    (fun h : prep => ⟨(data h).1.1.one,(data h).2.2,direct_port_reads (data h).2.1,(data h).1.1.raw⟩)
    (fun _ _ h => h)) ?_
  intro r
  let rawMatches := ArrayDenotes v 26 (operandsRawBit p stages.size i b raw) r
  refine BuildDefines.bind ((defines_port_samples p v stages i b atom reads promotions vals).mono
    (fun h : prep ∧ rawMatches => ⟨(data h.1).1.1.one,(data h.1).2.2,direct_port_reads (data h.1).2.1,
      h.1.2,(data h.1).1.1.vertices,(data h.1).1.1.values⟩) (fun _ _ h => h)) ?_
  intro vs
  let valuesMatch := ArrayDenotes v samples.size (operandsSampleBit p stages i b vals) vs
  refine BuildDefines.bind ((anc reads promotions).mono
    (fun h : (prep ∧ rawMatches) ∧ valuesMatch =>
      ⟨(data h.1.1).1.1.one,(data h.1.1).1.2,direct_port_reads (data h.1.1).2.1,h.1.1.2⟩)
    (fun _ _ z => z)) ?_
  intro ancestors
  exact BuildDefines.pure p v _ (fun h => ⟨h.1.1.2,h.1.2,h.2⟩)

/-- The exact port emitter reads the raw support from atoms and direct wires.
    A promotion supplies a sample value but adds no new raw inputs. -/
theorem buildPort_defines (p : Input → Bool) (v : Values) (stages : Array Stage) (hosts : Array Leaf)
    (i b : Nat) (canonical : Bool) (raw vals : Nat → Nat → Bool) :
    BuildDefines p v (PortInputs v stages raw vals) (buildPort stages hosts i b canonical)
      (fun port =>
        ArrayDenotes v 26 (operandsRawBit p stages.size i b raw) port.raw ∧
        ArrayDenotes v samples.size (operandsSampleBit p stages i b vals) port.values) := by
  exact (buildPort_tables p v stages hosts i b canonical raw vals True (fun _ => True)
    (fun ds ps => (defines_portAncestors p v stages ds ps canonical).mono (fun _ => trivial)
      (fun _ _ z => z))).mono (fun h => ⟨h,trivial⟩) (fun _ _ z => ⟨z.1,z.2.1⟩)

#print axioms buildPort_tables

end SixEdge.Formula
