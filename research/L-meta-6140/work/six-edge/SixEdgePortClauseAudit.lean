import SixEdgeBuildPort

namespace SixEdge.Formula

set_option maxHeartbeats 3000000

private theorem Audited.thenKeep {p : Input → Bool} {v : Values} {α β : Type}
    {pre : Prop} {m : Build α} {f : α → Build β} {post : β → Prop}
    (action : Audited p v pre m (fun _ => True))
    (next : ∀ x, Audited p v pre (f x) post) : Audited p v pre (m >>= f) post :=
  Audited.bind action (fun x => (next x).mono And.left (fun _ _ h => h))

private theorem audit_choices (p : Input → Bool) (v : Values) (n : Nat) (name : Nat → Input) :
    Audited p v True ((List.range n).mapM fun j => choose (name j))
      (fun ls => ArrayDenotes v n (fun j => p (name j)) ls.toArray) :=
  (Audited.mapM (List.range n) (fun j => (audit_choose p v (name j)).mono
    (fun _ => trivial) (fun _ _ h => h))).mono id (fun _ _ h => list_to_array_denotes h)

private theorem list_at {v : Values} {n : Nat} {bit : Nat → Bool} {ls : List Lit}
    (h : ArrayDenotes v n bit ls.toArray) (j : Nat) (jb : j < ls.length) :
    Denotes v (bit j) ls[j]! := by
  have size : ls.length = n := h.1
  simpa only [List.getElem!_toArray] using h.2 j (size ▸ jb)

private theorem cons_list_bits {v : Values} {n : Nat} {bit : Nat → Bool} {ls : List Lit} {t : Lit}
    (tail : ArrayDenotes v n (fun j => bit (j+1)) ls.toArray) (head : Denotes v (bit 0) t) :
    ArrayDenotes v (n+1) bit (t :: ls).toArray := by
  have size : ls.length = n := tail.1
  refine ⟨by simp [size],?_⟩
  intro j bound
  have atj : j < (t :: ls).length := by simpa [size] using bound
  cases j with
  | zero => simpa only [List.getElem!_toArray,List.getElem!_cons_zero] using head
  | succ j =>
    have hj : j < ls.length := by simpa using atj
    simpa only [List.getElem!_toArray,List.getElem!_cons_succ] using list_at tail j hj

private theorem list_on {v : Values} {n : Nat} {bit : Nat → Bool} {ls : List Lit}
    (correct : ArrayDenotes v n bit ls.toArray) (h : ∃ j < n, bit j = true) : ClauseTrue v ls := by
  obtain ⟨j,hj,on⟩ := h
  have size : ls.length = n := correct.1
  have bound : j < ls.length := size.symm ▸ hj
  refine ⟨ls[j],List.getElem_mem bound,?_⟩
  simpa only [getElem!_pos ls j bound] using (list_at correct j bound).2.trans on

private theorem pairs_indices {α : Type} [Inhabited α] (xs : List α) {u w : α}
    (mem : (u,w) ∈ pairs xs) :
    ∃ j k, j < k ∧ k < xs.length ∧ xs[j]! = u ∧ xs[k]! = w := by
  induction xs with
  | nil => simp [pairs] at mem
  | cons x xs ih =>
    rcases List.mem_append.mp mem with first | next
    · obtain ⟨y,hy,eq⟩ := List.mem_map.mp first
      obtain ⟨j,bound,elem⟩ := List.mem_iff_getElem.mp hy
      refine ⟨0,j+1,by omega,by simpa using bound,?_ ,?_⟩
      · simpa only [List.getElem!_cons_zero] using congrArg Prod.fst eq
      · simp only [List.getElem!_cons_succ,getElem!_pos xs j bound,elem]
        exact congrArg Prod.snd eq
    · obtain ⟨j,k,jk,kb,eqj,eqk⟩ := ih next
      have k' : k+1 < (x::xs).length := by simpa using kb
      exact ⟨j+1,k+1,by omega,k',by simpa only [List.getElem!_cons_succ] using eqj,
        by simpa only [List.getElem!_cons_succ] using eqk⟩

theorem pairs_distinct {α : Type} (xs : List α) {x y : α}
    (hx : x ∈ xs) (hy : y ∈ xs) (diff : x ≠ y) : (x,y) ∈ pairs xs ∨ (y,x) ∈ pairs xs := by
  induction xs with
  | nil => simp at hx
  | cons a as ih =>
    rcases List.mem_cons.mp hx with atHead | inTail
    · have ym : y ∈ as := (List.mem_cons.mp hy).resolve_left (fun eq => diff (atHead.trans eq.symm))
      rw [atHead]
      exact Or.inl (List.mem_append_left _ (List.mem_map_of_mem ym))
    · rcases List.mem_cons.mp hy with atHead | inTail'
      · rw [atHead]
        exact Or.inr (List.mem_append_left _ (List.mem_map_of_mem inTail))
      · exact (ih inTail inTail').imp (List.mem_append_right _) (List.mem_append_right _)

/-- A selector is fixed by its position and by the bit enabling its group. -/
def Selects (n : Nat) (enabled : Bool) (bits : Nat → Bool) : Prop :=
  ∃ chosen < n, ∀ j < n, bits j = (enabled && (j == chosen))

private theorem Selects.on {n : Nat} {bits : Nat → Bool} (s : Selects n true bits) :
    ∃ j < n, bits j = true := by
  obtain ⟨j,hj,eq⟩ := s
  exact ⟨j,hj,by simp [eq j hj]⟩

private theorem Selects.enabled {n : Nat} {enabled : Bool} {bits : Nat → Bool}
    (s : Selects n enabled bits) {j : Nat} (hj : j < n) (on : bits j = true) : enabled = true := by
  obtain ⟨_,_,eq⟩ := s
  rw [eq j hj] at on
  exact (Bool.and_eq_true_iff.mp on).1

private theorem selects_pair {v : Values} {n : Nat} {enabled : Bool} {bits : Nat → Bool} {ls : List Lit}
    (sel : Selects n enabled bits) (correct : ArrayDenotes v n bits ls.toArray) {a b : Lit}
    (mem : (a,b) ∈ pairs ls) : ClauseTrue v [-a,-b] := by
  obtain ⟨j,k,jk,kb,eqj,eqk⟩ := pairs_indices ls mem
  obtain ⟨chosen,_,eq⟩ := sel
  have size : ls.length = n := correct.1
  have jn : j < n := size ▸ lt_trans jk kb
  have kn : k < n := size ▸ kb
  by_cases h : j = chosen
  · have hb := list_at correct k kb
    have off : (k == chosen) = false := Bool.eq_false_iff.mpr (fun z => by
      have := beq_iff_eq.mp z
      omega)
    rw [eq k kn,off,Bool.and_false,eqk] at hb
    exact ⟨-b,by simp,hb.neg.2⟩
  · have ha := list_at correct j (lt_trans jk kb)
    have off : (j == chosen) = false := Bool.eq_false_iff.mpr (fun z => h (beq_iff_eq.mp z))
    rw [eq j jn,off,Bool.and_false,eqj] at ha
    exact ⟨-a,by simp,ha.neg.2⟩

private theorem audit_at_most_one (p : Input → Bool) (v : Values) (r : Rule) (n : Nat)
    (enabled : Bool) (bit : Nat → Bool) (ls : List Lit) :
    Audited p v (Selects n enabled bit ∧ ArrayDenotes v n bit ls.toArray)
      ((pairs ls).forM fun (x,y) => require r [-x,-y]) (fun _ => True) := by
  apply Audited.forM
  rintro ⟨x,y⟩
  exact (audit_require p v r [-x,-y]).mono (fun h => selects_pair h.1.1 h.1.2 h.2) (fun _ _ h => h)

private theorem audit_one_mode (p : Input → Bool) (v : Values) (n : Nat) (bits : Nat → Bool) (ls : List Lit) :
    Audited p v (Selects n true bits ∧ ArrayDenotes v n bits ls.toArray)
      (one .portMode ls) (fun _ => True) := by
  unfold one
  refine Audited.thenKeep ((audit_require p v .portMode ls).mono
    (fun h => list_on h.2 h.1.on) (fun _ _ h => h)) ?_
  exact fun _ => audit_at_most_one p v .portMode n true bits ls

private theorem if_on_clause {v : Values} {enabled : Bool} {t : Lit} {ls : List Lit}
    (h : Denotes v enabled t) (on : enabled = true → ClauseTrue v ls) : ClauseTrue v (-t :: ls) := by
  cases enabled with
  | false => exact ⟨-t,List.mem_cons_self,h.neg.2⟩
  | true =>
    obtain ⟨l,mem,yes⟩ := on rfl
    exact ⟨l,List.mem_cons_of_mem _ mem,yes⟩

private theorem implies_clause {v : Values} {x y : Bool} {a b : Lit}
    (first : Denotes v x a) (second : Denotes v y b) (imp : x = true → y = true) :
    ClauseTrue v [-a,b] :=
  if_on_clause first (fun on => ⟨b,List.mem_cons_self,second.2.trans (imp on)⟩)


private theorem on_related {v : Values} {α : Type} {bit : α → Bool}
    {xs : List α} {ls : List Lit}
    (h : List.Forall₂ (fun x t => Denotes v (bit x) t) xs ls)
    {x : α} (mem : x ∈ xs) (on : bit x = true) : ClauseTrue v ls := by
  induction h with
  | nil => simp at mem
  | cons head _ ih =>
    rcases List.mem_cons.mp mem with this | later
    · exact ⟨_,List.mem_cons_self,head.2.trans (this ▸ on)⟩
    · obtain ⟨t,ht,on⟩ := ih later
      exact ⟨t,List.mem_cons_of_mem _ ht,on⟩

structure HostCheck (v : Values) (bank : Leaf) (j : Nat) (on : Bool) (bit : Nat → Bool) : Prop where
  points : ∀ x ∈ bank.map Prod.fst, x < 26
  supports : on = true → ∀ x < 26, bit x = true → literalValue v (rawAt bank x) = true
  witnesses : 26 ≤ j → on = true →
    ∃ xy ∈ pairs (bank.map Prod.fst), (bit xy.1 && bit xy.2) = true

private theorem audit_host (p : Input → Bool) (v : Values) (bank : Leaf) (j : Nat) (h : Lit)
    (atom : Array Lit) (on : Bool) (bit : Nat → Bool) :
    Audited p v (v 1 = true ∧ Denotes v on h ∧ ArrayDenotes v 26 bit atom ∧ HostCheck v bank j on bit)
      (checkPortHost bank j h atom) (fun _ => True) := by
  let pre := v 1 = true ∧ Denotes v on h ∧ ArrayDenotes v 26 bit atom ∧ HostCheck v bank j on bit
  have support : Audited p v pre
      ((List.range 26).forM fun x => require .hostSupport [-h,-atom[x]!,rawAt bank x]) (fun _ => True) := by
    apply Audited.forM
    intro x
    refine (audit_require p v .hostSupport _).mono ?_ (fun _ _ z => z)
    intro ⟨⟨_,host,atoms,good⟩,mem⟩
    have bound := List.mem_range.mp mem
    exact if_on_clause host (fun enabled => if_on_clause (atoms.2 x bound)
      (fun active => ⟨_,List.mem_cons_self,good.supports enabled x bound active⟩))
  unfold checkPortHost
  refine Audited.thenKeep support (fun _ => ?_)
  split
  · rename_i large
    let keys := pairs (bank.map Prod.fst)
    let eval (xy : Nat × Nat) := bit xy.1 && bit xy.2
    have pairWork : Audited p v pre
        (keys.mapM fun (x,y) => makeAnd [atom[x]!,atom[y]!])
        (List.Forall₂ (fun xy t => Denotes v (eval xy) t) keys) := by
      apply Audited.mapM
      rintro ⟨x,y⟩
      refine (denote_pair v atom[x]! atom[y]! (bit x) (bit y) (primary := p)).mono ?_ (fun _ _ z => z)
      intro ⟨⟨one,_,atoms,spec⟩,mem⟩
      obtain ⟨a,b,lt,bb,ea,eb⟩ := pairs_indices (bank.map Prod.fst) mem
      have ab := lt_trans lt bb
      rw [getElem!_pos (bank.map Prod.fst) a ab] at ea
      rw [getElem!_pos (bank.map Prod.fst) b bb] at eb
      have xa : x ∈ bank.map Prod.fst := ea ▸ List.getElem_mem ab
      have yb : y ∈ bank.map Prod.fst := eb ▸ List.getElem_mem bb
      exact ⟨one,atoms.2 x (spec.points x xa),atoms.2 y (spec.points y yb)⟩
    refine Audited.bind pairWork ?_
    intro ts
    refine (audit_require p v .nontrivialHost (-h :: ts)).mono ?_ (fun _ _ z => z)
    intro ⟨⟨_,host,_,spec⟩,readings⟩
    apply if_on_clause host
    intro active
    obtain ⟨xy,mem,yes⟩ := spec.witnesses large active
    exact on_related readings mem yes
  · exact Audited.pure p v () (fun _ => trivial)

structure HostChecks (p : Input → Bool) (v : Values) (hosts : Array Leaf) (i b : Nat) : Prop where
  atom_live : p (.atomMode i b) = true → ∃ x < 26, p (.atom i b x) = true
  atom_mode : ∀ x < 26, p (.atom i b x) = true → p (.atomMode i b) = true
  host_select : Selects hosts.size (p (.atomMode i b)) (fun j => p (.host i b j))
  host_check : ∀ j < hosts.size, HostCheck v hosts[j]! j (p (.host i b j)) (fun x => p (.atom i b x))

private theorem audit_hosts (p : Input → Bool) (v : Values) (hosts : Array Leaf) (i b : Nat)
    (mode : Lit) (atom : Array Lit) :
    Audited p v (v 1 = true ∧ Denotes v (p (.atomMode i b)) mode ∧
        ArrayDenotes v 26 (fun x => p (.atom i b x)) atom ∧ HostChecks p v hosts i b)
      (checkPortHosts hosts i b mode atom) (fun _ => True) := by
  let enabled := p (.atomMode i b)
  let sel := fun j => p (.host i b j)
  let bit := fun x => p (.atom i b x)
  let pre := v 1 = true ∧ Denotes v enabled mode ∧ ArrayDenotes v 26 bit atom ∧ HostChecks p v hosts i b
  have atomLive : Audited p v pre (require .nonemptyAtom (-mode :: atom.toList)) (fun _ => True) := by
    apply (audit_require p v _ _).mono ?_ (fun _ _ z => z)
    exact fun h => if_on_clause h.2.1 (fun enabling =>
      list_on (by simpa using h.2.2.1) (h.2.2.2.atom_live enabling))
  have atomMode : Audited p v pre (atom.toList.forM fun w => require .atomMode [-w,mode]) (fun _ => True) := by
    apply Audited.forM
    intro w
    refine (audit_require p v _ _).mono ?_ (fun _ _ z => z)
    rintro ⟨⟨_,matchMode,atoms,facts⟩,mem⟩
    obtain ⟨x,xb,eq⟩ := List.mem_iff_getElem.mp mem
    have bnd : x < 26 := by simpa only [Array.length_toList, atoms.1] using xb
    have has := list_at (bit := bit) (ls := atom.toList) (by simpa using atoms) x xb
    rw [getElem!_pos atom.toList x xb,eq] at has
    exact implies_clause has matchMode (facts.atom_mode x bnd)
  unfold checkPortHosts
  refine Audited.thenKeep atomLive (fun _ => Audited.thenKeep atomMode (fun _ => ?_))
  refine Audited.bind ((audit_choices p v hosts.size (.host i b)).mono
    (fun _ : pre => trivial) (fun _ _ z => z)) ?_
  intro host
  let ready := pre ∧ ArrayDenotes v hosts.size sel host.toArray
  have hostMode : Audited p v ready (host.forM fun h => require .hostMode [-h,mode]) (fun _ => True) := by
    apply Audited.forM
    intro h
    refine (audit_require p v _ _).mono ?_ (fun _ _ z => z)
    rintro ⟨⟨⟨_,meaning,_,facts⟩,checked⟩,mem⟩
    obtain ⟨x,xb,eq⟩ := List.mem_iff_getElem.mp mem
    have size : host.length = hosts.size := checked.1
    have bnd : x < hosts.size := size ▸ xb
    have selOn := list_at checked x xb
    rw [getElem!_pos host x xb,eq] at selOn
    exact implies_clause selOn meaning (facts.host_select.enabled bnd)
  have hostChoice : Audited p v ready (require .hostChoice (-mode :: host)) (fun _ => True) := by
    refine (audit_require p v _ _).mono ?_ (fun _ _ z => z)
    rintro ⟨⟨_,meaning,_,facts⟩,checked⟩
    apply if_on_clause meaning
    intro active
    have choice : Selects hosts.size true sel := active ▸ facts.host_select
    exact list_on checked choice.on
  have hostMutex : Audited p v ready
      ((pairs host).forM fun (h,k) => require .hostChoice [-h,-k]) (fun _ => True) :=
    (audit_at_most_one p v .hostChoice hosts.size enabled sel host).mono
      (fun h => ⟨h.1.2.2.2.host_select,h.2⟩) (fun _ _ z => z)
  refine Audited.thenKeep hostMode (fun _ => Audited.thenKeep hostChoice (fun _ =>
    Audited.thenKeep hostMutex (fun _ => ?_)))
  apply Audited.forM
  intro j
  refine (audit_host p v hosts[j]! j host[j]! atom (sel j) bit).mono ?_ (fun _ _ z => z)
  rintro ⟨⟨⟨one,_,atoms,facts⟩,checked⟩,mem⟩
  have bnd := List.mem_range.mp mem
  have size : host.length = hosts.size := checked.1
  exact ⟨one,list_at checked j (size.symm ▸ bnd),atoms,
    facts.host_check j bnd⟩

structure PromotionChecks (p : Input → Bool) (v : Values) (stages : Array Stage)
    (i b j : Nat) (raw : Nat → Bool) : Prop where
  prior : ArrayDenotes v 26 raw stages[j]!.raw
  mode : p (.promotion i b j) = true → p (.atomMode i b) = true
  live : p (.promotion i b j) = true → ∃ x < 26, raw x = true
  subset : p (.promotion i b j) = true → ∀ x < 26, raw x = true → p (.atom i b x) = true

private theorem audit_promotion (p : Input → Bool) (v : Values) (stages : Array Stage) (i b j : Nat)
    (mode : Lit) (atom : Array Lit) (raw : Nat → Bool) :
    Audited p v (Denotes v (p (.atomMode i b)) mode ∧ ArrayDenotes v 26 (fun x => p (.atom i b x)) atom ∧
        PromotionChecks p v stages i b j raw)
      (choosePromotion stages i b j mode atom) (fun _ => True) := by
  let pre := Denotes v (p (.atomMode i b)) mode ∧ ArrayDenotes v 26 (fun x => p (.atom i b x)) atom ∧
    PromotionChecks p v stages i b j raw
  unfold choosePromotion
  refine Audited.bind ((audit_choose p v (.promotion i b j)).mono (fun _ : pre => trivial) (fun _ _ z => z)) ?_
  intro pick
  let ready := pre ∧ Denotes v (p (.promotion i b j)) pick
  have modeClause : Audited p v ready (require .promotionMode [-pick,mode]) (fun _ => True) :=
    (audit_require p v _ _).mono (fun h => implies_clause h.2 h.1.1 h.1.2.2.mode) (fun _ _ z => z)
  have eligibleClause : Audited p v ready (eligible stages[j]!.raw atom pick) (fun _ => True) := by
    refine (audit_eligible p v _ _ _).mono ?_ (fun _ _ z => z)
    rintro ⟨⟨_,atoms,conditions⟩,meaning⟩
    refine ⟨meaning.1,conditions.prior.nonzero,?_⟩
    intro on
    have active := meaning.2.symm.trans on
    exact raw_subset_of_denotes conditions.prior atoms (conditions.live active) (conditions.subset active)
  refine Audited.thenKeep modeClause (fun _ => Audited.thenKeep eligibleClause (fun _ => ?_))
  refine Audited.thenKeep ((audit_record_use p v j pick).mono (fun _ : ready => trivial) (fun _ _ z => z)) ?_
  exact fun _ => Audited.pure p v (j,pick) (fun _ => trivial)


-- The rest of the port builder only adds Boolean definitions. Those events
-- cannot add a required clause, whatever literals the builder is given.
theorem audit_define_or (p : Input → Bool) (v : Values) (ts : List Lit) :
    Audited p v True (makeOr ts) (fun _ => True) := by
  unfold makeOr
  split
  · exact Audited.pure p v 1 (fun _ => trivial)
  · dsimp only
    generalize ((ts.filter (· != -1)).eraseDups) = kept
    cases kept with
    | nil => exact Audited.pure p v (-1) (fun _ => trivial)
    | cons x rest =>
      cases rest with
      | nil => exact Audited.pure p v x (fun _ => trivial)
      | cons y more =>
        intro s
        exact ⟨[.defineOr (s.variableCount+1) (x::y::more)],by simp,by simp [Meets]⟩

private theorem audit_gated_reads (p : Input → Bool) (v : Values) (reads : List (Nat × Lit)) (read : Nat → Lit) :
    Audited p v True (gatedReads reads read) (fun _ => True) := by
  unfold gatedReads
  have each (s : Nat × Lit) :
      Audited p v (True ∧ s ∈ reads) (makeAnd [s.2,read s.1]) (fun _ => True) := by
    unfold makeAnd
    refine Audited.thenKeep ((audit_define_or p v _).mono (fun _ => trivial) (fun _ _ z => z)) ?_
    intro t
    exact Audited.pure p v (-t) (fun _ => trivial)
  exact (Audited.mapM reads each).mono id (fun _ _ _ => trivial)

theorem audit_literal_array (p : Input → Bool) (v : Values) (n : Nat) (emit : Nat → Build Lit)
    (rows : ∀ j, Audited p v True (emit j) (fun _ => True)) :
    Audited p v True (buildLitArray n emit) (fun _ => True) := by
  unfold buildLitArray
  refine Audited.bind (Audited.mapM (List.range n) (fun j =>
    (rows j).mono (fun _ => trivial) (fun _ _ h => h))) ?_
  intro ts
  exact Audited.pure p v ts.toArray (fun _ => trivial)

attribute [local irreducible] buildLitArray samples List.range

private theorem audit_raw_definitions (p : Input → Bool) (v : Values) (stages : Array Stage)
    (atom : Array Lit) (direct : List (Nat × Lit)) :
    Audited p v True (portRaw stages atom direct) (fun _ => True) := by
  unfold portRaw
  apply audit_literal_array
  intro j
  exact Audited.thenKeep (audit_gated_reads p v direct (fun x => stages[x]!.raw[j]!))
    (fun terms => audit_define_or p v (atom[j]! :: terms))

private theorem audit_sample_definitions (p : Input → Bool) (v : Values) (stages : Array Stage)
    (atom : Array Lit) (direct promoted : List (Nat × Lit)) :
    Audited p v True (portSamples stages atom direct promoted) (fun _ => True) := by
  unfold portSamples
  apply audit_literal_array
  intro j
  refine Audited.thenKeep (audit_gated_reads p v promoted (fun x => stages[x]!.values[j]!)) ?_
  intro ps
  refine Audited.thenKeep (audit_gated_reads p v direct (fun x => stages[x]!.values[j]!)) ?_
  exact fun ds => audit_define_or p v ((samples[j]!).map (fun x => atom[x]!) ++ ps ++ ds)

private theorem audit_ancestor_definitions (p : Input → Bool) (v : Values) (stages : Array Stage)
    (direct promoted : List (Nat × Lit)) (canonical : Bool) :
    Audited p v True (portAncestors stages direct promoted canonical) (fun _ => True) := by
  unfold portAncestors
  split
  · refine Audited.bind (Audited.mapM (List.range 5) (r := fun _ _ => True) (fun j => ?_)) ?_
    · refine Audited.thenKeep ((audit_gated_reads p v direct (fun x => stages[x]!.ancestors[j]!)).mono
        (fun _ => trivial) (fun _ _ z => z)) ?_
      intro ds
      refine Audited.thenKeep ((audit_gated_reads p v promoted (fun x => stages[x]!.ancestors[j]!)).mono
        (fun _ => trivial) (fun _ _ z => z)) ?_
      intro ps
      exact (audit_define_or p v (ds ++ ps)).mono (fun _ => trivial) (fun _ _ z => z)
    · intro ts
      exact Audited.pure p v ts.toArray (fun _ => trivial)
  · exact Audited.pure p v #[] (fun _ => trivial)

structure PortClauseChecks (p : Input → Bool) (v : Values) (stages : Array Stage)
    (hosts : Array Leaf) (i b : Nat) (raw : Nat → Nat → Bool) : Prop where
  constant : v 1 = true
  mode : Selects (stages.size+1) true (fun j => p (modeInput i b j))
  hosts : HostChecks p v hosts i b
  promotions : ∀ j ∈ promotionSlots stages, PromotionChecks p v stages i b j (raw j)

attribute [local irreducible] checkPortHosts choosePromotion portRaw portSamples portAncestors

/-- Audits every required clause emitted by the exact port builder and
    identifies its returned mode literals for the subsequent port-order check. -/
theorem audit_buildPort (p : Input → Bool) (v : Values) (stages : Array Stage) (hosts : Array Leaf)
    (i b : Nat) (canonical : Bool) (raw : Nat → Nat → Bool) :
    Audited p v (PortClauseChecks p v stages hosts i b raw) (buildPort stages hosts i b canonical)
      (fun port => ArrayDenotes v (stages.size+1) (fun j => p (modeInput i b j)) port.modes.toArray) := by
  let pre := PortClauseChecks p v stages hosts i b raw
  unfold buildPort
  refine Audited.bind ((audit_choices p v stages.size (.direct i b)).mono
    (fun _ : pre => trivial) (fun _ _ z => z)) ?_
  intro ds
  let direct := ds.toArray
  let reads := directReads direct
  let directs := ArrayDenotes v stages.size (fun j => p (.direct i b j)) direct
  refine Audited.thenKeep ((Audited.forM reads (fun x =>
    (audit_record_use p v x.1 x.2).mono (fun _ : (pre ∧ directs) ∧ x ∈ reads => trivial)
      (fun _ _ z => z)))) ?_
  intro _
  refine Audited.bind ((audit_choose p v (.atomMode i b)).mono
    (fun _ : pre ∧ directs => trivial) (fun _ _ z => z)) ?_
  intro mode
  let enabled := Denotes v (p (.atomMode i b)) mode
  let bits := fun j => p (modeInput i b j)
  let before := (pre ∧ directs) ∧ enabled
  have modes (h : before) : ArrayDenotes v (stages.size+1) bits (mode :: ds).toArray :=
    cons_list_bits h.1.2 h.2
  refine Audited.thenKeep ((audit_one_mode p v (stages.size+1) bits (mode :: direct.toList)).mono
    (fun h : before => ⟨h.1.1.mode,by simpa only [List.toList_toArray] using modes h⟩) (fun _ _ z => z)) ?_
  intro _
  refine Audited.bind ((audit_choices p v 26 (.atom i b)).mono
    (fun _ : before => trivial) (fun _ _ z => z)) ?_
  intro ls
  let atom := ls.toArray
  let ready := before ∧ ArrayDenotes v 26 (fun x => p (.atom i b x)) atom
  refine Audited.thenKeep ((audit_hosts p v hosts i b mode atom).mono
    (fun h : ready => ⟨h.1.1.1.constant,h.1.2,h.2,h.1.1.1.hosts⟩) (fun _ _ z => z)) ?_
  intro _
  have promotions : Audited p v ready ((promotionSlots stages).mapM fun j =>
      choosePromotion stages i b j mode atom) (fun _ => True) := by
    refine (Audited.mapM (promotionSlots stages) (fun j =>
      (audit_promotion p v stages i b j mode atom (raw j)).mono
        (fun h : ready ∧ j ∈ promotionSlots stages => ⟨h.1.1.2,h.1.2,h.1.1.1.1.promotions j h.2⟩)
        (fun _ _ z => z))).mono id (fun _ _ _ => trivial)
  refine Audited.thenKeep promotions ?_
  intro promoted
  refine Audited.thenKeep ((audit_raw_definitions p v stages atom reads).mono
    (fun _ : ready => trivial) (fun _ _ z => z)) ?_
  intro r
  refine Audited.thenKeep ((audit_sample_definitions p v stages atom reads promoted).mono
    (fun _ : ready => trivial) (fun _ _ z => z)) ?_
  intro vs
  refine Audited.thenKeep ((audit_ancestor_definitions p v stages reads promoted canonical).mono
    (fun _ : ready => trivial) (fun _ _ z => z)) ?_
  intro anc
  exact Audited.pure p v (⟨mode :: direct.toList,r,vs,anc⟩ : Port)
    (fun h : ready => by simpa only [List.toList_toArray] using modes h.1)

#print axioms audit_buildPort

end SixEdge.Formula
