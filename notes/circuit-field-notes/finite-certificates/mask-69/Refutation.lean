import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace Mask69

-- Gate elimination adapted from the project's Shannon, Support and Elim proofs
-- at e6bfe1a56efc768d244627b78f175b18de1acd6f (Apache-2.0).
-- A sum represents either a fixed Boolean or an alias for a surviving wire.
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

-- The allowed gates: AND, OR, NOT reading at most two wires.
def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

variable {n : ℕ}

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

-- The support of a gate: the union of the supports of the wires it reads.
def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

lemma mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

lemma mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

-- The supports of all wires, starting from the supports `L` of the wires present.
def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

-- The supports of the input wires: input `i` has support `{i}`.
def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

-- Wire lists `w`, `w'` (for the inputs `x`, `y`) agree on every wire whose support `x` and `y` agree on.
def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

lemma agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

lemma agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

-- A NOT gate reads only its first wire: drop the others.
def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

-- An allowed gate whose NOT gates read at most one wire.
def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

lemma normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate]

lemma wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

-- The status of an old wire: a constant, or the wire `j` of the new circuit.
abbrev Stat := Sum Bool Nat

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

-- What a gate becomes, given the statuses of the wires it reads; `m` is the number of the next new wire. The result is the gate to emit, if any, and the status of the gate's wire.
def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

lemma simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg; subst hg; simp [Ok]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg; subst hg; simp [Ok]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg; subst hg; simp [Ok]
  · simp at hg
  · simp at hg

lemma simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

lemma simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

-- One step of the pass: `acc.1` holds the statuses of the old wires, `acc.2` the new gates.
def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

lemma getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

lemma elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

lemma toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

lemma elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

lemma elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

-- If the status of old wire `k` is a constant and some gate reads wire `k`, one gate is saved.
lemma elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

lemma Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

lemma Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

-- The invariant of the pass, for one input `y` of the new circuit: `w` are the old wires, and every old wire has a valid status whose value on the new wires is the old value.
def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

lemma inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

-- The statuses at the start: the first `n` old wires are the new input wires, and the last input is the constant `b`.
def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => (Sum.inr i.val : Stat)) ++ [(Sum.inl b : Stat)]

lemma inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr i.val : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

lemma ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

-- If no gate reads wire `n`, no other wire has the last input in its support.
lemma supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

lemma inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

lemma inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

-- Gate elimination: fix the last input of `f` to `b`. If `f` depends on that input and the restriction is not constant, a circuit of size `s + 1` for `f` gives one of size `s` for the restriction.
lemma gate_elim (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s + 1 := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Sum.inl false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    have hlen : acc.2.length ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

-- Each bit records a wire value on one of the six promised three-input tests.
abbrev Column := BitVec 6

def rowBit (i : Fin 6) (v : Column) : Bool := v.getLsbD i.val

def tableValue (op : GateOp) (vs : List Column) : Column :=
  match op, vs with
  | .and, [] => 63
  | .and, [a] => a
  | .and, a :: b :: _ => a &&& b
  | .or, [] => 0
  | .or, [a] => a
  | .or, a :: b :: _ => a ||| b
  | .not, [] => 63
  | .not, a :: _ => ~~~a
  | _, _ => 0

lemma tableValue_bit (i : Fin 6) (op : GateOp) (vs : List Column)
    (hop : op = .and ∨ op = .or ∨ op = .not) (hlen : vs.length ≤ 2) :
    rowBit i (tableValue op vs) = op.eval (vs.map (rowBit i)) := by
  have ones : (63 : Column).getLsbD i.val = true :=
    (by decide : ∀ j : Fin 6, (63 : Column).getLsbD j.val = true) i
  rcases hop with rfl | rfl | rfl <;>
    rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
    simp_all [tableValue, GateOp.eval, rowBit, i.isLt]

def addColumn (w : List Column) (g : Gate) : List Column :=
  w ++ [tableValue g.op (g.inputs.map fun i => w.getD i 0)]

lemma mapping_gate (i : Fin 6) (w : List Column) (g : Gate) (hg : Ok g) :
    (addColumn w g).map (rowBit i) =
      w.map (rowBit i) ++ [g.op.eval (g.inputs.map fun j => (w.map (rowBit i)).getD j false)] := by
  simp only [addColumn, List.map_append, List.map_cons, List.map_nil]
  rw [tableValue_bit i _ _ hg.1 (by simpa using hg.2), List.map_map]
  congr 2
  apply congrArg g.op.eval
  apply List.map_congr_left
  intro j _
  have zero_bit : rowBit i 0 = false := by simp [rowBit]
  simpa only [Function.comp_apply, zero_bit] using (List.getD_map (l := w) (d := 0) (n := j) (rowBit i)).symm

lemma mapping_circuit (gs : List Gate) (i : Fin 6) (w : List Column) (ok : ∀ g ∈ gs, Ok g) :
    (gs.foldl addColumn w).map (rowBit i) = wiresFrom gs (w.map (rowBit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (fun a ha => ok a (List.mem_cons_of_mem _ ha)), mapping_gate i w g (ok g List.mem_cons_self)]
    rfl

def rawColumns (pool : List Column) : List Column :=
  ((pool.map (fun a => ~~~a)) ++
    pool.flatMap (fun a => pool.flatMap fun b => [a &&& b, a ||| b]))

def nextColumns (pool : List Column) : List Column := (rawColumns pool).dedup

lemma getD_in_pool (w p : List Column) (hsub : ∀ a ∈ w, a ∈ p) (zero : 0 ∈ p) (j : Nat) :
    w.getD j 0 ∈ p := by
  by_cases hj : j < w.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact hsub _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact zero

lemma gate_in_pool (op : GateOp) (vs p : List Column)
    (hop : op = .and ∨ op = .or ∨ op = .not) (hlen : vs.length ≤ 2)
    (zero : 0 ∈ p) (ones : 63 ∈ p) (inputs : ∀ a ∈ vs, a ∈ p) :
    tableValue op vs ∈ p ∨ tableValue op vs ∈ nextColumns p := by
  have neg (a : Column) (ha : a ∈ p) : ~~~a ∈ nextColumns p := by
    simp only [nextColumns, rawColumns, List.mem_dedup, List.mem_append, List.mem_map]
    exact Or.inl ⟨a, ha, rfl⟩
  have bin (a b v : Column) (ha : a ∈ p) (hb : b ∈ p) (hv : v = a &&& b ∨ v = a ||| b) :
      v ∈ nextColumns p := by
    simp only [nextColumns, rawColumns, List.mem_dedup, List.mem_append, List.mem_flatMap, List.mem_cons,
      List.not_mem_nil, or_false]
    exact Or.inr ⟨a,ha,b,hb,hv⟩
  rcases hop with rfl | rfl | rfl <;>
    rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
    simp_all [tableValue]
  · exact Or.inr (bin a b _ inputs.1 inputs.2 (Or.inl rfl))
  · exact Or.inr (bin a b _ inputs.1 inputs.2 (Or.inr rfl))

-- Both constants are free in this search. A repeated truth table can reuse the earlier wire.
def reaches (target : Column) : Nat → List Column → Bool
  | 0, pool => pool.contains target
  | 1, pool => pool.contains target || (rawColumns pool).contains target
  | k+2, pool => reaches target (k+1) pool ||
      (nextColumns pool).any fun x => !(pool.contains x) && reaches target (k+1) (x :: pool)

lemma reaches_step (target : Column) (k : Nat) (p : List Column) :
    reaches target (k+1) p = (reaches target k p ||
      (nextColumns p).any fun x => !(p.contains x) && reaches target k (x :: p)) := by
  cases k with
  | succ k => rfl
  | zero =>
    apply Bool.eq_iff_iff.mpr
    simp only [reaches, Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true,
      Bool.and_eq_true, Bool.not_eq_true', List.mem_cons, nextColumns, List.mem_dedup]
    by_cases mem : target ∈ p
    · exact ⟨fun _ => Or.inl mem, fun _ => Or.inl mem⟩
    · constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr ⟨target, h, by simpa using mem, Or.inl rfl⟩
      · rintro (h | ⟨x, hx, _, heq | hp⟩)
        · exact Or.inl h
        · exact Or.inr (heq.symm ▸ hx)
        · exact Or.inl hp

lemma search_complete (target : Column) (out : Nat) (k : Nat) :
    ∀ (gs : List Gate) (w p : List Column), gs.length ≤ k → (∀ g ∈ gs, Ok g) →
      (∀ x ∈ w, x ∈ p) → 0 ∈ p → 63 ∈ p →
      (gs.foldl addColumn w).getD out 0 = target → reaches target k p = true := by
  induction k with
  | zero =>
    intro gs w p size ok sub zero ones result
    have e : gs = [] := List.length_eq_zero_iff.mp (by omega)
    subst gs
    simp only [List.foldl_nil] at result
    simpa [reaches, ← result] using getD_in_pool w p sub zero out
  | succ k ih =>
    intro gs w p size ok sub zero ones result
    rw [reaches_step, Bool.or_eq_true]
    cases gs with
    | nil => exact Or.inl (ih [] w p (by simp) ok sub zero ones result)
    | cons g gs =>
      have sz : gs.length ≤ k := by simpa using size
      have tailOk : ∀ a ∈ gs, Ok a := fun a ha => ok a (List.mem_cons_of_mem _ ha)
      have hg := ok g List.mem_cons_self
      let vs := g.inputs.map fun j => w.getD j 0
      let x := tableValue g.op vs
      have inputs : ∀ a ∈ vs, a ∈ p := by
        intro a ha
        obtain ⟨j,_,rfl⟩ := List.mem_map.mp ha
        exact getD_in_pool w p sub zero j
      have next : x ∈ p ∨ x ∈ nextColumns p :=
        gate_in_pool g.op vs p hg.1 (by simpa [vs] using hg.2) zero ones inputs
      change (gs.foldl addColumn (w ++ [x])).getD out 0 = target at result
      by_cases old : x ∈ p
      · apply Or.inl (ih gs (w ++ [x]) p sz tailOk _ zero ones result)
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact sub a ha
        · simpa only [List.mem_singleton.mp ha] using old
      · right
        apply List.any_eq_true.mpr
        refine ⟨x, next.resolve_left old, ?_⟩
        simp only [Bool.and_eq_true, Bool.not_eq_true']
        refine ⟨by simpa using old, ih gs (w ++ [x]) (x :: p) sz tailOk ?_ (List.mem_cons_of_mem _ zero) (List.mem_cons_of_mem _ ones) result⟩
        intro a ha
        rcases List.mem_append.mp ha with h | h
        · exact List.mem_cons_of_mem _ (sub a h)
        · exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp h))

-- Row masks 1 through 6 encode the three singletons and three unordered pairs.
-- The three initial columns are the three input wires; bit i is the answer on row i+1.
def initial : List Column := [21, 38, 56]
def startPool : List Column := [0, 63, 21, 38, 56]
def wanted : Column := 19

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma four_gates_fail : reaches wanted 4 startPool = false := by decide +kernel

def pos (r : Nat) : Bool := r == 1 || r == 2 || r == 5
def rows : List Nat := [1, 2, 3, 4, 5, 6]

-- A restriction fixes the last input to false.
def sample (n r : Nat) (i : Fin n) : Bool := r.testBit i.val

def restrict {n : Nat} (f : (Fin (n+1) → Bool) → Bool) (y : Fin n → Bool) : Bool :=
  f (Fin.snoc y false)

-- The witnesses below only use singletons and pairs covered by the original statement.
def needed : List Nat := [1, 2, 3, 4, 5, 6, 9, 17]

lemma fromDesk (C : Circuit) (heval : ∀ i j : Fin 5,
    C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) =
      (69 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) :
    ∀ r ∈ needed, C.eval (List.ofFn (sample 5 r)) = pos r := by
  have covers : ∀ r ∈ needed, ∃ i j : Fin 5,
      List.ofFn (sample 5 r) = (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) ∧
      (69 : Nat).testBit (5 * min i.val j.val + max i.val j.val) = pos r := by
    intro r hr
    simp only [needed, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h|h|h|h|h|h|h|h <;> subst r <;> decide
  intro r hr
  obtain ⟨i,j,hin,hout⟩ := covers r hr
  rw [hin, heval, hout]

lemma reducedImpossible (h : (Fin 3 → Bool) → Bool)
    (values : ∀ r ∈ rows, h (sample 3 r) = pos r) : ¬ HasCircuitSize 3 h 4 := by
  rintro ⟨C, fan, size, eval⟩
  have inputsAgree (i : Fin 6) : initial.map (rowBit i) = List.ofFn (sample 3 (i.val + 1)) :=
    (by decide : ∀ j : Fin 6, initial.map (rowBit j) = List.ofFn (sample 3 (j.val + 1))) i
  have answers (i : Fin 6) : pos (i.val + 1) = rowBit i wanted :=
    (by decide : ∀ j : Fin 6, pos (j.val + 1) = rowBit j wanted) i
  let ws := C.gates.foldl addColumn initial
  have out : ws.getD C.output 0 = wanted := by
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro j hj
    let i : Fin 6 := ⟨j,hj⟩
    change rowBit i (ws.getD C.output 0) = rowBit i wanted
    have bits : ws.map (rowBit i) = C.wires (List.ofFn (sample 3 (i.val+1))) := by
      rw [show ws.map (rowBit i) = wiresFrom C.gates (initial.map (rowBit i)) from
        mapping_circuit C.gates i initial fan, inputsAgree]
      rfl
    have present : i.val + 1 ∈ rows := (by decide : ∀ j : Fin 6, j.val+1 ∈ rows) i
    calc
      rowBit i (ws.getD C.output 0) = (ws.map (rowBit i)).getD C.output (rowBit i 0) :=
        (List.getD_map _ _ _).symm
      _ = C.eval (List.ofFn (sample 3 (i.val+1))) := by rw [bits, show rowBit i 0 = false by simp [rowBit]]; rfl
      _ = h (sample 3 (i.val+1)) := eval _
      _ = rowBit i wanted := (values _ present).trans (answers i)
  have yes := search_complete wanted C.output 4 C.gates initial startPool size fan
    (by decide) (by decide) (by decide) out
  exact Bool.false_ne_true (four_gates_fail.symm.trans yes)

lemma eliminateLastTwo (f : (Fin 5 → Bool) → Bool)
    (obs : ∀ r ∈ needed, f (sample 5 r) = pos r) : ¬ HasCircuitSize 5 f 6 := by
  intro circuit
  let g := restrict (n := 4) f
  let h := restrict (n := 3) g
  have gval (r : Nat) (hr : r < 16) : g (sample 4 r) = f (sample 5 r) := by
    exact congrArg f ((by decide : ∀ i : Fin 16, Fin.snoc (sample 4 i.val) false = sample 5 i.val) ⟨r,hr⟩)
  have hval (r : Nat) (hr : r < 8) : h (sample 3 r) = g (sample 4 r) := by
    exact congrArg g ((by decide : ∀ i : Fin 8, Fin.snoc (sample 3 i.val) false = sample 4 i.val) ⟨r,hr⟩)
  have high : Function.update (sample 5 1) (Fin.last 4) (!(sample 5 1 (Fin.last 4))) = sample 5 17 := by decide
  have next : Function.update (sample 4 1) (Fin.last 3) (!(sample 4 1 (Fin.last 3))) = sample 4 9 := by decide
  have gsz : HasCircuitSize 4 g 5 := by
    apply gate_elim 4 f false 5 _ _ circuit
    · refine ⟨sample 5 1, ?_⟩
      rw [high, obs 17 (by decide), obs 1 (by decide)]
      decide
    · refine ⟨sample 4 1, sample 4 4, ?_⟩
      change g (sample 4 1) ≠ g (sample 4 4)
      rw [gval 1 (by decide), gval 4 (by decide), obs 1 (by decide), obs 4 (by decide)]
      decide
  have hsz : HasCircuitSize 3 h 4 := by
    apply gate_elim 3 g false 4 _ _ gsz
    · refine ⟨sample 4 1, ?_⟩
      rw [next, gval 9 (by decide), gval 1 (by decide), obs 9 (by decide), obs 1 (by decide)]
      decide
    · refine ⟨sample 3 1, sample 3 4, ?_⟩
      change h (sample 3 1) ≠ h (sample 3 4)
      rw [hval 1 (by decide), hval 4 (by decide), gval 1 (by decide), gval 4 (by decide), obs 1 (by decide), obs 4 (by decide)]
      decide
  apply reducedImpossible h _ hsz
  intro r hr
  have hr8 : r < 8 := (by decide : ∀ t ∈ rows, t < 8) r hr
  have hn : r ∈ needed := (by decide : ∀ t ∈ rows, t ∈ needed) r hr
  exact (hval r hr8).trans ((gval r (by omega)).trans (obs r hn))

end Mask69

theorem Mask69.no_six :
    ¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 6 ∧
      ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) =
        (69 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  rintro ⟨C, fan, size, heval⟩
  let f := fun x : Fin 5 → Bool => C.eval (List.ofFn x)
  exact Mask69.eliminateLastTwo f (Mask69.fromDesk C heval) ⟨C, fan, size, fun _ => rfl⟩
