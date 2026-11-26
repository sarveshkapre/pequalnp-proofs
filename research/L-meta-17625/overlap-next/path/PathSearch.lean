import PathSearchDefs

namespace PathSearch
private def finish (gs : List Gate) : Bool :=
  let z := (ports gs).filter (fun w => w.raw == 0)
  let before := covered gs
  z.any (fun u => z.any (fun v =>
    let g := (true,combine true u v)
    eligible g && ((before ||| g.2.value) == target)))

private def visit : List Bool → List Gate → Bool
  | [], gs => wins gs
  | [op], gs => wins gs || (op && finish gs)
  | op::next::rest, gs => wins gs || (outputs gs op).any (fun w => visit (next::rest) (gs ++ [(op,w)]))

private abbrev exhausted (ops : List Bool) := visit ops [] = false

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

set_option linter.unusedVariables false in
example : target = ((0xAAAA : BitVec 16) &&& 0xCCCC) ||| (0xCCCC &&& 0xF0F0) ||| (0xF0F0 &&& 0xFF00) := by decide

theorem output_mem {gs : List Gate} {u v : Wire} (op : Bool)
    (left : u ∈ ports gs) (right : v ∈ ports gs) : combine op u v ∈ outputs gs op := by
  exact List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨u,left,List.mem_map.mpr ⟨v,right,rfl⟩⟩)

private theorem covered_append (gs hs : List Gate) :
    covered (gs ++ hs) = covered gs ||| covered hs := by
  induction gs with
  | nil => simp [covered]
  | cons g gs ih => simp only [List.cons_append,covered,ih,BitVec.or_assoc]

private theorem terminal_sound {gs : List Gate} (u v : Wire) (op : Bool)
    (left : u ∈ ports gs) (right : v ∈ ports gs) (quiet : wins gs = false)
    (last : (op && finish gs) = false) : wins (gs ++ [(op,combine op u v)]) = false := by
  apply Bool.eq_false_iff.mpr
  intro yes
  change (covered (gs ++ [(op,combine op u v)]) == target) = true at yes
  rw [covered_append] at yes
  let w := combine op u v
  have ok : eligible (op,w) = true := by
    by_contra! no
    change (covered gs ||| covered [(op,w)] == target) = true at yes
    simp [covered,no] at yes
    exact Bool.false_ne_true (quiet.symm.trans (beq_iff_eq.mpr yes))
  have raw := ok
  simp [eligible] at raw
  rcases op with _|_
  · simp [eligible] at ok
  · have zero : u.raw ||| v.raw = 0 := raw.1.2
    have rawU : u.raw = 0 := by bv_decide
    have rawV : v.raw = 0 := by bv_decide
    have inU : u ∈ (ports gs).filter (fun w => w.raw == 0) := List.mem_filter.mpr ⟨left, beq_iff_eq.mpr rawU⟩
    have inV : v ∈ (ports gs).filter (fun w => w.raw == 0) := List.mem_filter.mpr ⟨right, beq_iff_eq.mpr rawV⟩
    have hit : finish gs = true := by
      apply List.any_eq_true.mpr
      refine ⟨u, inU, List.any_eq_true.mpr ⟨v, inV, ?_⟩⟩
      change (eligible (true,w) && ((covered gs ||| w.value) == target)) = true
      rw [ok]
      change (covered gs ||| covered [(true,w)] == target) = true at yes
      simpa [covered,ok] using yes
    simp [hit] at last

private theorem propagate {gs : List Gate} (valid : Valid gs) :
    ∀ rest, exhausted (gs.map Prod.fst ++ rest) → visit rest gs = false := by
  induction valid with
  | nil => intro rest h; simpa using h
  | snoc old op u v left right ih =>
    intro rest bad
    have prior := ih (op::rest) (by simpa [List.map_append,List.append_assoc] using bad)
    cases rest with
    | nil =>
      simp only [visit,Bool.or_eq_false_iff] at prior
      exact terminal_sound u v op left right prior.1 prior.2
    | cons next rest =>
      rw [visit,Bool.or_eq_false_iff] at prior
      exact Bool.eq_false_iff.mpr ((List.any_eq_false.mp prior.2) _ (output_mem op left right))

private theorem counts (ops : List Bool) : ops.count false + ops.count true = ops.length := by
  induction ops with
  | nil => rfl
  | cons b bs ih => cases b <;> simp <;> omega

/- Verification of the six topological orders. -/
private theorem checked0 : exhausted [false,false,true,true] := by decide +kernel
private theorem checked1 : exhausted [false,true,false,true] := by decide +kernel
private theorem checked2 : exhausted [false,true,true,false] := by decide +kernel
private theorem checked3 : exhausted [true,false,false,true] := by decide +kernel
private theorem checked4 : exhausted [true,false,true,false] := by decide +kernel
private theorem checked5 : exhausted [true,true,false,false] := by decide +kernel

private theorem all_orders (ops : List Bool) (a : ops.count false = 2) (o : ops.count true = 2) :
    exhausted ops := by
  have len := counts ops
  obtain ⟨x,y,z,w,rfl⟩ := List.length_eq_four.mp (show ops.length = 4 by omega)
  cases x <;> cases y <;> cases z <;> cases w <;> simp_all
  case false.false.true.true => exact checked0
  case false.true.false.true => exact checked1
  case false.true.true.false => exact checked2
  case true.false.false.true => exact checked3
  case true.false.true.false => exact checked4
  case true.true.false.false => exact checked5

private theorem stop {gs : List Gate} {ops : List Bool} (done : visit ops gs = false) : wins gs = false := by
  cases ops with
  | nil => exact done
  | cons op more =>
    cases more with
    | nil => exact (Bool.or_eq_false_iff.mp done).1
    | cons _ _ => exact (Bool.or_eq_false_iff.mp done).1

/-- No prefix of any valid gate order with at most two ANDs and two ORs
covers all of a-b-c-d through eligible outputs. -/
theorem no_win {gs : List Gate} (valid : Valid gs) (andBudget : (gs.map Prod.fst).count false ≤ 2)
    (orBudget : (gs.map Prod.fst).count true ≤ 2) : wins gs = false := by
  let ops := gs.map Prod.fst
  let rest := List.replicate (2 - ops.count false) false ++ List.replicate (2 - ops.count true) true
  have pass := all_orders (ops ++ rest) (by simp [rest,ops,List.count_replicate]; omega)
    (by simp [rest,ops,List.count_replicate]; omega)
  exact stop (propagate valid rest pass)

#print axioms wins_of_cover
#print axioms no_win
end PathSearch
