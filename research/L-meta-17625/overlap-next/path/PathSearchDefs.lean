import Mathlib

/-! Four exceptional gates on the induced path a-b-c-d. Bit i of the value is
the result on the assignment with vertex-variable bits i. A nonempty global
raw set can have an empty four-vertex intersection. Both facts are tracked. -/
namespace PathSearch

structure Wire where
  value : BitVec 16
  raw : BitVec 4
  nz : Bool
  deriving DecidableEq, Repr

abbrev Gate := Bool × Wire

def target : BitVec 16 := 0xF8C8

def single : List Wire := [
  ⟨0,0,true⟩, ⟨0xAAAA,1,true⟩, ⟨0xCCCC,2,true⟩,
  ⟨0xF0F0,4,true⟩, ⟨0xFF00,8,true⟩]

def thin (r : BitVec 4) : Bool := r &&& (r - 1) == 0

def merge (u v : Wire) : Wire := ⟨u.value ||| v.value, u.raw ||| v.raw, u.nz || v.nz⟩

def combine (op : Bool) (u v : Wire) : Wire :=
  if op then merge u v else ⟨u.value &&& v.value, 0, false⟩

def extendOrdinary (initial : List Wire) (g : Gate) : List Wire :=
  if g.1 && g.2.nz then
    initial ++ (initial.map (fun w => merge w g.2)).filter (fun w => thin w.raw)
  else initial

def ports (gates : List Gate) : List Wire :=
  (gates.map Prod.snd ++ gates.foldl extendOrdinary single).eraseDups

def outputs (gates : List Gate) (op : Bool) : List Wire :=
  let ws := ports gates
  (ws.flatMap (fun w => ws.map (combine op w))).eraseDups

def eligible (g : Gate) : Bool :=
  g.1 && g.2.nz && g.2.raw == 0 && (g.2.value &&& ~~~target) == 0

def covered : List Gate → BitVec 16
  | [] => 0
  | g :: gs => (if eligible g then g.2.value else 0) ||| covered gs

def wins (gates : List Gate) : Bool := covered gates == target

/-- Valid sequences read two available ports at each gate. The list is in
topological order. No restriction on repeated reads or dead gates is imposed. -/
inductive Valid : List Gate → Prop
  | nil : Valid []
  | snoc {gs : List Gate} (old : Valid gs) (op : Bool) (u v : Wire)
      (left : u ∈ ports gs) (right : v ∈ ports gs) : Valid (gs ++ [(op,combine op u v)])

theorem covered_bit {gs : List Gate} (i : Nat) :
    (covered gs).getLsbD i = true ↔ ∃ g ∈ gs, eligible g = true ∧ g.2.value.getLsbD i = true := by
  induction gs with
  | nil => simp [covered]
  | cons g gs ih =>
    by_cases ok : eligible g = true
    · simp only [covered,ok,ite_true,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons]
      grind
    · simp [covered,ok,ih]

theorem wins_of_cover {gs : List Gate}
    (agreement : ∀ i < 16, target.getLsbD i = true ↔ ∃ g ∈ gs,
      g.1 = true ∧ g.2.nz = true ∧ g.2.raw = 0 ∧ (g.2.value &&& ~~~target) = 0 ∧
      g.2.value.getLsbD i = true) : wins gs = true := by
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  apply Bool.eq_iff_iff.mpr
  rw [covered_bit,agreement i hi]
  simp [eligible,and_assoc]

end PathSearch
