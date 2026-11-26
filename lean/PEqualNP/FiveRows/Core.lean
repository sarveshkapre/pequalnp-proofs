import PEqualNP.Atlas56.FullClassification

/-! Exhaust the four formula shapes on the 5 by 7 zero matrix.
A bit in a column domain is a six-bit rectangle-side assignment still
consistent with the rows already read. All finite checks use the kernel. -/
namespace FiveSevenCheck
inductive Shape where | four | threeTwo | cube | outside deriving DecidableEq
abbrev Code := BitVec 6
abbrev Domain := BitVec 64

def value (s : Shape) (v : Code) : Bool :=
  let a := v.getLsbD 0
  let b := v.getLsbD 1
  let c := v.getLsbD 2
  let d := v.getLsbD 3
  let e := v.getLsbD 4
  let f := v.getLsbD 5
  match s with
  | .four => (a || b) || (c || d)
  | .threeTwo => ((a || b) || c) && (d || e)
  | .cube => ((a || b) && (c || d)) && (e || f)
  | .outside => a || ((b || c) && (d || e))

def profiles : Shape → List Domain
  | .four => [
    0x0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee,
    0xf0f0f0f0f0f0f0f0, 0xfafafafafafafafa, 0xfcfcfcfcfcfcfcfc, 0xfefefefefefefefe,
    0xff00ff00ff00ff00, 0xffaaffaaffaaffaa, 0xffccffccffccffcc, 0xffeeffeeffeeffee,
    0xfff0fff0fff0fff0, 0xfffafffafffafffa, 0xfffcfffcfffcfffc, 0xfffefffefffefffe]
  | .threeTwo => [
    0x0, 0xaa00aa00aa00aa00, 0xaaaa0000aaaa0000, 0xaaaaaa00aaaaaa00,
    0xcc00cc00cc00cc00, 0xcccc0000cccc0000, 0xcccccc00cccccc00, 0xee00ee00ee00ee00,
    0xeeee0000eeee0000, 0xeeeeee00eeeeee00, 0xf000f000f000f000, 0xf0f00000f0f00000,
    0xf0f0f000f0f0f000, 0xfa00fa00fa00fa00, 0xfafa0000fafa0000, 0xfafafa00fafafa00,
    0xfc00fc00fc00fc00, 0xfcfc0000fcfc0000, 0xfcfcfc00fcfcfc00, 0xfe00fe00fe00fe00,
    0xfefe0000fefe0000, 0xfefefe00fefefe00]
  | .cube => [
    0x0, 0xa0a00000a0a00000, 0xa0a0a0a000000000, 0xa0a0a0a0a0a00000,
    0xaa000000aa000000, 0xaa00aa0000000000, 0xaa00aa00aa000000, 0xaaa00000aaa00000,
    0xaaa0aaa000000000, 0xaaa0aaa0aaa00000, 0xc0c00000c0c00000, 0xc0c0c0c000000000,
    0xc0c0c0c0c0c00000, 0xcc000000cc000000, 0xcc00cc0000000000, 0xcc00cc00cc000000,
    0xccc00000ccc00000, 0xccc0ccc000000000, 0xccc0ccc0ccc00000, 0xe0e00000e0e00000,
    0xe0e0e0e000000000, 0xe0e0e0e0e0e00000, 0xee000000ee000000, 0xee00ee0000000000,
    0xee00ee00ee000000, 0xeee00000eee00000, 0xeee0eee000000000, 0xeee0eee0eee00000]
  | .outside => [
    0x0, 0xaaaaaaaaaaaaaaaa, 0xcc00cc00cc00cc00, 0xcccc0000cccc0000,
    0xcccccc00cccccc00, 0xeeaaeeaaeeaaeeaa, 0xeeeeaaaaeeeeaaaa, 0xeeeeeeaaeeeeeeaa,
    0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f000f0f0f000, 0xfaaafaaafaaafaaa,
    0xfafaaaaafafaaaaa, 0xfafafaaafafafaaa, 0xfc00fc00fc00fc00, 0xfcfc0000fcfc0000,
    0xfcfcfc00fcfcfc00, 0xfeaafeaafeaafeaa, 0xfefeaaaafefeaaaa, 0xfefefeaafefefeaa]

set_option maxRecDepth 200000
set_option maxHeartbeats 0

private def columnMasks : Fin 6 → Domain :=
  ![0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,
    0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]

private theorem column_bit : ∀ (j : Fin 6) (c : Code),
    (columnMasks j).getLsbD c.toNat = c.getLsbD j.val := by decide +kernel

private def term (r : Code) (j : Fin 6) : Domain :=
  if r.getLsbD j.val then columnMasks j else 0

private theorem term_bit (r c : Code) (j : Fin 6) :
    (term r j).getLsbD c.toNat = (r.getLsbD j.val && c.getLsbD j.val) := by
  unfold term
  cases h : r.getLsbD j.val
  · simp only [Bool.false_eq_true,ite_false,Bool.false_and]
    simp
  · exact column_bit j c

private def truth (s : Shape) (r : Code) : Domain :=
  let a := term r 0
  let b := term r 1
  let c := term r 2
  let d := term r 3
  let e := term r 4
  let f := term r 5
  match s with
  | .four => (a ||| b) ||| (c ||| d)
  | .threeTwo => ((a ||| b) ||| c) &&& (d ||| e)
  | .cube => ((a ||| b) &&& (c ||| d)) &&& (e ||| f)
  | .outside => a ||| ((b ||| c) &&& (d ||| e))

private theorem listed (s : Shape) : ∀ r : Code, truth s r ∈ profiles s := by
  cases s <;> decide +kernel

/-- Every arbitrary row assignment has one of the listed truth tables on
all 64 column assignments. The table generator is outside the trusted proof. -/
theorem complete_profiles (s : Shape) (r : Code) : ∃ h ∈ profiles s,
    ∀ c : Code, h.getLsbD c.toNat = value s (r &&& c) := by
  refine ⟨truth s r,listed s r,?_⟩
  intro c
  cases s <;> simp [truth,value,term_bit]

structure Domains where
  a : Domain
  b : Domain
  c : Domain
  d : Domain
  e : Domain
  f : Domain
  g : Domain

def Domains.get (s : Domains) : Fin 7 → Domain := ![s.a,s.b,s.c,s.d,s.e,s.f,s.g]
def full : Domains := ⟨-1,-1,-1,-1,-1,-1,-1⟩

def restrictTo (old h : Domain) (pos : Bool) : Domain :=
  old &&& (if pos then h else ~~~h)

def advance (d : Domains) (p : BitVec 7) (h : Domain) : Domains :=
  ⟨restrictTo d.a h (p.getLsbD 0), restrictTo d.b h (p.getLsbD 1),
   restrictTo d.c h (p.getLsbD 2), restrictTo d.d h (p.getLsbD 3),
   restrictTo d.e h (p.getLsbD 4), restrictTo d.f h (p.getLsbD 5),
   restrictTo d.g h (p.getLsbD 6)⟩

def viable (d : Domains) : Bool :=
  d.a != 0 && d.b != 0 && d.c != 0 && d.d != 0 && d.e != 0 && d.f != 0 && d.g != 0

def search (hs : List Domain) : List (BitVec 7) → Domains → Bool
  | [], _ => true
  | p :: ps, d => hs.any fun h =>
      let next := advance d p h
      viable next && search hs ps next

def Keeps (d : Domains) (cols : Fin 7 → Code) : Prop :=
  ∀ j, (d.get j).getLsbD (cols j).toNat = true

theorem full_keeps (cols : Fin 7 → Code) : Keeps full cols := by
  have ones : ∀ c : Code, (-1 : Domain).getLsbD c.toNat = true := by decide +kernel
  intro j
  fin_cases j <;> exact ones _

private theorem kept_viable {d : Domains} {cols : Fin 7 → Code} (hd : Keeps d cols) :
    viable d = true := by
  have nonzero (i : Fin 7) : d.get i ≠ 0 := by
    intro hi
    have h := hd i
    simp [hi] at h
  have ha := nonzero 0
  have hb := nonzero 1
  have hc := nonzero 2
  have hh := nonzero 3
  have he := nonzero 4
  have hf := nonzero 5
  have hg := nonzero 6
  simpa [viable,Domains.get] using And.intro (And.intro (And.intro (And.intro
    (And.intro (And.intro ha hb) hc) hh) he) hf) hg

private theorem advance_keeps {d : Domains} {cols : Fin 7 → Code} (hd : Keeps d cols)
    (p : BitVec 7) (h : Domain) (hh : ∀ j : Fin 7, h.getLsbD (cols j).toNat = p.getLsbD j.val) :
    Keeps (advance d p h) cols := by
  intro j
  have eqn : (advance d p h).get j = restrictTo (d.get j) h (p.getLsbD j.val) := by
    fin_cases j <;> rfl
  have within : (cols j).toNat < 64 := (cols j).isLt
  rw [eqn]
  cases hb : p.getLsbD j.val <;>
    simp only [restrictTo, Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,
      BitVec.getLsbD_not,hd j,hh j,hb,within,Bool.true_and] <;> rfl

theorem search_complete (hs : List Domain) (cols : Fin 7 → Code) (ps : List (BitVec 7))
    (matchRows : ∀ p ∈ ps, ∃ h ∈ hs, ∀ j : Fin 7, h.getLsbD (cols j).toNat = p.getLsbD j.val)
    (d : Domains) (hd : Keeps d cols) : search hs ps d = true := by
  induction ps generalizing d with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨h,hm,hh⟩ := matchRows p (by simp)
    have hk := advance_keeps hd p h hh
    apply List.any_eq_true.mpr
    exact ⟨h,hm,Bool.and_eq_true_iff.mpr ⟨kept_viable hk,
      ih (fun p hp => matchRows p (by simp [hp])) _ hk⟩⟩

def masks : Fin 5 → BitVec 7 := ![42,25,82,99,124]
def order : List (Fin 5) := [0,1,2,3,4]
def inputs : List (BitVec 7) := order.map masks

end FiveSevenCheck

namespace FiveSevenCheck
set_option maxHeartbeats 0
set_option maxRecDepth 200000

/-- Split on the profile of row 0. Splitting the computation into lemmas
keeps the memory needed for one kernel reduction bounded. -/
private def branch (s : Shape) (h : Domain) : Bool :=
  let next := advance full 42 h
  viable next && search (profiles s) [25, 82, 99, 124] next

private theorem reject_four_0 : branch .four 0x0 = false := by decide +kernel
private theorem reject_four_1 : branch .four 0xaaaaaaaaaaaaaaaa = false := by decide +kernel
private theorem reject_four_2 : branch .four 0xcccccccccccccccc = false := by decide +kernel
private theorem reject_four_3 : branch .four 0xeeeeeeeeeeeeeeee = false := by decide +kernel
private theorem reject_four_4 : branch .four 0xf0f0f0f0f0f0f0f0 = false := by decide +kernel
private theorem reject_four_5 : branch .four 0xfafafafafafafafa = false := by decide +kernel
private theorem reject_four_6 : branch .four 0xfcfcfcfcfcfcfcfc = false := by decide +kernel
private theorem reject_four_7 : branch .four 0xfefefefefefefefe = false := by decide +kernel
private theorem reject_four_8 : branch .four 0xff00ff00ff00ff00 = false := by decide +kernel
private theorem reject_four_9 : branch .four 0xffaaffaaffaaffaa = false := by decide +kernel
private theorem reject_four_10 : branch .four 0xffccffccffccffcc = false := by decide +kernel
private theorem reject_four_11 : branch .four 0xffeeffeeffeeffee = false := by decide +kernel
private theorem reject_four_12 : branch .four 0xfff0fff0fff0fff0 = false := by decide +kernel
private theorem reject_four_13 : branch .four 0xfffafffafffafffa = false := by decide +kernel
private theorem reject_four_14 : branch .four 0xfffcfffcfffcfffc = false := by decide +kernel
private theorem reject_four_15 : branch .four 0xfffefffefffefffe = false := by decide +kernel

theorem fails_four : search (profiles .four) inputs full = false := by
  change (profiles .four).any (branch .four) = false
  simp only [profiles,List.any_cons,List.any_nil,Bool.false_or,
    reject_four_0,reject_four_1,reject_four_2,reject_four_3,reject_four_4,
    reject_four_5,reject_four_6,reject_four_7,reject_four_8,reject_four_9,
    reject_four_10,reject_four_11,reject_four_12,reject_four_13,reject_four_14,
    reject_four_15]

private theorem reject_threeTwo_0 : branch .threeTwo 0x0 = false := by decide +kernel
private theorem reject_threeTwo_1 : branch .threeTwo 0xaa00aa00aa00aa00 = false := by decide +kernel
private theorem reject_threeTwo_2 : branch .threeTwo 0xaaaa0000aaaa0000 = false := by decide +kernel
private theorem reject_threeTwo_3 : branch .threeTwo 0xaaaaaa00aaaaaa00 = false := by decide +kernel
private theorem reject_threeTwo_4 : branch .threeTwo 0xcc00cc00cc00cc00 = false := by decide +kernel
private theorem reject_threeTwo_5 : branch .threeTwo 0xcccc0000cccc0000 = false := by decide +kernel
private theorem reject_threeTwo_6 : branch .threeTwo 0xcccccc00cccccc00 = false := by decide +kernel
private theorem reject_threeTwo_7 : branch .threeTwo 0xee00ee00ee00ee00 = false := by decide +kernel
private theorem reject_threeTwo_8 : branch .threeTwo 0xeeee0000eeee0000 = false := by decide +kernel
private theorem reject_threeTwo_9 : branch .threeTwo 0xeeeeee00eeeeee00 = false := by decide +kernel
private theorem reject_threeTwo_10 : branch .threeTwo 0xf000f000f000f000 = false := by decide +kernel
private theorem reject_threeTwo_11 : branch .threeTwo 0xf0f00000f0f00000 = false := by decide +kernel
private theorem reject_threeTwo_12 : branch .threeTwo 0xf0f0f000f0f0f000 = false := by decide +kernel
private theorem reject_threeTwo_13 : branch .threeTwo 0xfa00fa00fa00fa00 = false := by decide +kernel
private theorem reject_threeTwo_14 : branch .threeTwo 0xfafa0000fafa0000 = false := by decide +kernel
private theorem reject_threeTwo_15 : branch .threeTwo 0xfafafa00fafafa00 = false := by decide +kernel
private theorem reject_threeTwo_16 : branch .threeTwo 0xfc00fc00fc00fc00 = false := by decide +kernel
private theorem reject_threeTwo_17 : branch .threeTwo 0xfcfc0000fcfc0000 = false := by decide +kernel
private theorem reject_threeTwo_18 : branch .threeTwo 0xfcfcfc00fcfcfc00 = false := by decide +kernel
private theorem reject_threeTwo_19 : branch .threeTwo 0xfe00fe00fe00fe00 = false := by decide +kernel
private theorem reject_threeTwo_20 : branch .threeTwo 0xfefe0000fefe0000 = false := by decide +kernel
private theorem reject_threeTwo_21 : branch .threeTwo 0xfefefe00fefefe00 = false := by decide +kernel

theorem fails_threeTwo : search (profiles .threeTwo) inputs full = false := by
  change (profiles .threeTwo).any (branch .threeTwo) = false
  simp only [profiles,List.any_cons,List.any_nil,Bool.false_or,
    reject_threeTwo_0,reject_threeTwo_1,reject_threeTwo_2,reject_threeTwo_3,reject_threeTwo_4,
    reject_threeTwo_5,reject_threeTwo_6,reject_threeTwo_7,reject_threeTwo_8,reject_threeTwo_9,
    reject_threeTwo_10,reject_threeTwo_11,reject_threeTwo_12,reject_threeTwo_13,reject_threeTwo_14,
    reject_threeTwo_15,reject_threeTwo_16,reject_threeTwo_17,reject_threeTwo_18,reject_threeTwo_19,
    reject_threeTwo_20,reject_threeTwo_21]

private theorem reject_cube_0 : branch .cube 0x0 = false := by decide +kernel
private theorem reject_cube_1 : branch .cube 0xa0a00000a0a00000 = false := by decide +kernel
private theorem reject_cube_2 : branch .cube 0xa0a0a0a000000000 = false := by decide +kernel
private theorem reject_cube_3 : branch .cube 0xa0a0a0a0a0a00000 = false := by decide +kernel
private theorem reject_cube_4 : branch .cube 0xaa000000aa000000 = false := by decide +kernel
private theorem reject_cube_5 : branch .cube 0xaa00aa0000000000 = false := by decide +kernel
private theorem reject_cube_6 : branch .cube 0xaa00aa00aa000000 = false := by decide +kernel
private theorem reject_cube_7 : branch .cube 0xaaa00000aaa00000 = false := by decide +kernel
private theorem reject_cube_8 : branch .cube 0xaaa0aaa000000000 = false := by decide +kernel
private theorem reject_cube_9 : branch .cube 0xaaa0aaa0aaa00000 = false := by decide +kernel
private theorem reject_cube_10 : branch .cube 0xc0c00000c0c00000 = false := by decide +kernel
private theorem reject_cube_11 : branch .cube 0xc0c0c0c000000000 = false := by decide +kernel
private theorem reject_cube_12 : branch .cube 0xc0c0c0c0c0c00000 = false := by decide +kernel
private theorem reject_cube_13 : branch .cube 0xcc000000cc000000 = false := by decide +kernel
private theorem reject_cube_14 : branch .cube 0xcc00cc0000000000 = false := by decide +kernel
private theorem reject_cube_15 : branch .cube 0xcc00cc00cc000000 = false := by decide +kernel
private theorem reject_cube_16 : branch .cube 0xccc00000ccc00000 = false := by decide +kernel
private theorem reject_cube_17 : branch .cube 0xccc0ccc000000000 = false := by decide +kernel
private theorem reject_cube_18 : branch .cube 0xccc0ccc0ccc00000 = false := by decide +kernel
private theorem reject_cube_19 : branch .cube 0xe0e00000e0e00000 = false := by decide +kernel
private theorem reject_cube_20 : branch .cube 0xe0e0e0e000000000 = false := by decide +kernel
private theorem reject_cube_21 : branch .cube 0xe0e0e0e0e0e00000 = false := by decide +kernel
private theorem reject_cube_22 : branch .cube 0xee000000ee000000 = false := by decide +kernel
private theorem reject_cube_23 : branch .cube 0xee00ee0000000000 = false := by decide +kernel
private theorem reject_cube_24 : branch .cube 0xee00ee00ee000000 = false := by decide +kernel
private theorem reject_cube_25 : branch .cube 0xeee00000eee00000 = false := by decide +kernel
private theorem reject_cube_26 : branch .cube 0xeee0eee000000000 = false := by decide +kernel
private theorem reject_cube_27 : branch .cube 0xeee0eee0eee00000 = false := by decide +kernel

theorem fails_cube : search (profiles .cube) inputs full = false := by
  change (profiles .cube).any (branch .cube) = false
  simp only [profiles,List.any_cons,List.any_nil,Bool.false_or,
    reject_cube_0,reject_cube_1,reject_cube_2,reject_cube_3,reject_cube_4,
    reject_cube_5,reject_cube_6,reject_cube_7,reject_cube_8,reject_cube_9,
    reject_cube_10,reject_cube_11,reject_cube_12,reject_cube_13,reject_cube_14,
    reject_cube_15,reject_cube_16,reject_cube_17,reject_cube_18,reject_cube_19,
    reject_cube_20,reject_cube_21,reject_cube_22,reject_cube_23,reject_cube_24,
    reject_cube_25,reject_cube_26,reject_cube_27]

private theorem reject_outside_0 : branch .outside 0x0 = false := by decide +kernel
private theorem reject_outside_1 : branch .outside 0xaaaaaaaaaaaaaaaa = false := by decide +kernel
private theorem reject_outside_2 : branch .outside 0xcc00cc00cc00cc00 = false := by decide +kernel
private theorem reject_outside_3 : branch .outside 0xcccc0000cccc0000 = false := by decide +kernel
private theorem reject_outside_4 : branch .outside 0xcccccc00cccccc00 = false := by decide +kernel
private theorem reject_outside_5 : branch .outside 0xeeaaeeaaeeaaeeaa = false := by decide +kernel
private theorem reject_outside_6 : branch .outside 0xeeeeaaaaeeeeaaaa = false := by decide +kernel
private theorem reject_outside_7 : branch .outside 0xeeeeeeaaeeeeeeaa = false := by decide +kernel
private theorem reject_outside_8 : branch .outside 0xf000f000f000f000 = false := by decide +kernel
private theorem reject_outside_9 : branch .outside 0xf0f00000f0f00000 = false := by decide +kernel
private theorem reject_outside_10 : branch .outside 0xf0f0f000f0f0f000 = false := by decide +kernel
private theorem reject_outside_11 : branch .outside 0xfaaafaaafaaafaaa = false := by decide +kernel
private theorem reject_outside_12 : branch .outside 0xfafaaaaafafaaaaa = false := by decide +kernel
private theorem reject_outside_13 : branch .outside 0xfafafaaafafafaaa = false := by decide +kernel
private theorem reject_outside_14 : branch .outside 0xfc00fc00fc00fc00 = false := by decide +kernel
private theorem reject_outside_15 : branch .outside 0xfcfc0000fcfc0000 = false := by decide +kernel
private theorem reject_outside_16 : branch .outside 0xfcfcfc00fcfcfc00 = false := by decide +kernel
private theorem reject_outside_17 : branch .outside 0xfeaafeaafeaafeaa = false := by decide +kernel
private theorem reject_outside_18 : branch .outside 0xfefeaaaafefeaaaa = false := by decide +kernel
private theorem reject_outside_19 : branch .outside 0xfefefeaafefefeaa = false := by decide +kernel

theorem fails_outside : search (profiles .outside) inputs full = false := by
  change (profiles .outside).any (branch .outside) = false
  simp only [profiles,List.any_cons,List.any_nil,Bool.false_or,
    reject_outside_0,reject_outside_1,reject_outside_2,reject_outside_3,reject_outside_4,
    reject_outside_5,reject_outside_6,reject_outside_7,reject_outside_8,reject_outside_9,
    reject_outside_10,reject_outside_11,reject_outside_12,reject_outside_13,reject_outside_14,
    reject_outside_15,reject_outside_16,reject_outside_17,reject_outside_18,reject_outside_19]

theorem no_representation (s : Shape) (rows : Fin 5 → Code) (cols : Fin 7 → Code)
    (hm : ∀ i j, value s (rows i &&& cols j) = (masks i).getLsbD j.val) : False := by
  have allRows : ∀ p ∈ inputs, ∃ h ∈ profiles s,
      ∀ j : Fin 7, h.getLsbD (cols j).toNat = p.getLsbD j.val := by
    intro p hp
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
    obtain ⟨h,hh,hv⟩ := complete_profiles s (rows i)
    exact ⟨h,hh,fun j => (hv (cols j)).trans (hm i j)⟩
  have accepted := search_complete (profiles s) cols inputs allRows full (full_keeps cols)
  cases s <;> simp_all only [fails_four,fails_threeTwo,fails_cube,fails_outside,Bool.false_eq_true]

#print axioms no_representation
end FiveSevenCheck


/-! Exact 3 versus 4 on a 5 by 7 graph in the free-union star model.
We work with zero sets, using pjscruggs's two-gate classification and
the three-gate classification and formula definitions of the 8 by 8 hand-back. -/
namespace FiveRowSharing
open Set TwoIntersections ThreeIntersectionsFormula ThreeIntersectionsSharingGap
open FiveSevenCheck (Shape Code value masks no_representation)
abbrev Cell := Fin 5 × Fin 7

def zero : Set Cell := {p | (masks p.1).getLsbD p.2.val = true}

def rowSides : Fin 6 → BitVec 5 := ![27,28,15,23,25,30]
def colSides : Fin 6 → BitVec 7 := ![57,86,99,124,46,91]
def rect (i : Fin 6) : Set Cell :=
  {r : Fin 5 | (rowSides i).getLsbD r.val = true} ×ˢ
  {c : Fin 7 | (colSides i).getLsbD c.val = true}

theorem rect_ok (i : Fin 6) : Rectangle (rect i) := ⟨_,_,rfl⟩

theorem construction : zero = (rect 2 ∪ (rect 3 ∩ (rect 0 ∪ rect 1))) ∩
    (rect 4 ∪ (rect 5 ∩ (rect 0 ∪ rect 1))) := by
  ext p
  revert p
  unfold zero masks rect rowSides colSides
  decide +kernel

theorem circuit_three : ThreeIntersections.Three Rectangle zero := by
  apply (ThreeIntersections.rectangle_normal_iff zero).mpr
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_,_,_,_,_,_, rect_ok 0, rect_ok 1,
    rect_ok 2, rect_ok 3, rect_ok 4, rect_ok 5, construction⟩)))

theorem formula_four : Formula Rectangle 4 zero := by
  rw [construction]
  exact diamond_four_formula (rect_ok 0) (rect_ok 1) (rect_ok 2) (rect_ok 3) (rect_ok 4) (rect_ok 5)

private def form (s : Shape) (t : Fin 6 → Set Cell) : Set Cell :=
  match s with
  | .four => (t 0 ∪ t 1) ∪ (t 2 ∪ t 3)
  | .threeTwo => ((t 0 ∪ t 1) ∪ t 2) ∩ (t 3 ∪ t 4)
  | .cube => ((t 0 ∪ t 1) ∩ (t 2 ∪ t 3)) ∩ (t 4 ∪ t 5)
  | .outside => t 0 ∪ ((t 1 ∪ t 2) ∩ (t 3 ∪ t 4))

private noncomputable def pack {ι : Type} (side : Fin 6 → Set ι) (i : ι) : Code := by
  classical
  exact BitVec.ofBoolListLE [decide (i ∈ side 0), decide (i ∈ side 1), decide (i ∈ side 2),
    decide (i ∈ side 3), decide (i ∈ side 4), decide (i ∈ side 5)]

private theorem no_form (s : Shape) (t : Fin 6 → Set Cell) (hr : ∀ i, Rectangle (t i))
    (hz : zero = form s t) : False := by
  classical
  choose R C hRC using hr
  apply no_representation s (pack R) (pack C)
  intro i j
  have hmem : (masks i).getLsbD j.val = true ↔ (i,j) ∈ form s t := by
    change (i,j) ∈ zero ↔ _
    rw [hz]
  have hv : value s (pack R i &&& pack C j) = true ↔ (i,j) ∈ form s t := by
    cases s <;> simp only [value,pack,BitVec.getLsbD_and,BitVec.getLsbD_ofBoolListLE] <;>
      simp [form,hRC,List.getD]
  exact Bool.eq_iff_iff.mpr (hv.trans hmem.symm)

theorem no_first_four : ¬ FirstFour Rectangle zero := by
  rintro (⟨a,b,c,d,ha,hb,hc,hd,hz⟩ | ⟨a,b,c,d,e,ha,hb,hc,hd,he,hz⟩ |
    ⟨a,b,c,d,e,f,ha,hb,hc,hd,he,hf,hz⟩ | ⟨a,b,c,d,e,ha,hb,hc,hd,he,hz⟩)
  · apply no_form .four ![a,b,c,d,a,b] _ hz
    intro i
    fin_cases i <;> assumption
  · apply no_form .threeTwo ![a,b,c,d,e,a] _ hz
    intro i
    fin_cases i <;> assumption
  · apply no_form .cube ![a,b,c,d,e,f] _ hz
    intro i
    fin_cases i <;> assumption
  · apply no_form .outside ![a,b,c,d,e,a] _ hz
    intro i
    fin_cases i <;> assumption

private theorem rect_closed : Closed (@Rectangle (Fin 5) (Fin 7)) := by
  rintro _ _ ⟨a,b,rfl⟩ ⟨c,d,rfl⟩
  exact ⟨a ∩ c,b ∩ d,by ext p; simp; tauto⟩

theorem formula_lower {n : Nat} (hn : n < 4) : ¬ Formula Rectangle n zero :=
  fun h => no_first_four (formula_first_four rect_closed h (by omega))

theorem circuit_lower : ¬ Two Rectangle zero := by
  intro h
  rcases (TwoIntersections.rectangle_normal_iff zero).mp h with
      ⟨a,b,c,ha,hb,hc,hz⟩ | ⟨a,b,c,d,ha,hb,hc,hd,hz⟩
  · apply formula_lower (n := 2) (by decide)
    rw [hz]
    exact .join (.join (.base ha) (.base hb)) (.base hc)
  · apply formula_lower (n := 2) (by decide)
    rw [hz]
    exact .meet (.join (.base ha) (.base hb)) (.join (.base hc) (.base hd))

theorem exact_circuit_formula_gap :
    ThreeIntersections.Three Rectangle zero ∧ ¬ Two Rectangle zero ∧
    Formula Rectangle 4 zero ∧ ∀ n, n < 4 → ¬ Formula Rectangle n zero :=
  ⟨circuit_three, circuit_lower, formula_four, fun _ => formula_lower⟩

#print axioms exact_circuit_formula_gap
end FiveRowSharing
