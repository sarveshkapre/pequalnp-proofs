import PEqualNP.SixSharing.ThreeIntersectionsFormula

/-! Exhaust the four formula shapes on the 6 by 6 zero matrix.
A bit in a column domain is a six-bit rectangle-side assignment still
consistent with the rows already read. All finite checks use the kernel. -/
namespace SixFormulaCheck
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

def Domains.get (s : Domains) : Fin 6 → Domain := ![s.a,s.b,s.c,s.d,s.e,s.f]
def full : Domains := ⟨-1,-1,-1,-1,-1,-1⟩

def restrictTo (old h : Domain) (pos : Bool) : Domain :=
  old &&& (if pos then h else ~~~h)

def advance (d : Domains) (p : Code) (h : Domain) : Domains :=
  ⟨restrictTo d.a h (p.getLsbD 0), restrictTo d.b h (p.getLsbD 1),
   restrictTo d.c h (p.getLsbD 2), restrictTo d.d h (p.getLsbD 3),
   restrictTo d.e h (p.getLsbD 4), restrictTo d.f h (p.getLsbD 5)⟩

def viable (d : Domains) : Bool :=
  d.a != 0 && d.b != 0 && d.c != 0 && d.d != 0 && d.e != 0 && d.f != 0

def search (hs : List Domain) : List Code → Domains → Bool
  | [], _ => true
  | p :: ps, d => hs.any fun h =>
      let next := advance d p h
      viable next && search hs ps next

def Keeps (d : Domains) (cols : Fin 6 → Code) : Prop :=
  ∀ j, (d.get j).getLsbD (cols j).toNat = true

theorem full_keeps (cols : Fin 6 → Code) : Keeps full cols := by
  have ones : ∀ c : Code, (-1 : Domain).getLsbD c.toNat = true := by decide +kernel
  intro j
  fin_cases j <;> exact ones _

private theorem kept_viable {d : Domains} {cols : Fin 6 → Code} (hd : Keeps d cols) :
    viable d = true := by
  have nonzero (i : Fin 6) : d.get i ≠ 0 := by
    intro hi
    have h := hd i
    simp [hi] at h
  have ha := nonzero 0
  have hb := nonzero 1
  have hc := nonzero 2
  have hh := nonzero 3
  have he := nonzero 4
  have hf := nonzero 5
  simpa [viable,Domains.get] using And.intro (And.intro (And.intro
    (And.intro (And.intro ha hb) hc) hh) he) hf

private theorem advance_keeps {d : Domains} {cols : Fin 6 → Code} (hd : Keeps d cols)
    (p : Code) (h : Domain) (hh : ∀ j : Fin 6, h.getLsbD (cols j).toNat = p.getLsbD j.val) :
    Keeps (advance d p h) cols := by
  intro j
  have eqn : (advance d p h).get j = restrictTo (d.get j) h (p.getLsbD j.val) := by
    fin_cases j <;> rfl
  have within : (cols j).toNat < 64 := (cols j).isLt
  rw [eqn]
  cases hb : p.getLsbD j.val <;>
    simp only [restrictTo, Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,
      BitVec.getLsbD_not,hd j,hh j,hb,within,Bool.true_and] <;> rfl

theorem search_complete (hs : List Domain) (cols : Fin 6 → Code) (ps : List Code)
    (matchRows : ∀ p ∈ ps, ∃ h ∈ hs, ∀ j : Fin 6, h.getLsbD (cols j).toNat = p.getLsbD j.val)
    (d : Domains) (hd : Keeps d cols) : search hs ps d = true := by
  induction ps generalizing d with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨h,hm,hh⟩ := matchRows p (by simp)
    have hk := advance_keeps hd p h hh
    apply List.any_eq_true.mpr
    exact ⟨h,hm,Bool.and_eq_true_iff.mpr ⟨kept_viable hk,
      ih (fun p hp => matchRows p (by simp [hp])) _ hk⟩⟩

def masks : Fin 6 → Code := ![44,22,29,62,32,56]
def order : List (Fin 6) := [2,1,0,5,3,4]
def inputs : List Code := order.map masks

end SixFormulaCheck
