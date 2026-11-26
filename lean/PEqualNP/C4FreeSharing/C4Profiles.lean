import PEqualNP.SixSharing.SixFormulaCheck

/-! A seven-column version of the kernel-checked rectangle-profile test.
The rectangle codes still have six bits. Row masks now have seven. -/
namespace C4Profiles
open SixFormulaCheck (Shape Code Domain value profiles complete_profiles)
set_option maxRecDepth 200000
set_option maxHeartbeats 0

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
  simpa [viable,Domains.get] using And.intro (And.intro (And.intro
    (And.intro (And.intro (And.intro ha hb) hc) hh) he) hf) hg

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

def masks : Fin 7 → BitVec 7 := ![113,109,125,106,62,126,79]
def order : List (Fin 7) := [1,4,3,0,6,5,2]
def inputs := order.map masks

end C4Profiles
