import PEqualNP.C4FreeSharing.C4Profiles
namespace ForestProfiles
open C4Profiles (advance full viable search search_complete full_keeps)

def masks : Fin 7 → BitVec 7 := ![117,109,106,62,126,79,119]
def order : List (Fin 7) := [1,3,2,0,5,4,6]
def inputs := order.map masks

open SixFormulaCheck (Shape Code Domain value profiles complete_profiles)
set_option maxHeartbeats 0
set_option maxRecDepth 200000

/-- Split on the profile of row 1. Splitting the computation into lemmas
keeps the memory needed for one kernel reduction bounded. -/
private def branch (s : Shape) (h : Domain) : Bool :=
  let next := advance full 109 h
  viable next && search (profiles s) [62,106,117,79,126,119] next

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

theorem no_representation (s : Shape) (rows cols : Fin 7 → Code)
    (hm : ∀ i j, value s (rows i &&& cols j) = (masks i).getLsbD j.val) : False := by
  have allRows : ∀ p ∈ inputs, ∃ h ∈ profiles s,
      ∀ j : Fin 7, h.getLsbD (cols j).toNat = p.getLsbD j.val := by
    intro p hp
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
    obtain ⟨h,hh,hv⟩ := complete_profiles s (rows i)
    exact ⟨h,hh,fun j => (hv (cols j)).trans (hm i j)⟩
  have accepted := search_complete (profiles s) cols inputs allRows full (full_keeps cols)
  cases s <;> simp_all only [fails_four,fails_threeTwo,fails_cube,fails_outside,Bool.false_eq_true]

end ForestProfiles
