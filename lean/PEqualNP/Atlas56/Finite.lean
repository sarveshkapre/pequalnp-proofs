import PEqualNP.Atlas56.Cover

namespace Atlas56
def patterns : List Pat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]
theorem patterns_nodup : patterns.Nodup := by decide
theorem patterns_full : patterns.toFinset = Finset.univ := by decide
def tail32 : List Entry := []
def tail31 := entry 31 :: tail32
def tail30 := entry 30 :: tail31
def tail29 := entry 29 :: tail30
def tail28 := entry 28 :: tail29
def tail27 := entry 27 :: tail28
def tail26 := entry 26 :: tail27
def tail25 := entry 25 :: tail26
def tail24 := entry 24 :: tail25
def tail23 := entry 23 :: tail24
def tail22 := entry 22 :: tail23
def tail21 := entry 21 :: tail22
def tail20 := entry 20 :: tail21
def tail19 := entry 19 :: tail20
def tail18 := entry 18 :: tail19
def tail17 := entry 17 :: tail18
def tail16 := entry 16 :: tail17
def tail15 := entry 15 :: tail16
def tail14 := entry 14 :: tail15
def tail13 := entry 13 :: tail14
def tail12 := entry 12 :: tail13
def tail11 := entry 11 :: tail12
def tail10 := entry 10 :: tail11
def tail9 := entry 9 :: tail10
def tail8 := entry 8 :: tail9
def tail7 := entry 7 :: tail8
def tail6 := entry 6 :: tail7
def tail5 := entry 5 :: tail6
def tail4 := entry 4 :: tail5
def tail3 := entry 3 :: tail4
def tail2 := entry 2 :: tail3
def tail1 := entry 1 :: tail2
def tail0 := entry 0 :: tail1
theorem table_eq : patterns.map entry = tail0 := rfl

set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem pass32 : check 6 tail32 allGood allExc = true := by decide +kernel
private theorem first31 : check 5 tail32 (allGood &&& good 31) (allExc &&& exc 31) = true := by decide +kernel
private theorem pass31 : check 6 tail31 allGood allExc = true :=
  Bool.and_eq_true_iff.mpr ⟨first31, pass32⟩
private theorem first30 : check 5 tail31 (allGood &&& good 30) (allExc &&& exc 30) = true := by decide +kernel
private theorem pass30 : check 6 tail30 allGood allExc = true :=
  Bool.and_eq_true_iff.mpr ⟨first30, pass31⟩
private theorem first29 : check 5 tail30 (allGood &&& good 29) (allExc &&& exc 29) = true := by decide +kernel
private theorem pass29 : check 6 tail29 allGood allExc = true :=
  Bool.and_eq_true_iff.mpr ⟨first29, pass30⟩
private theorem first28 : check 5 tail29 (allGood &&& good 28) (allExc &&& exc 28) = true := by decide +kernel
private theorem pass28 : check 6 tail28 allGood allExc = true :=
  Bool.and_eq_true_iff.mpr ⟨first28, pass29⟩
private theorem first27 : check 5 tail28 (allGood &&& good 27) (allExc &&& exc 27) = true := by decide +kernel
private theorem pass27 : check 6 tail27 allGood allExc = true :=
  Bool.and_eq_true_iff.mpr ⟨first27, pass28⟩
private theorem first26 : check 5 tail27 (allGood &&& good 26) (allExc &&& exc 26) = true := by decide +kernel
private theorem pass26 : check 6 tail26 allGood allExc = true :=
  Bool.and_eq_true_iff.mpr ⟨first26, pass27⟩
private theorem first25 : check 5 tail26 (allGood &&& good 25) (allExc &&& exc 25) = true := by decide +kernel
private theorem pass25 : check 6 tail25 allGood allExc = true :=
  Bool.and_eq_true_iff.mpr ⟨first25, pass26⟩
private theorem first24 : check 5 tail25 (allGood &&& good 24) (allExc &&& exc 24) = true := by decide +kernel
private theorem pass24 : check 6 tail24 allGood allExc = true :=
  Bool.and_eq_true_iff.mpr ⟨first24, pass25⟩
private theorem first23 : check 5 tail24 (allGood &&& good 23) (allExc &&& exc 23) = true := by decide +kernel
private theorem pass23 : check 6 tail23 allGood allExc = true :=
  Bool.and_eq_true_iff.mpr ⟨first23, pass24⟩
private theorem first22 : check 5 tail23 (allGood &&& good 22) (allExc &&& exc 22) = true := by decide +kernel
private theorem pass22 : check 6 tail22 allGood allExc = true :=
  Bool.and_eq_true_iff.mpr ⟨first22, pass23⟩
private theorem first21 : check 5 tail22 (allGood &&& good 21) (allExc &&& exc 21) = true := by decide +kernel
private theorem pass21 : check 6 tail21 allGood allExc = true :=
  Bool.and_eq_true_iff.mpr ⟨first21, pass22⟩
private theorem first20 : check 5 tail21 (allGood &&& good 20) (allExc &&& exc 20) = true := by decide +kernel
private theorem pass20 : check 6 tail20 allGood allExc = true :=
  Bool.and_eq_true_iff.mpr ⟨first20, pass21⟩
private theorem first19 : check 5 tail20 (allGood &&& good 19) (allExc &&& exc 19) = true := by decide +kernel
private theorem pass19 : check 6 tail19 allGood allExc = true :=
  Bool.and_eq_true_iff.mpr ⟨first19, pass20⟩
private theorem first18 : check 5 tail19 (allGood &&& good 18) (allExc &&& exc 18) = true := by decide +kernel
private theorem pass18 : check 6 tail18 allGood allExc = true :=
  Bool.and_eq_true_iff.mpr ⟨first18, pass19⟩
private theorem first17 : check 5 tail18 (allGood &&& good 17) (allExc &&& exc 17) = true := by decide +kernel
private theorem pass17 : check 6 tail17 allGood allExc = true :=
  Bool.and_eq_true_iff.mpr ⟨first17, pass18⟩
private theorem first16 : check 5 tail17 (allGood &&& good 16) (allExc &&& exc 16) = true := by decide +kernel
private theorem pass16 : check 6 tail16 allGood allExc = true :=
  Bool.and_eq_true_iff.mpr ⟨first16, pass17⟩
private theorem first15 : check 5 tail16 (allGood &&& good 15) (allExc &&& exc 15) = true := by decide +kernel
private theorem pass15 : check 6 tail15 allGood allExc = true :=
  Bool.and_eq_true_iff.mpr ⟨first15, pass16⟩
private theorem first14 : check 5 tail15 (allGood &&& good 14) (allExc &&& exc 14) = true := by decide +kernel
private theorem pass14 : check 6 tail14 allGood allExc = true :=
  Bool.and_eq_true_iff.mpr ⟨first14, pass15⟩
private theorem first13 : check 5 tail14 (allGood &&& good 13) (allExc &&& exc 13) = true := by decide +kernel
private theorem pass13 : check 6 tail13 allGood allExc = true :=
  Bool.and_eq_true_iff.mpr ⟨first13, pass14⟩
private theorem first12 : check 5 tail13 (allGood &&& good 12) (allExc &&& exc 12) = true := by decide +kernel
private theorem pass12 : check 6 tail12 allGood allExc = true :=
  Bool.and_eq_true_iff.mpr ⟨first12, pass13⟩
private theorem first11 : check 5 tail12 (allGood &&& good 11) (allExc &&& exc 11) = true := by decide +kernel
private theorem pass11 : check 6 tail11 allGood allExc = true :=
  Bool.and_eq_true_iff.mpr ⟨first11, pass12⟩
private theorem first10 : check 5 tail11 (allGood &&& good 10) (allExc &&& exc 10) = true := by decide +kernel
private theorem pass10 : check 6 tail10 allGood allExc = true :=
  Bool.and_eq_true_iff.mpr ⟨first10, pass11⟩
private theorem first9 : check 5 tail10 (allGood &&& good 9) (allExc &&& exc 9) = true := by decide +kernel
private theorem pass9 : check 6 tail9 allGood allExc = true :=
  Bool.and_eq_true_iff.mpr ⟨first9, pass10⟩
private theorem first8 : check 5 tail9 (allGood &&& good 8) (allExc &&& exc 8) = true := by decide +kernel
private theorem pass8 : check 6 tail8 allGood allExc = true :=
  Bool.and_eq_true_iff.mpr ⟨first8, pass9⟩
private theorem first7 : check 5 tail8 (allGood &&& good 7) (allExc &&& exc 7) = true := by decide +kernel
private theorem pass7 : check 6 tail7 allGood allExc = true :=
  Bool.and_eq_true_iff.mpr ⟨first7, pass8⟩
private theorem first6 : check 5 tail7 (allGood &&& good 6) (allExc &&& exc 6) = true := by decide +kernel
private theorem pass6 : check 6 tail6 allGood allExc = true :=
  Bool.and_eq_true_iff.mpr ⟨first6, pass7⟩
private theorem first5 : check 5 tail6 (allGood &&& good 5) (allExc &&& exc 5) = true := by decide +kernel
private theorem pass5 : check 6 tail5 allGood allExc = true :=
  Bool.and_eq_true_iff.mpr ⟨first5, pass6⟩
private theorem first4 : check 5 tail5 (allGood &&& good 4) (allExc &&& exc 4) = true := by decide +kernel
private theorem pass4 : check 6 tail4 allGood allExc = true :=
  Bool.and_eq_true_iff.mpr ⟨first4, pass5⟩
private theorem first3 : check 5 tail4 (allGood &&& good 3) (allExc &&& exc 3) = true := by decide +kernel
private theorem pass3 : check 6 tail3 allGood allExc = true :=
  Bool.and_eq_true_iff.mpr ⟨first3, pass4⟩
private theorem first2 : check 5 tail3 (allGood &&& good 2) (allExc &&& exc 2) = true := by decide +kernel
private theorem pass2 : check 6 tail2 allGood allExc = true :=
  Bool.and_eq_true_iff.mpr ⟨first2, pass3⟩
private theorem first1 : check 5 tail2 (allGood &&& good 1) (allExc &&& exc 1) = true := by decide +kernel
private theorem pass1 : check 6 tail1 allGood allExc = true :=
  Bool.and_eq_true_iff.mpr ⟨first1, pass2⟩
private theorem first0 : check 5 tail1 (allGood &&& good 0) (allExc &&& exc 0) = true := by decide +kernel
private theorem pass0 : check 6 tail0 allGood allExc = true :=
  Bool.and_eq_true_iff.mpr ⟨first0, pass1⟩

theorem complete_check : check 6 (patterns.map entry) allGood allExc = true := by
  rw [table_eq]
  exact pass0
end Atlas56
