import MatchWindow
import MatchingKernel
namespace MatchProjected
set_option maxRecDepth 300000
set_option maxHeartbeats 70000000
set_option linter.unusedSimpArgs false
theorem window_OAOA (c : Cross) (s t : Fin 4 → Selector) (ts : Fin 3 → TopSel) :
    window c ![true,false,true,false] s t ts = false := by
  simp (config := {decide := true, maxSteps := 5000000}) only [
    window, portOK, topTest, testRow, positive, independent, graphOK, allowed, leafOK,
    topVal, schedule, extend, gate, portRaw, portVal, portNz, side, included,
    lookup4, rawIte, valIte, nzIte, zero, subset, hit, bne, beq6,
    BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, bitIte,
    Bool.false_eq_true, ite_true, ite_false, Bool.and_false, Bool.and_true,
    Bool.or_false, Bool.or_true, Bool.false_and, Bool.true_and, Bool.false_or, Bool.true_or]
  matching_kernel_sat
#print axioms window_OAOA
end MatchProjected
