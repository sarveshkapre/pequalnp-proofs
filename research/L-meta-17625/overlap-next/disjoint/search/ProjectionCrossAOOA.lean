import SelectorBits
import KernelProp
namespace DisjointProjected
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000

theorem cross_AOOA (p q r s t u v w : P) (a b : BitVec 12) (c : BitVec 9) :
    realizes true true false true true false p q r s t u v w a b c = false := by
  exclude_selector_case

#print axioms cross_AOOA
end DisjointProjected
