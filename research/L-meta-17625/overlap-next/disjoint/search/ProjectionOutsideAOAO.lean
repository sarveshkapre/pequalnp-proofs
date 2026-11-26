import SelectorBits
import KernelProp
namespace DisjointProjected
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000

theorem outside_AOAO (p q r s t u v w : P) (a b : BitVec 12) (c : BitVec 9) :
    realizes false false false true false true p q r s t u v w a b c = false := by
  exclude_selector_case

#print axioms outside_AOAO
end DisjointProjected
