import SelectorBits
import KernelProp
namespace DisjointProjected
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000

theorem inside_AAOO (p q r s t u v w : P) (a b : BitVec 12) (c : BitVec 9) :
    realizes true false false false true true p q r s t u v w a b c = false := by
  exclude_selector_case

#print axioms inside_AAOO
end DisjointProjected
