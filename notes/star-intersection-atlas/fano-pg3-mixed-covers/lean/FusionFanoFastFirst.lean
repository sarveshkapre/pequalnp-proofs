import FusionFanoFastCheck

/- The first batch also provides a small performance checkpoint before checking
all cases. These are kernel proofs, not results from an external evaluator. -/
namespace FusionFanoCertificates

set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem first_case_checked :
    FusionFanoFastCheck.fastCheck (9593263918, 2, 0) = true := by
  decide +kernel

#print axioms first_case_checked

theorem fast0 : cases0.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast0

end FusionFanoCertificates
