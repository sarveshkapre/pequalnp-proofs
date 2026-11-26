import PEqualNP.ThreeGateGain.FiniteHost00
import PEqualNP.ThreeGateGain.FiniteHost01
import PEqualNP.ThreeGateGain.FiniteHost02
import PEqualNP.ThreeGateGain.FiniteHost03
import PEqualNP.ThreeGateGain.FiniteV04P004
import PEqualNP.ThreeGateGain.FiniteV05P019
import PEqualNP.ThreeGateGain.FiniteV08P003
import PEqualNP.ThreeGateGain.FiniteV10P005
import PEqualNP.ThreeGateGain.FiniteV12P007
import PEqualNP.ThreeGateGain.FiniteQuickSound

namespace GainFinite

set_option maxHeartbeats 0
set_option maxRecDepth 200000

/-- Every scalar host obeys the independently replayable finite score bound. -/
theorem all_checked : ∀ h : Host, checkHost h = true := by
  intro h; fin_cases h
  · exact census00
  · exact census01
  · exact census02
  · exact census03
  · exact quickHost_sound 4 F4.passed
  · exact quickHost_sound 5 F5.passed
  · decide +kernel
  · decide +kernel
  · exact quickHost_sound 8 F8.passed
  · decide +kernel
  · exact quickHost_sound 10 F10.passed
  · decide +kernel
  · exact quickHost_sound 12 F12.passed
  · decide +kernel
  · decide +kernel
  · decide +kernel

#print axioms all_checked
end GainFinite
