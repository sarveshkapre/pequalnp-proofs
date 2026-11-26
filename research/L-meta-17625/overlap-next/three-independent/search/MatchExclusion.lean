import MatchOrders
import MatchCaseAAOO
import MatchCaseAOAO
import MatchCaseAOOA
import MatchCaseOAAO
import MatchCaseOAOA
import MatchCaseOOAA

namespace MatchProjected

/-- On three distinct residual pairs, this four-gate window cannot realize the required
acceptances and reject every independent subset of the six terminals. -/
theorem no_realizes {c o s t ts} : ¬ Realizes c o s t ts := by
  intro h
  have yes := h.window_true
  rcases six_orders o h.operations with d|d|d|d|d|d
  · rw [d, window_AAOO] at yes
    contradiction
  · rw [d, window_AOAO] at yes
    contradiction
  · rw [d, window_AOOA] at yes
    contradiction
  · rw [d, window_OAAO] at yes
    contradiction
  · rw [d, window_OAOA] at yes
    contradiction
  · rw [d, window_OOAA] at yes
    contradiction

#print axioms no_realizes
end MatchProjected
