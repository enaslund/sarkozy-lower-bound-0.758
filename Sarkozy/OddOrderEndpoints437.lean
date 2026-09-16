import Sarkozy.OddOrderData437
import Sarkozy.OddEndpointCheck

/-!
# Endpoint ordering through a Boolean certificate

This proves the same endpoint order as the original global `IsChain` decision,
but keeps the computed certificate Boolean. It avoids the independent checker's
deep recursive proof construction for a 19,683-element `IsChain` proposition.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Sarkozy.OddOrder437

/-- All adjacent right endpoints are ordered, checked by the ordinary kernel. -/
theorem endpoints_sorted_checked : (rows.map OddOrder.entryEnd).IsChain (· ≤ ·) := by
  apply OddOrder.adjacentLE_sound
  decide +kernel

end Sarkozy.OddOrder437
