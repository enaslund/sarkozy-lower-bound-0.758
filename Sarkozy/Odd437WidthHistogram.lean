import Sarkozy.OddOrderData437
import Sarkozy.Odd437MomentData
import Sarkozy.OddMoments
import Sarkozy.OddKernelSort

/-!
# Width histogram of the endpoint-sorted 437 rows

This finite identity is checked separately from edge ordering, so the two
independent certificates can be built without duplicating their large checks.
Boolean list equality is converted to mathematical equality by the proved
`LawfulBEq` interface, avoiding a deep recursive decidable-equality proof.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Sarkozy.OddOrder437

theorem widths_match_histogram :
    (rows.map (fun r => r.1.2.2)).Perm
      (OddMoments.histogramExpansion Odd437.momentHistogram) := by
  apply OddKernelSort.perm_of_sort_eq_list 16
  apply eq_of_beq
  decide +kernel

end Sarkozy.OddOrder437
