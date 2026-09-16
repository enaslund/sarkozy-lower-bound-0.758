import Sarkozy.OddData437
import Sarkozy.OddMoments
import Sarkozy.Odd437MomentData
import Sarkozy.Odd437Threshold
import Sarkozy.OddKernelSort

/-!
# The target moment of the original fixed 437 witness

The numerical histogram is connected directly to the widths in `OddData437`.
This proof uses no edge-order certificate or alternative ordering of the rows.
Sorting is used only to certify equality of the two multisets of widths.
-/

namespace Sarkozy.Odd437

open scoped BigOperators

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- The original geometric rows have exactly the certified width multiplicities. -/
theorem widths_perm_moment_histogram :
    (rows.map (fun r => r.2.2)).Perm (OddMoments.histogramExpansion momentHistogram) := by
  apply OddKernelSort.perm_of_sort_eq_list 16
  decide +kernel

/-- Histogram transport preserves the original indexed moment at every real power. -/
theorem moment_eq_histogram (f : ℝ) :
    (∑ k : Fin 19683, ((width k : ℝ) / denominator)^f) =
      (momentHistogram.map (fun wc =>
        (wc.2 : ℝ) * ((wc.1 : ℝ) / denominator)^f)).sum := by
  calc
    (∑ k : Fin 19683, ((width k : ℝ) / denominator)^f) =
        ((rows.map (fun r => r.2.2)).map (fun w : ℕ => ((w : ℝ) / denominator)^f)).sum :=
      OddMoments.indexed_width_moment_eq_list rows rows_size denominator f
    _ = ((OddMoments.histogramExpansion momentHistogram).map
        (fun w : ℕ => ((w : ℝ) / denominator)^f)).sum :=
      (widths_perm_moment_histogram.map (fun w : ℕ => ((w : ℝ) / denominator)^f)).sum_eq
    _ = _ := OddMoments.histogram_moment_eq_weighted momentHistogram denominator f

/-- The original fixed 437 witness meets the full target moment without assumptions. -/
theorem target_moment :
    (437^6 : ℝ)^targetExponent ≤ (437^3 : ℕ) *
      ∑ k : Fin 19683, ((width k : ℝ) / denominator)^(componentPowers 7) := by
  apply moment_threshold.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [moment_eq_histogram]
  exact moment_histogram_lower_bound

end Sarkozy.Odd437
