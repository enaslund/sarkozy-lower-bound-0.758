import Sarkozy.OddOrder215
import Sarkozy.Odd215MomentData
import Sarkozy.Odd215Threshold
import Sarkozy.OddMoments
import Sarkozy.OddKernelSort
import Sarkozy.ActualOddTarget

/-!
# The complete reconstructed 215 interval certificate

The geometry rows are sorted by right endpoint, whereas the numerical
certificate is organized by width and multiplicity. A kernel-checked equality
of sorted width lists connects them. Every input to the finite odd lift,
including its target moment, is then discharged for this witness.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Sarkozy.OddOrder215

open scoped BigOperators

theorem widths_match_histogram :
    (rows.map (fun r => r.1.2.2)).Perm
      (OddMoments.histogramExpansion Odd215.momentHistogram) := by
  apply OddKernelSort.perm_of_sort_eq_list 14
  decide +kernel

theorem moment_eq_histogram (f : ℝ) :
    (∑ k : Fin 4913, ((width k : ℝ)/denominator)^f) =
      (Odd215.momentHistogram.map (fun wc =>
        (wc.2 : ℝ) * ((wc.1 : ℝ)/denominator)^f)).sum := by
  have hs := OddMoments.indexed_sum_eq_list rows rows_size
    (fun r => ((r.1.2.2 : ℝ)/denominator)^f)
  change (∑ k : Fin 4913, ((width k : ℝ)/denominator)^f) = _ at hs
  rw [hs]
  have hp := widths_match_histogram
  have hm := (hp.map (fun w : ℕ => ((w : ℝ)/denominator)^f)).sum_eq
  simp only [List.map_map, Function.comp_def] at hm
  exact hm.trans (OddMoments.histogram_moment_eq_weighted Odd215.momentHistogram denominator f)

/-- The full target moment at the original rational component power. -/
theorem target_moment :
    (215^6 : ℝ)^targetExponent ≤ (215^3 : ℕ) *
      ∑ k : Fin 4913, ((width k : ℝ)/denominator)^(componentPowers 6) := by
  apply Odd215.moment_threshold.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [moment_eq_histogram]
  exact Odd215.moment_histogram_lower_bound

/-- The entire 215 component, including its expanded CRT alphabet and moment,
exists without any unproved finite-certificate hypotheses. -/
theorem interval_certificate :
    ∃ (C : Finset ℤ) (a w : ℤ → ℝ),
      (∀ x ∈ C, 0 ≤ x ∧ x < componentBases 6) ∧
      (∀ x ∈ C, 0 ≤ a x ∧ 0 < w x ∧ w x < 1 ∧ a x+w x ≤ 1) ∧
      IntervalOrderedModulo C (componentBases 6) a w ∧
      (componentBases 6 : ℝ)^targetExponent ≤
        ∑ x ∈ C, (w x)^(componentPowers 6) := by
  apply record_odd_interval_of_integer_checks 0 4913 denominator point start width
    denominator_pos point_bounds point_injective width_bounds endpoint_bound low_order
  change ((215^6 : ℕ) : ℝ)^targetExponent ≤ (215^3 : ℕ) *
    ∑ k : Fin 4913, ((width k : ℝ)/denominator)^(componentPowers 6)
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using target_moment

end Sarkozy.OddOrder215
