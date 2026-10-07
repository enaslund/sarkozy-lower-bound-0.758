module

public import Sarkozy.OddOrder437
public import Sarkozy.Odd437WidthHistogram
public import Sarkozy.Odd437MomentData
public import Sarkozy.Odd437Threshold
public import Sarkozy.OddMoments
public import Sarkozy.OddKernelSort
public import Sarkozy.ActualOddTarget

@[expose] public section
set_option backward.privateInPublic true

/-!
# The complete (19,23) interval certificate

The geometry rows are sorted by right endpoint, whereas the numerical
certificate is organized by width and multiplicity. A kernel-checked equality
of sorted width lists connects them. Every input to the finite odd lift,
including its target moment, is discharged for this witness.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Sarkozy.OddOrder437

open scoped BigOperators

theorem moment_eq_histogram (f : ℝ) :
    (∑ k : Fin 3645, ((width k : ℝ)/denominator)^f) =
      (Odd437.momentHistogram.map (fun wc =>
        (wc.2 : ℝ) * ((wc.1 : ℝ)/denominator)^f)).sum := by
  have hs := OddMoments.indexed_sum_eq_list rows rows_size
    (fun r => ((r.1.2.2 : ℝ)/denominator)^f)
  change (∑ k : Fin 3645, ((width k : ℝ)/denominator)^f) = _ at hs
  rw [hs]
  have hp := widths_match_histogram
  have hm := (hp.map (fun w : ℕ => ((w : ℝ)/denominator)^f)).sum_eq
  simp only [List.map_map, Function.comp_def] at hm
  exact hm.trans (OddMoments.histogram_moment_eq_weighted Odd437.momentHistogram denominator f)

/-- The full target moment at the original rational component power. -/
theorem target_moment :
    (3628411^2 : ℝ)^targetExponent ≤ (3628411 : ℕ) *
      ∑ k : Fin 3645, ((width k : ℝ)/denominator)^(componentPowers 7) := by
  apply Odd437.moment_threshold.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [moment_eq_histogram]
  exact Odd437.moment_histogram_lower_bound

/-- The entire (19,23) component, including its expanded CRT alphabet and moment,
exists without any unproved finite-certificate hypotheses. -/
theorem interval_certificate :
    ∃ (C : Finset ℤ) (a w : ℤ → ℝ),
      (∀ x ∈ C, 0 ≤ x ∧ x < componentBases 7) ∧
      (∀ x ∈ C, 0 ≤ a x ∧ 0 < w x ∧ w x < 1 ∧ a x+w x ≤ 1) ∧
      IntervalOrderedModulo C (componentBases 7) a w ∧
      (componentBases 7 : ℝ)^targetExponent ≤
        ∑ x ∈ C, (w x)^(componentPowers 7) := by
  apply record_odd_interval_of_integer_checks 1 3645 denominator point start width
    denominator_pos point_bounds point_injective width_bounds endpoint_bound low_order
  change ((3628411^2 : ℕ) : ℝ)^targetExponent ≤ (3628411 : ℕ) *
    ∑ k : Fin 3645, ((width k : ℝ)/denominator)^(componentPowers 7)
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using target_moment

end Sarkozy.OddOrder437
