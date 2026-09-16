import Sarkozy
import Solution

-- These declarations should depend only on Lean's standard foundational axioms.
#print axioms Sarkozy.reverseRank_realization
#print axioms Sarkozy.crt_reverseRank_realization
#print axioms Sarkozy.two_four_squareDifferenceFree
#print axioms Sarkozy.six_elements_in_eighty_four
#print axioms Sarkozy.ranked_word_realization
#print axioms Sarkozy.geometric_family_exponent
#print axioms Sarkozy.stopping_selection
#print axioms Sarkozy.interval_moment_exponent
#print axioms Sarkozy.componentPowers_surplus
#print axioms Sarkozy.target_exponent_of_interval_certificates
#print axioms Sarkozy.exponent_three_fifths
#print axioms SarkozySubmission.interval_moment_bound

-- Construction assumptions discharged for the full numerical target.
#print axioms Sarkozy.exists_uniform_width_bounds
#print axioms Sarkozy.concretePrime_certified_moment
#print axioms Sarkozy.odd_prime_interval_lift
#print axioms Sarkozy.BinaryData.geometry_verified
#print axioms Sarkozy.RecordBinary.policy_valid
#print axioms Sarkozy.BinaryAlphabet.family_fits
#print axioms Sarkozy.BinaryAlphabet.root_interval_certificate
#print axioms Sarkozy.RecordBinary.interval_certificate
#print axioms Sarkozy.target_exponent_of_three_interval_certificates
#print axioms Sarkozy.target_exponent_of_odd_low_supports
#print axioms Sarkozy.record_exponent_of_finite_checks
#print axioms Sarkozy.RecordBinary.depth_condition
#print axioms Sarkozy.RecordBinary.rows_verified
#print axioms Sarkozy.record_binary_interval_certificate
#print axioms Sarkozy.target_exponent_of_two_odd_interval_certificates
#print axioms Sarkozy.primeLowFinite_iff
#print axioms Sarkozy.record_odd_finite_certificate
#print axioms Sarkozy.Odd215.rows_size
#print axioms Sarkozy.Odd215.rows_valid
#print axioms Sarkozy.Odd215.point_injective

-- Fixed odd witnesses and exact numerical checker.
#print axioms Sarkozy.record_exponent_of_actual_odd_checks
#print axioms Sarkozy.Odd437.rows_size
#print axioms Sarkozy.Odd437.rows_valid
#print axioms Sarkozy.Odd437.rows_sorted
#print axioms Sarkozy.Odd437.point_injective
#print axioms Sarkozy.Odd437.endpoint_bound
#print axioms Sarkozy.Odd437.moment_threshold
#print axioms Sarkozy.PowerChecker.sound
#print axioms Sarkozy.PowerPolynomial.log_comparison_of_nat
#print axioms Sarkozy.OddMoments.indexed_width_moment_eq_histogram

-- The complete 215 witness and the final two checks on the actual 437 witness.
#print axioms Sarkozy.OddOrder.predecessors_sound
#print axioms Sarkozy.OddOrder.interval_order_of_checked_rows
#print axioms Sarkozy.OddOrder215.sources_checked
#print axioms Sarkozy.OddOrder215.targets_checked
#print axioms Sarkozy.OddOrder215.low_order
#print axioms Sarkozy.OddOrder215.point_injective
#print axioms Sarkozy.Odd215.moment_entries_checked
#print axioms Sarkozy.Odd215.moment_histogram_lower_bound
#print axioms Sarkozy.Odd215.target_moment
#print axioms Sarkozy.OddOrder215.widths_match_histogram
#print axioms Sarkozy.OddOrder215.target_moment
#print axioms Sarkozy.OddOrder215.interval_certificate
#print axioms Sarkozy.target_exponent_of_one_odd_interval_certificate
#print axioms Sarkozy.record_exponent_of_437_checks

#print axioms Sarkozy.OddKernelSort.perm_of_sort_eq
#print axioms Sarkozy.OddOrder.fastTargetCheck_eq
#print axioms Sarkozy.OddOrder.allIndexed_of_blocks

-- Both odd certificates and the unconditional full exponent.
#print axioms Sarkozy.OddOrder437.sources_checked
#print axioms Sarkozy.OddOrder437.targets_checked
#print axioms Sarkozy.OddOrder437.low_order
#print axioms Sarkozy.OddOrder437.point_injective
#print axioms Sarkozy.Odd437.moment_histogram_lower_bound
#print axioms Sarkozy.Odd437.target_moment
#print axioms Sarkozy.OddOrder437.widths_match_histogram
#print axioms Sarkozy.OddOrder437.target_moment
#print axioms Sarkozy.OddOrder437.interval_certificate
#print axioms Sarkozy.record_exponent
#print axioms SarkozySubmission.improved_bound
#print axioms Sarkozy.Odd437.moment_entry_lower
#print axioms Sarkozy.Odd437.moment_blocks_lower
#print axioms Sarkozy.Odd437.MomentChunk000.lower_bound

-- Boolean endpoint checking avoids a deep recursive decidability proof.
#print axioms Sarkozy.OddOrder.adjacentLE_sound
#print axioms Sarkozy.OddOrder437.endpoints_sorted_checked

-- Shared exact natural-number checker used by both odd witnesses.
#print axioms Sarkozy.PowerChecker.endpoint_valid_sound
