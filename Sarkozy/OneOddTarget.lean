import Sarkozy.Odd215Certificate

/-!
# A modular interface for the 437 component

The six prime chains, the entire binary component and the complete 215 odd
component are supplied by proved library certificates. The first interface
takes a single expanded 437 interval certificate. The second fixes the actual
19,683 low rows and takes their order and moment checks. `Sarkozy.FullTarget`
discharges the 437 certificate and proves the unconditional result.
-/

namespace Sarkozy

open scoped BigOperators

theorem target_exponent_of_one_odd_interval_certificate
    (C : Finset ℤ) (a w : ℤ → ℝ)
    (hC : ∀ x ∈ C, 0 ≤ x ∧ x < componentBases 7)
    (hgeom : ∀ x ∈ C, 0 ≤ a x ∧ 0 < w x ∧ w x < 1 ∧ a x+w x ≤ 1)
    (horder : IntervalOrderedModulo C (componentBases 7) a w)
    (hmoment : (componentBases 7 : ℝ)^targetExponent ≤
      ∑ x ∈ C, (w x)^(componentPowers 7)) : LowerBoundExponent targetExponent := by
  obtain ⟨C0,a0,w0,hC0,hgeom0,hord0,hmom0⟩ := OddOrder215.interval_certificate
  apply target_exponent_of_two_odd_interval_certificates ![C0,C] ![a0,a] ![w0,w]
  · intro i; fin_cases i
    · exact hC0
    · exact hC
  · intro i; fin_cases i
    · exact hgeom0
    · exact hgeom
  · intro i; fin_cases i
    · exact hord0
    · exact horder
  · intro i; fin_cases i
    · exact hmom0
    · exact hmoment

/-- The full result from only the ordering and moment of the actual 437 data.
Its point bounds, distinctness, and interval geometry are already proved. -/
theorem record_exponent_of_437_checks
    (horder : ∀ k l, k ≠ l →
      (∀ i, PrimeLowRelated (recordOddPrimes 1 i) 3
        (Odd437.point k i : ℤ) (Odd437.point l i : ℤ)) →
      Odd437.start k + Odd437.width k ≤ Odd437.start l)
    (hmoment : (437^6 : ℝ)^targetExponent ≤ (437^3 : ℕ) *
      ∑ k : Fin 19683, ((Odd437.width k : ℝ)/Odd437.denominator)^(componentPowers 7)) :
    LowerBoundExponent targetExponent := by
  obtain ⟨C,a,w,hC,hgeom,hord,hmom⟩ :=
    record_odd_interval_of_integer_checks 1 19683 Odd437.denominator
      Odd437.point Odd437.start Odd437.width Odd437.denominator_pos
      Odd437.point_bounds Odd437.point_injective Odd437.width_bounds
      Odd437.endpoint_bound horder (by
        change ((437^6 : ℕ) : ℝ)^targetExponent ≤ (437^3 : ℕ) *
          ∑ k : Fin 19683, ((Odd437.width k : ℝ)/Odd437.denominator)^(componentPowers 7)
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using hmoment)
  exact target_exponent_of_one_odd_interval_certificate C a w hC hgeom hord hmom

end Sarkozy
