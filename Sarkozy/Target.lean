import Sarkozy.Moment
import Sarkozy.Parameters

/-!
# A modular interface for the nine interval certificates

The moduli, moment powers, and positive contribution surplus are fixed and
proved. The hypotheses describe the finite expanded alphabets,
their interval geometry, and their numerical moments. No asymptotic lemma
or word-construction assertion is assumed.

The concrete alphabets and all their certificate hypotheses are discharged
elsewhere in the library. `Sarkozy.FullTarget` assembles the unconditional
result; this interface also supports alternative certificates at the same bases.
-/

namespace Sarkozy

open scoped BigOperators

/-- Finite interval certificates at the nine fixed bases imply the improved
exponent for every sufficiently large `N`, with any positive epsilon loss. -/
theorem target_exponent_of_interval_certificates
    (C : Fin 9 → Finset ℤ) (a w : Fin 9 → ℤ → ℝ) (σ ρ : ℝ)
    (hC : ∀ i, ∀ x ∈ C i, 0 ≤ x ∧ x < componentBases i)
    (hσ : 0 < σ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hgeom : ∀ i, ∀ x ∈ C i,
      0 ≤ a i x ∧ σ ≤ w i x ∧ w i x ≤ ρ ∧ a i x + w i x ≤ 1)
    (horder : ∀ i, IntervalOrderedModulo (C i) (componentBases i) (a i) (w i))
    (hmoment : ∀ i, (componentBases i : ℝ) ^ targetExponent ≤
      ∑ x ∈ C i, (w i x) ^ (componentPowers i)) :
    LowerBoundExponent targetExponent := by
  exact interval_moment_exponent C componentBases a w componentPowers
    targetExponent σ ρ componentBases_gt_one componentBases_coprime
    componentBases_square hC hσ hρ hρ1 hgeom horder targetExponent_nonneg
    componentPowers_nonneg hmoment componentPowers_budget

end Sarkozy
