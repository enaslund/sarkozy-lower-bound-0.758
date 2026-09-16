import Sarkozy.FiniteAlphabets
import Sarkozy.PrimeChains
import Sarkozy.Parameters
import Sarkozy.ChainMoments

/-!
# A modular interface adjoining three components to the prime chains

The first six alphabets and their numerical moments are explicit checked
constructions, not supplied hypotheses. The two odd composite alphabets and
the binary alphabet are the three interval inputs to this interface.
Common width bounds are derived from finiteness. The concrete inputs are
proved in the library; `Sarkozy.FullTarget` assembles the unconditional result.
-/

namespace Sarkozy

open scoped BigOperators

theorem chain_component_base (i : Fin 6) :
    componentBases (Fin.castAdd 3 i) = primeChainPrimes i ^ 2 := by
  fin_cases i <;> rfl

/-- Combine three interval certificates with the six proved prime-chain
alphabets, including their ordering, geometry and numerical moments. -/
theorem target_exponent_of_three_interval_certificates
    (C : Fin 3 → Finset ℤ) (a w : Fin 3 → ℤ → ℝ)
    (hC : ∀ i, ∀ x ∈ C i, 0 ≤ x ∧ x < componentBases (Fin.natAdd 6 i))
    (hgeom : ∀ i, ∀ x ∈ C i,
      0 ≤ a i x ∧ 0 < w i x ∧ w i x < 1 ∧ a i x + w i x ≤ 1)
    (horder : ∀ i, IntervalOrderedModulo (C i) (componentBases (Fin.natAdd 6 i))
      (a i) (w i))
    (hmoment : ∀ i : Fin 3,
      (componentBases (Fin.natAdd 6 i) : ℝ) ^ targetExponent ≤
        ∑ x ∈ C i, (w i x) ^ (componentPowers (Fin.natAdd 6 i))) :
    LowerBoundExponent targetExponent := by
  let D : Fin 9 → Finset ℤ := Fin.append concretePrimeDigits C
  let A : Fin 9 → ℤ → ℝ := Fin.append concretePrimeStart a
  let W : Fin 9 → ℤ → ℝ := Fin.append concretePrimeWidth w
  apply interval_moment_exponent_of_pointwise_widths D componentBases A W
    componentPowers targetExponent componentBases_gt_one componentBases_coprime
    componentBases_square
  · intro i
    refine Fin.addCases (m := 6) (n := 3) (fun j => ?_) (fun j => ?_) i
    · simpa [D, chain_component_base] using concretePrimeDigits_bounds j
    · simpa [D] using hC j
  · intro i
    refine Fin.addCases (m := 6) (n := 3) (fun j => ?_) (fun j => ?_) i
    · intro x hx
      have g := concretePrime_geometry j x (by simpa [D] using hx)
      simpa [A, W] using
        (show 0 ≤ concretePrimeStart j x ∧ 0 < concretePrimeWidth j x ∧
          concretePrimeWidth j x < 1 ∧
          concretePrimeStart j x + concretePrimeWidth j x ≤ 1 from
          ⟨g.1, lt_of_lt_of_le (by norm_num) g.2.1,
           lt_of_le_of_lt g.2.2.1 (by norm_num), g.2.2.2⟩)
    · simpa [D, A, W] using hgeom j
  · intro i
    refine Fin.addCases (m := 6) (n := 3) (fun j => ?_) (fun j => ?_) i
    · simpa [D, A, W, chain_component_base] using concretePrime_interval_ordered j
    · simpa [D, A, W] using horder j
  · exact targetExponent_nonneg
  · exact componentPowers_nonneg
  · intro i
    refine Fin.addCases (m := 6) (n := 3) (fun j => ?_) (fun j => ?_) i
    · have hj : Fin.castLE (by decide : 6 ≤ 9) j = Fin.castAdd 3 j := by
        apply Fin.ext
        rfl
      simpa [D, W, hj] using concretePrime_certified_moment j
    · simpa [D, W] using hmoment j
  · exact componentPowers_budget

end Sarkozy
