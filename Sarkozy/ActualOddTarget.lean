import Sarkozy.OddData215
import Sarkozy.OddData437
import Sarkozy.TwoOddTarget

/-!
# Interfaces for integer odd certificates and the actual witnesses

The first interface converts integer low-point checks to an expanded interval
certificate. The second specializes to the actual low points and intervals,
using their proved geometry and taking order and moment checks as inputs.
The concrete checks are all proved in the library; `Sarkozy.FullTarget`
assembles the unconditional result.
-/

namespace Sarkozy

open scoped BigOperators

theorem record_odd_interval_of_integer_checks
    (j : Fin 2) (n D : ℕ) (point : Fin n → Fin 2 → ℕ)
    (start width : Fin n → ℕ)
    (hD : 0 < D)
    (hpoint : ∀ k i, point k i < (recordOddPrimes j i)^3)
    (hinj : Function.Injective point)
    (hwidth : ∀ k, 0 < width k ∧ width k < D)
    (hend : ∀ k, start k + width k ≤ D)
    (horder : ∀ k l, k ≠ l →
      (∀ i, PrimeLowRelated (recordOddPrimes j i) 3
        (point k i : ℤ) (point l i : ℤ)) → start k + width k ≤ start l)
    (hmoment : (componentBases (recordOddIndex j) : ℝ)^targetExponent ≤
      (recordOddRoots j ^ 3 : ℕ) *
        ∑ k : Fin n, ((width k : ℝ)/D)^(componentPowers (recordOddIndex j))) :
    ∃ (C : Finset ℤ) (a w : ℤ → ℝ),
      (∀ x ∈ C, 0 ≤ x ∧ x < componentBases (recordOddIndex j)) ∧
      (∀ x ∈ C, 0 ≤ a x ∧ 0 < w x ∧ w x < 1 ∧ a x+w x ≤ 1) ∧
      IntervalOrderedModulo C (componentBases (recordOddIndex j)) a w ∧
      (componentBases (recordOddIndex j) : ℝ)^targetExponent ≤
        ∑ x ∈ C, (w x)^(componentPowers (recordOddIndex j)) := by
  obtain ⟨S, left, widthS, _, hgeom, hord, hmom⟩ :=
    record_odd_finite_certificate j n D point start width
      hD hpoint hinj hwidth hend horder
  obtain ⟨C, a, w, _, hC, hgeomC, hordC, hmomC⟩ :=
    record_odd_interval_alphabet j S left widthS hgeom hord
  refine ⟨C, a, w, hC, hgeomC, hordC, ?_⟩
  rw [hmomC, hmom]
  exact hmoment

/-- An interface for the actual witnesses' two order and two moment checks.
All construction and asymptotic steps are supplied by proved library lemmas. -/
theorem record_exponent_of_actual_odd_checks
    (horder215 : ∀ k l, k ≠ l →
      (∀ i, PrimeLowRelated (recordOddPrimes 0 i) 3
        (Odd215.point k i : ℤ) (Odd215.point l i : ℤ)) →
      Odd215.start k + Odd215.width k ≤ Odd215.start l)
    (hmoment215 : (215^6 : ℝ)^targetExponent ≤ (215^3 : ℕ) *
      ∑ k : Fin 4913, ((Odd215.width k : ℝ)/Odd215.denominator)^(componentPowers 6))
    (horder437 : ∀ k l, k ≠ l →
      (∀ i, PrimeLowRelated (recordOddPrimes 1 i) 3
        (Odd437.point k i : ℤ) (Odd437.point l i : ℤ)) →
      Odd437.start k + Odd437.width k ≤ Odd437.start l)
    (hmoment437 : (437^6 : ℝ)^targetExponent ≤ (437^3 : ℕ) *
      ∑ k : Fin 19683, ((Odd437.width k : ℝ)/Odd437.denominator)^(componentPowers 7)) :
    LowerBoundExponent targetExponent := by
  obtain ⟨C0,a0,w0,hC0,hgeom0,hord0,hmom0⟩ :=
    record_odd_interval_of_integer_checks 0 4913 Odd215.denominator
      Odd215.point Odd215.start Odd215.width Odd215.denominator_pos
      Odd215.point_bounds Odd215.point_injective Odd215.width_bounds
      Odd215.endpoint_bound horder215 (by
        change ((215^6 : ℕ) : ℝ)^targetExponent ≤ (215^3 : ℕ) *
          ∑ k : Fin 4913, ((Odd215.width k : ℝ)/Odd215.denominator)^(componentPowers 6)
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using hmoment215)
  obtain ⟨C1,a1,w1,hC1,hgeom1,hord1,hmom1⟩ :=
    record_odd_interval_of_integer_checks 1 19683 Odd437.denominator
      Odd437.point Odd437.start Odd437.width Odd437.denominator_pos
      Odd437.point_bounds Odd437.point_injective Odd437.width_bounds
      Odd437.endpoint_bound horder437 (by
        change ((437^6 : ℕ) : ℝ)^targetExponent ≤ (437^3 : ℕ) *
          ∑ k : Fin 19683, ((Odd437.width k : ℝ)/Odd437.denominator)^(componentPowers 7)
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using hmoment437)
  apply target_exponent_of_two_odd_interval_certificates ![C0,C1] ![a0,a1] ![w0,w1]
  · intro i; fin_cases i
    · exact hC0
    · exact hC1
  · intro i; fin_cases i
    · exact hgeom0
    · exact hgeom1
  · intro i; fin_cases i
    · exact hord0
    · exact hord1
  · intro i; fin_cases i
    · exact hmom0
    · exact hmom1

end Sarkozy
