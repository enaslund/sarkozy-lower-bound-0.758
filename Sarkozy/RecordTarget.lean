import Sarkozy.TwoOddTarget

/-!
# A modular interface for odd low-support certificates

Every expanded alphabet is constructed in Lean. The six prime chains and
their moments, both prime-coordinate free-digit lifts, and the actual binary
policy geometry are proved. The inputs are the two odd low supports
with their interval geometry/order/moments. The full binary certificate,
including every growth row and the fixed-depth inequality, is proved. This
interface allows alternative low supports. The actual odd certificates are
proved in the library and assembled in `Sarkozy.FullTarget`.
-/

namespace Sarkozy

open scoped BigOperators

/-- The record exponent from two unexpanded odd certificates, with the
prime chains, odd lifts and full binary certificate supplied by library proofs. -/
theorem record_exponent_of_finite_checks
    (S : (j : Fin 2) → Finset (RecordOddWord j))
    (left width : (j : Fin 2) → RecordOddWord j → ℝ)
    (hgeometry : ∀ j, ∀ a ∈ S j, 0 ≤ left j a ∧ 0 < width j a ∧ width j a < 1 ∧
      left j a + width j a ≤ 1)
    (horder : ∀ j, ∀ a ∈ S j, ∀ b ∈ S j, a ≠ b →
      (∀ i, PrimeLowRelated (recordOddPrimes j i) 3 (a i) (b i)) →
      left j a + width j a ≤ left j b)
    (hmoment : ∀ j,
      (componentBases (recordOddIndex j) : ℝ) ^ targetExponent ≤
        (recordOddRoots j ^ 3 : ℕ) *
          ∑ x ∈ S j, (width j x) ^ (componentPowers (recordOddIndex j))) :
    LowerBoundExponent targetExponent := by
  obtain ⟨C,a,w,hcan,hgeom,hordered,hbinarymoment⟩ :=
    record_binary_interval_certificate
  exact target_exponent_of_odd_low_supports S left width hgeometry horder hmoment
    C a w hcan hgeom hordered hbinarymoment

end Sarkozy
