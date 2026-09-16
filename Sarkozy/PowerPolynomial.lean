import Sarkozy.PowerChecker

/-!
# Integer polynomial checks for the logarithmic power certificates

Clearing the common denominator in the eight-term logarithm enclosure avoids
normalizing thousands of intermediate rational numbers during finite checks.
The resulting comparison uses natural-number arithmetic only; this file proves
that it implies the rational logarithm comparison used by `PowerChecker`.
-/

namespace Sarkozy.PowerPolynomial

/-- Numerator of the eight-term series at `a / D`, with common denominator
`840 * a * D^8`. The factors `840/i` are integral for `1 ≤ i ≤ 8`. -/
def seriesNumerator (D a : ℕ) : ℕ :=
  a * (840 * (D-a) * D^7 + 420 * (D-a)^2 * D^6 +
    280 * (D-a)^3 * D^5 + 210 * (D-a)^4 * D^4 +
    168 * (D-a)^5 * D^3 + 140 * (D-a)^6 * D^2 +
    120 * (D-a)^7 * D + 105 * (D-a)^8)

/-- Numerator of the logarithm remainder bound at the same denominator. -/
def errorNumerator (D a : ℕ) : ℕ := 840 * (D-a)^9

theorem series_eq (D a : ℕ) (hD : 0 < D) (ha : 0 < a) (haD : a ≤ D) :
    PowerChecker.series ((a : ℚ)/D) =
      (seriesNumerator D a : ℚ)/(840 * a * (D : ℚ)^8) := by
  have hDQ : (D : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hD
  have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ha
  simp only [seriesNumerator, Nat.cast_mul, Nat.cast_add, Nat.cast_pow,
    Nat.cast_ofNat, Nat.cast_sub haD]
  norm_num [PowerChecker.series, Finset.sum_range_succ]
  field_simp [hDQ, haQ] <;> ring

theorem error_eq (D a : ℕ) (hD : 0 < D) (ha : 0 < a) (haD : a ≤ D) :
    PowerChecker.error ((a : ℚ)/D) =
      (errorNumerator D a : ℚ)/(840 * a * (D : ℚ)^8) := by
  have hDQ : (D : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hD
  have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ha
  simp only [PowerChecker.error, errorNumerator, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, Nat.cast_sub haD]
  field_simp [hDQ, haQ] <;> ring

theorem lowerLog_eq (D a : ℕ) (hD : 0 < D) (ha : 0 < a) (haD : a ≤ D) :
    PowerChecker.lowerLog ((a : ℚ)/D) =
      -((seriesNumerator D a : ℚ) + errorNumerator D a)/(840 * a * (D : ℚ)^8) := by
  rw [PowerChecker.lowerLog, series_eq D a hD ha haD, error_eq D a hD ha haD]
  ring

theorem upperLog_eq (D a : ℕ) (hD : 0 < D) (ha : 0 < a) (haD : a ≤ D) :
    PowerChecker.upperLog ((a : ℚ)/D) =
      (-(seriesNumerator D a : ℚ) + errorNumerator D a)/(840 * a * (D : ℚ)^8) := by
  rw [PowerChecker.upperLog, series_eq D a hD ha haD, error_eq D a hD ha haD]
  ring

/-- An exact natural-number polynomial inequality suffices for the logarithm
comparison in a power certificate. This theorem performs no finite search. -/
theorem log_comparison_of_nat (D a b p q : ℕ)
    (hD : 0 < D) (ha : 0 < a) (hb : 0 < b) (hq : 0 < q)
    (haD : a ≤ D) (hbD : b ≤ D)
    (h : p*b*(seriesNumerator D a + errorNumerator D a) +
      q*a*errorNumerator D b ≤ q*a*seriesNumerator D b) :
    PowerChecker.upperLog ((b : ℚ)/D) ≤
      ((p : ℚ)/q)*PowerChecker.lowerLog ((a : ℚ)/D) := by
  have hDQ : (0 : ℚ) < D := by exact_mod_cast hD
  have haQ : (0 : ℚ) < a := by exact_mod_cast ha
  have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have hQ : (p : ℚ)*b*((seriesNumerator D a : ℚ) + errorNumerator D a) +
      (q : ℚ)*a*errorNumerator D b ≤ (q : ℚ)*a*seriesNumerator D b := by
    exact_mod_cast h
  rw [upperLog_eq D b hD hb hbD, lowerLog_eq D a hD ha haD]
  have hr : (p : ℚ)/q *
      (-((seriesNumerator D a : ℚ) + errorNumerator D a)/(840*a*(D : ℚ)^8)) =
      (-(p : ℚ)*((seriesNumerator D a : ℚ) + errorNumerator D a))/
        ((q : ℚ)*840*a*(D : ℚ)^8) := by ring
  rw [hr]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hc : (q : ℚ)*a*(-(seriesNumerator D b : ℚ) + errorNumerator D b) ≤
      -(p : ℚ)*b*((seriesNumerator D a : ℚ) + errorNumerator D a) := by
    nlinarith only [hQ]
  have hm := mul_le_mul_of_nonneg_right hc (by positivity : (0 : ℚ) ≤ 840*(D : ℚ)^8)
  convert hm using 1 <;> ring

end Sarkozy.PowerPolynomial
