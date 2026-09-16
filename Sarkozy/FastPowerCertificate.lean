import Sarkozy.PowerPolynomial

/-! A finite power certificate retaining only its two terminal root bounds. -/
namespace Sarkozy.PowerChecker

private theorem lower_endpoint_log {D a x n : ℕ}
    (hD : 0 < D) (hx : 0 < x)
    (h : x ^ (n+1) ≤ a * D ^ n) :
    (n+1 : ℕ) * Real.log ((x : ℝ)/D) ≤ Real.log ((a : ℝ)/D) := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hR : (x : ℝ) ^ (n+1) ≤ (a : ℝ) * (D : ℝ) ^ n := by exact_mod_cast h
  have hp : ((x : ℝ)/D) ^ (n+1) ≤ (a : ℝ)/D := by
    rw [div_pow]
    apply (div_le_div_iff₀ (pow_pos hDR _) hDR).mpr
    simpa only [pow_succ, mul_assoc] using mul_le_mul_of_nonneg_right hR hDR.le
  have hl := Real.log_le_log (pow_pos (div_pos hxR hDR) _) hp
  simpa only [Real.log_pow] using hl

private theorem upper_endpoint_log {D b x n : ℕ}
    (hD : 0 < D) (hb : 0 < b)
    (h : b * D ^ n ≤ x ^ (n+1)) :
    Real.log ((b : ℝ)/D) ≤ (n+1 : ℕ) * Real.log ((x : ℝ)/D) := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hR : (b : ℝ) * (D : ℝ) ^ n ≤ (x : ℝ) ^ (n+1) := by exact_mod_cast h
  have hp : (b : ℝ)/D ≤ ((x : ℝ)/D) ^ (n+1) := by
    rw [div_pow]
    apply (div_le_div_iff₀ hDR (pow_pos hDR _)).mpr
    simpa only [pow_succ, mul_assoc] using mul_le_mul_of_nonneg_right hR hDR.le
  have hl := Real.log_le_log (div_pos hbR hDR) hp
  simpa only [Real.log_pow] using hl

/-- Direct integer power comparisons and the existing polynomial logarithm
comparison imply the desired real power bound. Only the two endpoints are data. -/
theorem endpoint_sound {D p q n a0 b0 lo hi : ℕ}
    (hD : 0 < D) (hq : 0 < q) (ha : 0 < a0) (hb : 0 < b0)
    (hlo : 0 < lo) (hloD : lo ≤ D) (hhi : 0 < hi) (hhiD : hi ≤ D)
    (hlower : lo ^ (n+1) ≤ a0 * D ^ n)
    (hupper : b0 * D ^ n ≤ hi ^ (n+1))
    (hcmp : p * hi * (PowerPolynomial.seriesNumerator D lo +
          PowerPolynomial.errorNumerator D lo) +
        q * lo * PowerPolynomial.errorNumerator D hi ≤
        q * lo * PowerPolynomial.seriesNumerator D hi) :
    (b0 : ℝ)/D ≤ ((a0 : ℝ)/D) ^ ((p : ℝ)/q) := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have haR : (0 : ℝ) < a0 := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b0 := by exact_mod_cast hb
  have hDQ : (0 : ℚ) < D := by exact_mod_cast hD
  have hlow := (log_bounds ((lo : ℚ)/D)
    (div_pos (by exact_mod_cast hlo) hDQ)
    ((div_le_one₀ hDQ).mpr (by exact_mod_cast hloD))).1
  have hhigh := (log_bounds ((hi : ℚ)/D)
    (div_pos (by exact_mod_cast hhi) hDQ)
    ((div_le_one₀ hDQ).mpr (by exact_mod_cast hhiD))).2
  norm_num only [Rat.cast_div, Rat.cast_natCast] at hlow hhigh
  have hleft := (mul_le_mul_of_nonneg_left hlow
    (Nat.cast_nonneg (n+1) : (0 : ℝ) ≤ (n+1 : ℕ))).trans
      (lower_endpoint_log hD hlo hlower)
  have hright := (upper_endpoint_log hD hb hupper).trans
    (mul_le_mul_of_nonneg_left hhigh
      (Nat.cast_nonneg (n+1) : (0 : ℝ) ≤ (n+1 : ℕ)))
  have hcmpQ := PowerPolynomial.log_comparison_of_nat D lo hi p q
    hD hlo hhi hq hloD hhiD hcmp
  have hcmpR : (upperLog ((hi : ℚ)/D) : ℝ) ≤
      ((p : ℝ)/q) * (lowerLog ((lo : ℚ)/D) : ℝ) := by
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_natCast] using
      (Rat.cast_le (K := ℝ)).mpr hcmpQ
  apply (Real.log_le_log_iff (div_pos hbR hDR)
    (Real.rpow_pos_of_pos (div_pos haR hDR) _)).mp
  rw [Real.log_rpow (div_pos haR hDR)]
  calc
    Real.log ((b0 : ℝ)/D) ≤ (n+1 : ℕ) * (upperLog ((hi : ℚ)/D) : ℝ) := hright
    _ ≤ (n+1 : ℕ) * (((p : ℝ)/q) * (lowerLog ((lo : ℚ)/D) : ℝ)) :=
      mul_le_mul_of_nonneg_left hcmpR (Nat.cast_nonneg _)
    _ = ((p : ℝ)/q) * ((n+1 : ℕ) * (lowerLog ((lo : ℚ)/D) : ℝ)) := by ring
    _ ≤ ((p : ℝ)/q) * Real.log ((a0 : ℝ)/D) :=
      mul_le_mul_of_nonneg_left hleft (by positivity)

/-- Initial numerators and their two terminal root bounds. -/
structure EndpointCertificate where
  a0 : ℕ
  b0 : ℕ
  low : ℕ
  high : ℕ

/-- The exact endpoint test; `n+1` is the common root degree. -/
def EndpointValid (D p q n : ℕ) (c : EndpointCertificate) : Prop :=
  0 < D ∧ 0 < q ∧ 0 < c.a0 ∧ 0 < c.b0 ∧
  0 < c.low ∧ c.low ≤ D ∧ 0 < c.high ∧ c.high ≤ D ∧
  c.low ^ (n+1) ≤ c.a0 * D ^ n ∧ c.b0 * D ^ n ≤ c.high ^ (n+1) ∧
  p * c.high * (PowerPolynomial.seriesNumerator D c.low +
      PowerPolynomial.errorNumerator D c.low) +
    q * c.low * PowerPolynomial.errorNumerator D c.high ≤
    q * c.low * PowerPolynomial.seriesNumerator D c.high

instance (D p q n : ℕ) (c : EndpointCertificate) : Decidable (EndpointValid D p q n c) := by
  unfold EndpointValid
  infer_instance

/-- Soundness of the finite endpoint check. -/
theorem endpoint_valid_sound {D p q n : ℕ} {c : EndpointCertificate}
    (hc : EndpointValid D p q n c) :
    (c.b0 : ℝ)/D ≤ ((c.a0 : ℝ)/D) ^ ((p : ℝ)/q) := by
  obtain ⟨hD,hq,ha,hb,hlo,hloD,hhi,hhiD,hlower,hupper,hcmp⟩ := hc
  exact endpoint_sound hD hq ha hb hlo hloD hhi hhiD hlower hupper hcmp

/-- A width, its multiplicity, and its certified lower power numerator. -/
structure MomentEntry where
  width : ℕ
  multiplicity : ℕ
  lower : ℕ
  certificate : EndpointCertificate

/-- Only the terminal bounds are stored; initial values have fixed scalings. -/
def MomentEntry.scaled (widthScale lowerScale width multiplicity lower low high : ℕ) : MomentEntry :=
  ⟨width, multiplicity, lower, ⟨width * widthScale, lower * lowerScale, low, high⟩⟩

end Sarkozy.PowerChecker
