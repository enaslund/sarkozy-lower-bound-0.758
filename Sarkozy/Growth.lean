import Sarkozy.Asymptotic

/-! Elementary growth estimates used to turn strict finite budgets into exponents. -/

namespace Sarkozy

/-- Exponential slack absorbs any fixed polynomial loss. -/
theorem eventually_polynomial_le_geometric (c r : ℝ) (hc : 0 < c)
    (hr : 1 < r) (d : ℕ) :
    ∀ᶠ k : ℕ in Filter.atTop, c * ((k : ℝ) + 1) ^ d ≤ r ^ k := by
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt d hr).const_mul (c * 2 ^ d)
  have hsmall : ∀ᶠ k : ℕ in Filter.atTop,
      (c * 2 ^ d) * ((k : ℝ) ^ d / r ^ k) < 1 := by
    exact ht.eventually (gt_mem_nhds (show c * 2 ^ d * 0 < (1 : ℝ) by simp))
  filter_upwards [hsmall, Filter.eventually_ge_atTop 1] with k hk hk1
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hp : ((k : ℝ) + 1) ^ d ≤ (2 * (k : ℝ)) ^ d :=
    pow_le_pow_left₀ (by positivity) (by linarith) d
  have hupper : c * 2 ^ d * (k : ℝ) ^ d ≤ r ^ k := by
    rw [← mul_div_assoc] at hk
    simpa only [one_mul] using
      ((div_lt_iff₀ (pow_pos (by linarith : 0 < r) k)).mp hk).le
  calc
    c * ((k : ℝ) + 1) ^ d ≤ c * (2 * (k : ℝ)) ^ d :=
      mul_le_mul_of_nonneg_left hp hc.le
    _ = c * 2 ^ d * (k : ℝ) ^ d := by rw [mul_pow, mul_assoc]
    _ ≤ r ^ k := hupper

/-- A positive gap in the contribution exponents eventually dominates
the polynomial number of possible stopping lengths. -/
theorem eventually_moment_budget (ρ c α F : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hc : 0 < c) (hgap : α < F) (d : ℕ) :
    ∀ᶠ k : ℕ in Filter.atTop,
      c * ((k : ℝ) + 1) ^ d ≤ (ρ ^ k) ^ (α - F) := by
  have hr : 1 < ρ ^ (α - F) :=
    Real.one_lt_rpow_of_pos_of_lt_one_of_neg hρ hρ1 (sub_neg.mpr hgap)
  filter_upwards [eventually_polynomial_le_geometric c (ρ ^ (α - F)) hc hr d]
    with k hk
  simpa only [Real.rpow_pow_comm hρ.le] using hk

/-- Rounding interval ranks adds only a fixed factor to the common rank scale. -/
theorem ceiling_rank_budget (n : ℕ) (σ δ : ℝ) (hσ : 0 < σ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ((1 + n * (⌈1 / (δ * σ)⌉₊ - 1) : ℕ) : ℝ) ≤
      ((n : ℝ) + 1) * (1 / σ + 1) / δ := by
  let H : ℕ := ⌈1 / (δ * σ)⌉₊
  have hH : 1 ≤ H := by
    have : 0 < H := Nat.ceil_pos.mpr (by positivity)
    omega
  have ht : (H : ℝ) ≤ 1 / (δ * σ) + 1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ 1 / (δ * σ))).le
  have hδH : δ * (H : ℝ) ≤ 1 / σ + 1 := by
    calc
      δ * (H : ℝ) ≤ δ * (1 / (δ * σ) + 1) :=
        mul_le_mul_of_nonneg_left ht hδ.le
      _ = 1 / σ + δ := by field_simp
      _ ≤ 1 / σ + 1 := by linarith
  have htotal : 1 + n * (H - 1) ≤ (n + 1) * H := by
    have : H - 1 + 1 = H := Nat.sub_add_cancel hH
    nlinarith
  have htotal' : ((1 + n * (H - 1) : ℕ) : ℝ) ≤ ((n : ℝ) + 1) * H := by
    exact_mod_cast htotal
  apply (le_div_iff₀ hδ).mpr
  calc
    ((1 + n * (H - 1) : ℕ) : ℝ) * δ ≤ (((n : ℝ) + 1) * H) * δ :=
      mul_le_mul_of_nonneg_right htotal' hδ.le
    _ = ((n : ℝ) + 1) * (δ * H) := by ring
    _ ≤ ((n : ℝ) + 1) * (1 / σ + 1) :=
      mul_le_mul_of_nonneg_left hδH (by positivity)

/-- The algebraic contribution-budget calculation, separated from the
combinatorics which supplies the cardinality and rank estimates. -/
theorem weighted_growth_budget (M Q h δ c α F P : ℝ)
    (hM : 0 ≤ M) (hQ : 0 ≤ Q) (hh : 0 ≤ h) (hδ : 0 < δ)
    (hc : 0 < c) (hα : 0 ≤ α)
    (hcard : M ^ α ≤ Q * δ ^ F * P)
    (hbudget : c ^ α * P ≤ δ ^ (α - F))
    (hrank : h ≤ c / δ) : (M * h) ^ α ≤ Q := by
  have hb : δ ^ F * (P * c ^ α) ≤ δ ^ α := by
    calc
      δ ^ F * (P * c ^ α) = δ ^ F * (c ^ α * P) := by ring
      _ ≤ δ ^ F * δ ^ (α - F) :=
        mul_le_mul_of_nonneg_left hbudget (Real.rpow_nonneg hδ.le F)
      _ = δ ^ α := by rw [← Real.rpow_add hδ]; congr 1; ring
  have hcombined : M ^ α * c ^ α ≤ Q * δ ^ α := by
    calc
      M ^ α * c ^ α ≤ (Q * δ ^ F * P) * c ^ α :=
        mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hc.le α)
      _ = Q * (δ ^ F * (P * c ^ α)) := by ring
      _ ≤ Q * δ ^ α := mul_le_mul_of_nonneg_left hb hQ
  calc
    (M * h) ^ α ≤ (M * (c / δ)) ^ α :=
      Real.rpow_le_rpow (mul_nonneg hM hh) (mul_le_mul_of_nonneg_left hrank hM) hα
    _ = (M ^ α * c ^ α) / δ ^ α := by
      rw [Real.mul_rpow hM (div_nonneg hc.le hδ.le), Real.div_rpow hc.le hδ.le]
      ring
    _ ≤ Q := (div_le_iff₀ (Real.rpow_pos_of_pos hδ α)).mpr hcombined

end Sarkozy
