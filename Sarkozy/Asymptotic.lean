import Sarkozy.Ranked

/-! Passing from an explicit geometric family to a bound for every large integer. -/

namespace Sarkozy

/-- The usual lower-bound interpretation of `N^(α-o(1))`, stated without
introducing an extremal function or choosing an unspecified error term. -/
def LowerBoundExponent (α : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∃ A : Finset ℤ, (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧
      SquareDifferenceFree A ∧ (N : ℝ) ^ (α - ε) ≤ A.card

/-- Interpolation costs only one factor of the geometric cardinality. -/
theorem geometric_family_bound (L Q : ℕ) (hL : 1 < L)
    (α : ℝ) (hα : 0 ≤ α) (hgrowth : (L : ℝ) ^ α ≤ Q)
    (hfamily : ∀ k : ℕ, ∃ A : Finset ℤ, A.card = Q ^ k ∧
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ L ^ k) ∧ SquareDifferenceFree A)
    (N : ℕ) (hN : 0 < N) :
    ∃ A : Finset ℤ, (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧
      SquareDifferenceFree A ∧ (N : ℝ) ^ α ≤ Q * (A.card : ℝ) := by
  let k := Nat.log L N
  obtain ⟨A, hcard, hbound, hfree⟩ := hfamily k
  refine ⟨A, ?_, hfree, ?_⟩
  · intro a ha
    have hpow : L ^ k ≤ N := Nat.pow_log_le_self L (Nat.ne_of_gt hN)
    exact ⟨(hbound a ha).1, (hbound a ha).2.trans (by exact_mod_cast hpow)⟩
  · have hupper : (N : ℝ) ≤ (L : ℝ) ^ (k + 1) := by
      exact_mod_cast (Nat.lt_pow_succ_log_self hL N).le
    calc
      (N : ℝ) ^ α ≤ ((L : ℝ) ^ (k + 1)) ^ α :=
        Real.rpow_le_rpow (Nat.cast_nonneg N) hupper hα
      _ = ((L : ℝ) ^ α) ^ (k + 1) :=
        (Real.rpow_pow_comm (Nat.cast_nonneg L) α (k + 1)).symm
      _ ≤ (Q : ℝ) ^ (k + 1) :=
        pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg L) α) hgrowth _
      _ = Q * (A.card : ℝ) := by rw [hcard, Nat.cast_pow, pow_succ, mul_comm]

/-- A family on all geometric scales gives the claimed exponent for all `N`. -/
theorem geometric_family_exponent (L Q : ℕ) (hL : 1 < L)
    (α : ℝ) (hα : 0 ≤ α) (hgrowth : (L : ℝ) ^ α ≤ Q)
    (hfamily : ∀ k : ℕ, ∃ A : Finset ℤ, A.card = Q ^ k ∧
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ L ^ k) ∧ SquareDifferenceFree A) :
    LowerBoundExponent α := by
  intro ε hε
  have ht : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ ε)
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ N : ℕ in Filter.atTop, (Q : ℝ) ≤ (N : ℝ) ^ ε :=
    ht.eventually (Filter.eventually_ge_atTop (Q : ℝ))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hpos : 0 < N := by omega
  obtain ⟨A, hbound, hfree, hsize⟩ :=
    geometric_family_bound L Q hL α hα hgrowth hfamily N hpos
  refine ⟨A, hbound, hfree, ?_⟩
  have hreal : (0 : ℝ) < N := by exact_mod_cast hpos
  rw [Real.rpow_sub hreal]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hreal ε)).mpr
  exact hsize.trans (by
    have := mul_le_mul_of_nonneg_right (hN₀ N (by omega)) (Nat.cast_nonneg A.card)
    simpa [mul_comm] using this)

end Sarkozy
