import Sarkozy.Words
import Sarkozy.CRT
import Sarkozy.Asymptotic

/-!
# A finite certificate for an asymptotic exponent

The certificate consists of a finite ranked alphabet in a square base and
one integer power inequality. No asymptotic statement is a hypothesis.
The interval-moment argument applies this general criterion to the project's
concrete witnesses. `Sarkozy.FullTarget` assembles the unconditional target bound.
-/

namespace Sarkozy

/-- An integer power comparison suffices to check a rational exponent. -/
theorem rpow_le_of_power_certificate (L Q p q : ℕ) (hq : 0 < q)
    (h : L ^ p ≤ Q ^ q) : (L : ℝ) ^ ((p : ℝ) / q) ≤ Q := by
  apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg (Nat.cast_nonneg L) _)
    (Nat.cast_nonneg Q) (show (0 : ℝ) < (q : ℝ) by exact_mod_cast hq)).mp
  rw [← Real.rpow_mul (Nat.cast_nonneg L),
    div_mul_cancel₀ _ (by exact_mod_cast (Nat.ne_of_gt hq)),
    Real.rpow_natCast, Real.rpow_natCast]
  exact_mod_cast h

/-- A finite square-base ranked alphabet gives an exponent at every large `N`.
The cardinality comparison is the only numerical growth hypothesis. -/
theorem ranked_alphabet_exponent (C : Finset ℤ) (B h : ℕ) (r : ℤ → ℤ)
    (hB : 1 < B) (hh : 0 < h) (hsquare : ∃ s : ℕ, B = s ^ 2)
    (hC : ∀ x ∈ C, 0 ≤ x ∧ x < B)
    (hr : ∀ x ∈ C, 0 ≤ r x ∧ r x < h) (hCr : RankedModulo C B r)
    (α : ℝ) (hα : 0 ≤ α) (hgrowth : ((B * h : ℕ) : ℝ) ^ α ≤ C.card) :
    LowerBoundExponent α := by
  apply geometric_family_exponent (B * h) C.card (by nlinarith) α hα hgrowth
  intro k
  obtain ⟨s, hs⟩ := hsquare
  obtain ⟨A,hcard,hbound,hfree⟩ := ranked_word_realization C B h r
    (by exact_mod_cast (show 0 < B by omega)) (by exact_mod_cast hh)
    ⟨(s : ℤ), by exact_mod_cast hs⟩ hC hr hCr k
  exact ⟨A, hcard, by simpa only [Nat.cast_pow, Nat.cast_mul] using hbound, hfree⟩

/-- All hypotheses of this rational-exponent criterion concern finite data. -/
theorem ranked_alphabet_rational_exponent (C : Finset ℤ) (B h : ℕ) (r : ℤ → ℤ)
    (hB : 1 < B) (hh : 0 < h) (hsquare : ∃ s : ℕ, B = s ^ 2)
    (hC : ∀ x ∈ C, 0 ≤ x ∧ x < B)
    (hr : ∀ x ∈ C, 0 ≤ r x ∧ r x < h) (hCr : RankedModulo C B r)
    (p q : ℕ) (hq : 0 < q) (hsize : (B * h) ^ p ≤ C.card ^ q) :
    LowerBoundExponent ((p : ℝ) / q) := by
  exact ranked_alphabet_exponent C B h r hB hh hsquare hC hr hCr _
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (rpow_le_of_power_certificate (B * h) C.card p q hq hsize)

open scoped BigOperators

/-- Combining finite local certificates by CRT before word lifting. -/
theorem crt_alphabet_exponent {ι : Type*} [Fintype ι]
    (C : ι → Finset ℤ) (M K : ι → ℕ) (r : ι → ℤ → ℤ)
    (hM : ∀ i, 0 < M i) (hprod : 1 < ∏ i, M i)
    (hcop : Pairwise (fun i j => (M i).Coprime (M j)))
    (hsquare : ∀ i, ∃ s : ℕ, M i = s ^ 2)
    (hC : ∀ i, ∀ x ∈ C i, 0 ≤ x ∧ x < M i)
    (hr : ∀ i, ∀ x ∈ C i, 0 ≤ r i x ∧ r i x ≤ K i)
    (hranked : ∀ i, RankedModulo (C i) (M i) (r i))
    (α : ℝ) (hα : 0 ≤ α)
    (hsize : (((∏ i, M i) * (1 + ∑ i, K i) : ℕ) : ℝ) ^ α ≤
      (∏ i, (C i).card : ℕ)) : LowerBoundExponent α := by
  classical
  have hs : ∃ s : ℕ, (∏ i, M i) = s ^ 2 := by
    choose s hs using hsquare
    exact ⟨∏ i, s i, by simp only [hs, Finset.prod_pow]⟩
  refine ranked_alphabet_exponent (crtResidueSet C M hM hcop)
    (∏ i, M i) (1 + ∑ i, K i) (crtRank M r) hprod (by omega) hs
    (crtResidueSet_canonical C M hM hcop) ?_
    (crtResidueSet_ranked C M r hM hcop hC hranked) α hα ?_
  · intro x hx
    have hb := crtRank_bounds C M r (fun i => (K i : ℤ)) hM hcop hC hr hx
    constructor
    · exact hb.1
    · push_cast
      linarith [hb.2]
  · simpa only [crtResidueSet_card C M hM hcop hC] using hsize

/-- Rational exponents can be checked with an integer power comparison. -/
theorem crt_certificate_exponent {ι : Type*} [Fintype ι]
    (C : ι → Finset ℤ) (M K : ι → ℕ) (r : ι → ℤ → ℤ)
    (hM : ∀ i, 0 < M i) (hprod : 1 < ∏ i, M i)
    (hcop : Pairwise (fun i j => (M i).Coprime (M j)))
    (hsquare : ∀ i, ∃ s : ℕ, M i = s ^ 2)
    (hC : ∀ i, ∀ x ∈ C i, 0 ≤ x ∧ x < M i)
    (hr : ∀ i, ∀ x ∈ C i, 0 ≤ r i x ∧ r i x ≤ K i)
    (hranked : ∀ i, RankedModulo (C i) (M i) (r i))
    (p q : ℕ) (hq : 0 < q)
    (hsize : ((∏ i, M i) * (1 + ∑ i, K i)) ^ p ≤ (∏ i, (C i).card) ^ q) :
    LowerBoundExponent ((p : ℝ) / q) := by
  exact crt_alphabet_exponent C M K r hM hprod hcop hsquare hC hr hranked _
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (rpow_le_of_power_certificate _ _ p q hq hsize)

end Sarkozy
