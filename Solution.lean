import Sarkozy.FullTarget

/-!
# Submission statements

The general interval-moment criterion and its unconditional application to
exponent 0.75806746. Both statements are written out independently of the
Challenge module. Supporting constructions and specializations live in Sarkozy.
-/

open scoped BigOperators

namespace SarkozySubmission

/-- The general finite interval-moment criterion. The nonempty finite family
has pairwise coprime square bases greater than one. All assumptions refer to
the input alphabets and real parameters; the all-large-N conclusion is proved. -/
theorem interval_moment_bound
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (C : ι → Finset ℤ) (B : ι → ℕ) (a w : ι → ℤ → ℝ)
    (f : ι → ℝ) (α σ ρ : ℝ)
    (hB : ∀ i, 1 < B i)
    (hcop : Pairwise (fun i j => (B i).Coprime (B j)))
    (hsquare : ∀ i, ∃ s : ℕ, B i = s ^ 2)
    (hC : ∀ i, ∀ x ∈ C i, 0 ≤ x ∧ x < B i)
    (hσ : 0 < σ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hgeom : ∀ i, ∀ x ∈ C i,
      0 ≤ a i x ∧ σ ≤ w i x ∧ w i x ≤ ρ ∧ a i x + w i x ≤ 1)
    (horder : ∀ i, ∀ x ∈ C i, ∀ y ∈ C i, x ≠ y →
      (∃ z : ℤ, (B i : ℤ) ∣ (y - x - z ^ 2)) → a i x + w i x ≤ a i y)
    (hα : 0 ≤ α) (hf : ∀ i, 0 ≤ f i)
    (hmoment : ∀ i, (B i : ℝ) ^ α ≤ ∑ x ∈ C i, (w i x) ^ (f i))
    (hgap : α < ∑ i, f i) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ A : Finset ℤ,
        (∀ x ∈ A, 1 ≤ x ∧ x ≤ N) ∧
        (∀ x ∈ A, ∀ y ∈ A, ∀ z : ℤ, z ≠ 0 → y - x ≠ z ^ 2) ∧
        (N : ℝ) ^ (α - ε) ≤ A.card := by
  exact Sarkozy.interval_moment_exponent C B a w f α σ ρ hB hcop hsquare hC
    hσ hρ hρ1 hgeom horder hα hf hmoment hgap

/-- The full exponent, with every finite certificate proved in the library. -/
theorem improved_bound :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ A : Finset ℤ,
        (∀ x ∈ A, 1 ≤ x ∧ x ≤ N) ∧
        (∀ x ∈ A, ∀ y ∈ A, ∀ z : ℤ, z ≠ 0 → y - x ≠ z ^ 2) ∧
        (N : ℝ) ^ ((37903373 : ℝ) / 50000000 - ε) ≤ A.card := by
  exact Sarkozy.record_exponent

end SarkozySubmission
