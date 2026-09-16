import Sarkozy.Certificate

/-!
# A completely discharged asymptotic example

The six digits congruent to `0` or `1` modulo three, taken modulo nine, have
ranks zero or one. Every hypothesis is proved in Lean, including the finite
modular check and the integer comparison `18^3 ≤ 6^5`.
-/

namespace Sarkozy

/-- Six digits in square base nine, with two possible rank values. -/
def sixDigits : Finset ℤ := {0, 1, 3, 4, 6, 7}

theorem sixDigits_canonical : ∀ x ∈ sixDigits, 0 ≤ x ∧ x < (9 : ℤ) := by
  norm_num [sixDigits]

theorem sixDigits_rank_bounds : ∀ x ∈ sixDigits, 0 ≤ x % 3 ∧ x % 3 < (2 : ℤ) := by
  norm_num [sixDigits]

/-- The only square residues modulo nine are zero, one, four, and seven.
The finite computation uses ordinary kernel-reduced `decide`. -/
theorem square_residues_nine : ∀ z : ZMod 9,
    z ^ 2 = 0 ∨ z ^ 2 = 1 ∨ z ^ 2 = 4 ∨ z ^ 2 = 7 := by decide

/-- All nontrivial modular square edges among the six digits go from rank zero
to rank one. -/
theorem sixDigits_ranked : RankedModulo sixDigits 9 (fun x => x % 3) := by
  intro x hx y hy hxy hsquare
  simp only [sixDigits, Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact (hxy rfl).elim
  all_goals try norm_num
  all_goals obtain ⟨z,hz⟩ := hsquare
  all_goals have hcast := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 9).mpr hz
  all_goals push_cast at hcast
  all_goals rcases square_residues_nine (z : ZMod 9) with h | h | h | h
  all_goals norm_num [h] at hcast
  all_goals exact absurd hcast (by decide)

/-- A fully certified construction of `6^k` integers in `[1,18^k]`. -/
theorem six_power_word_realization (k : ℕ) :
    ∃ A : Finset ℤ, A.card = 6 ^ k ∧
      (∀ x ∈ A, 1 ≤ x ∧ x ≤ (18 : ℤ) ^ k) ∧ SquareDifferenceFree A := by
  have h := ranked_word_realization sixDigits 9 2 (fun x => x % 3)
    (by norm_num) (by norm_num) ⟨3, by norm_num⟩ sixDigits_canonical
    sixDigits_rank_bounds sixDigits_ranked k
  simpa [sixDigits] using h

/-- An unconditional asymptotic example. For every `ε>0`, all sufficiently
large `N` admit a square-difference-free subset of `[1,N]` of size at least
`N^(3/5-ε)`. This is an illustrative exponent, not the project's target bound. -/
theorem exponent_three_fifths : LowerBoundExponent ((3 : ℝ) / 5) := by
  apply ranked_alphabet_rational_exponent sixDigits 9 2 (fun x => x % 3)
    (by norm_num) (by norm_num) ⟨3, by norm_num⟩ sixDigits_canonical
    sixDigits_rank_bounds sixDigits_ranked 3 5 (by norm_num)
  norm_num [sixDigits]

end Sarkozy
