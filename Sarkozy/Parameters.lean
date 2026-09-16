import Mathlib

/-! Exact parameters of the target construction. No large power is evaluated. -/

namespace Sarkozy

open scoped BigOperators

/-- The target exponent, exactly `0.75806746`. -/
noncomputable def targetExponent : ℝ := 37903373 / 50000000

/-- Six prime chains, two odd composite alphabets, and the binary alphabet. -/
def componentRoots : Fin 9 → ℕ := ![3, 7, 11, 31, 59, 103, 215, 437, 2]

def componentDepths : Fin 9 → ℕ := ![1, 1, 1, 1, 1, 1, 3, 3, 10000000000]

/-- The square bases, represented symbolically even for the binary component. -/
def componentBases (i : Fin 9) : ℕ := componentRoots i ^ (2 * componentDepths i)

/-- Rational moment powers, rounded down for the six chains. -/
noncomputable def componentPowers : Fin 9 → ℝ :=
  ![181945506487 / 1000000000000, 85799249226 / 1000000000000,
    107233269134 / 1000000000000, 89166212567 / 1000000000000,
    42173711274 / 1000000000000, 2397851691 / 1000000000000,
    26537312662 / 1000000000000, 67871875356 / 1000000000000,
    154942497274 / 1000000000000]

theorem componentRoots_gt_one : ∀ i, 1 < componentRoots i := by decide

theorem componentDepths_pos : ∀ i, 0 < componentDepths i := by decide

theorem componentRoots_coprime : Pairwise (fun i j =>
    (componentRoots i).Coprime (componentRoots j)) := by
  unfold Pairwise
  decide

theorem componentBases_gt_one (i : Fin 9) : 1 < componentBases i := by
  exact one_lt_pow₀ (componentRoots_gt_one i)
    (Nat.ne_of_gt (Nat.mul_pos (by decide) (componentDepths_pos i)))

theorem componentBases_coprime : Pairwise (fun i j =>
    (componentBases i).Coprime (componentBases j)) := by
  intro i j hij
  exact (componentRoots_coprime hij).pow _ _

theorem componentBases_square (i : Fin 9) : ∃ s : ℕ, componentBases i = s ^ 2 := by
  refine ⟨componentRoots i ^ componentDepths i, ?_⟩
  simp only [componentBases, ← pow_mul, Nat.mul_comm]

theorem targetExponent_nonneg : 0 ≤ targetExponent := by norm_num [targetExponent]

theorem componentPowers_nonneg : ∀ i, 0 ≤ componentPowers i := by
  intro i
  fin_cases i <;> norm_num [componentPowers]

/-- The exact contribution surplus is `0.000000025671`. -/
theorem componentPowers_surplus :
    (∑ i, componentPowers i) - targetExponent = 25671 / 1000000000000 := by
  norm_num [componentPowers, targetExponent, Fin.sum_univ_succ]

theorem componentPowers_budget : targetExponent < ∑ i, componentPowers i := by
  have := componentPowers_surplus
  norm_num at this ⊢
  linarith

end Sarkozy
