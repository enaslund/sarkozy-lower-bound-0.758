module

public import Mathlib

@[expose] public section
set_option backward.privateInPublic true

/-! Exact parameters of the target construction. No large power is evaluated. -/

namespace Sarkozy

open scoped BigOperators

/-- The target exponent, exactly `0.7580758318008816`. -/
noncomputable def targetExponent : ℝ := 473797394875551 / 625000000000000

/-- Six prime chains, two odd composite alphabets, and the binary alphabet.
The `(19,23)` alphabet has three restricted digits at `19` and two at `23`,
so its square base is `(19^3 * 23^2)^2 = 3628411^2`. -/
def componentRoots : Fin 9 → ℕ := ![3, 7, 11, 31, 59, 103, 215, 3628411, 2]

def componentDepths : Fin 9 → ℕ := ![1, 1, 1, 1, 1, 1, 3, 1, 100000000000000000000]

/-- The square bases, represented symbolically even for the binary component. -/
def componentBases (i : Fin 9) : ℕ := componentRoots i ^ (2 * componentDepths i)

/-- Exact rational contributions with 25 decimals. -/
noncomputable def componentPowers : Fin 9 → ℝ :=
  ![1819189685063644313459576 / 10000000000000000000000000,
    857695922261077385453455 / 10000000000000000000000000,
    1072043074619092931875010 / 10000000000000000000000000,
    891366647927413831505830 / 10000000000000000000000000,
    421426390460550181119771 / 10000000000000000000000000,
    23654891206769647316637 / 10000000000000000000000000,
    264983230432418544045862 / 10000000000000000000000000,
    681150585658841330427119 / 10000000000000000000000000,
    1549247890379023302829202 / 10000000000000000000000000]

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

/-- The exact contribution surplus is `15468032462 / 10^25`. -/
theorem componentPowers_surplus :
    (∑ i, componentPowers i) - targetExponent =
      15468032462 / 10000000000000000000000000 := by
  norm_num [componentPowers, targetExponent, Fin.sum_univ_succ]

theorem componentPowers_budget : targetExponent < ∑ i, componentPowers i := by
  have := componentPowers_surplus
  norm_num at this ⊢
  linarith

end Sarkozy
