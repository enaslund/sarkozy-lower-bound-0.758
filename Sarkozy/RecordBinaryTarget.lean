import Sarkozy.BinaryRealData
import Sarkozy.OddTarget

/-!
# The record binary component from its finite recursive certificate

The exact 25-state policy and positive vector are fixed. The general recursive
construction discharges all expanded-alphabet hypotheses. This interface takes
25 real-power row inequalities and one scalar logarithmic depth comparison;
`BinaryRows` and `BinaryDepth` prove them. `Sarkozy.FullTarget` uses the resulting
binary certificate in the unconditional lower bound.
-/

namespace Sarkozy
namespace RecordBinary

open scoped BigOperators

def rationalVector : Fin 25 → ℚ :=
  ![174810659971/250000000000,
    1,
    809401233457/1000000000000,
    969162871869/1000000000000,
    484458557827/500000000000,
    21625869137/25000000000,
    5997448713/6250000000,
    442427563111/500000000000,
    174810659971/250000000000,
    174810659971/250000000000,
    803818168703/1000000000000,
    195890262243/200000000000,
    410103937437/500000000000,
    818821025143/1000000000000,
    962569478709/1000000000000,
    53912284813/62500000000,
    107761255893/125000000000,
    969548463797/1000000000000,
    432184682331/500000000000,
    941150538179/1000000000000,
    940194115443/1000000000000,
    43441693439/50000000000,
    887845324227/1000000000000,
    470125862399/500000000000,
    434515077329/500000000000]

noncomputable def vector (s : Fin 25) : ℝ := rationalVector s

noncomputable def growth : ℝ := 1430118728343/500000000000

def depth : ℕ := 10000000000

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rationalVector_pos : ∀ s, 0 < rationalVector s := by decide +kernel

theorem vector_pos (s : Fin 25) : 0 < vector s := by
  exact Rat.cast_pos.mpr (rationalVector_pos s)

theorem vector_root : vector 1 = 1 := by norm_num [vector, rationalVector]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rational_seed_bound : ∀ s, (1/4 : ℚ)*rationalVector s ≤
    rationalPolicy.hi s (rationalPolicy.seed s)-rationalPolicy.lo s (rationalPolicy.seed s) := by
  decide +kernel

theorem seed_bound (s : Fin 25) : (1/4 : ℝ)*vector s ≤
    policy.hi s (policy.seed s)-policy.lo s (policy.seed s) := by
  change (1/4 : ℝ)*(rationalVector s : ℝ) ≤
    (rationalPolicy.hi s (rationalPolicy.seed s) : ℝ) -
    (rationalPolicy.lo s (rationalPolicy.seed s) : ℝ)
  have h : ((1/4*rationalVector s : ℚ) : ℝ) ≤
      ((rationalPolicy.hi s (rationalPolicy.seed s)-
        rationalPolicy.lo s (rationalPolicy.seed s) : ℚ) : ℝ) :=
    Rat.cast_le.mpr (rational_seed_bound s)
  norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_sub] at h
  exact h

/-- Exactly the 25 growth-row inequalities checked by the numerical certificate. -/
def Rows : Prop := ∀ s, growth*vector s ≤
  ∑ r ∈ policy.branches s, (policy.scale s r)^(componentPowers 8)*vector (policy.child s r)

/-- The fixed-depth comparison, with the deliberately weakened initialization
constant 1/4 instead of the largest certified constant. -/
def DepthCondition : Prop :=
  targetExponent*(depth : ℝ)*Real.log 4 ≤ Real.log (1/4 : ℝ) +
    ((depth-1 : ℕ) : ℝ)*Real.log growth - (componentPowers 8)*Real.log 2

theorem component_base : componentBases 8 = 4^depth := by
  unfold componentBases
  rw [pow_mul]
  exact congrArg₂ (fun b n : ℕ => b^n) (by rfl) (by rfl)

theorem component_base_int : (componentBases 8 : ℤ) = (4 : ℤ)^depth := by
  exact_mod_cast component_base

theorem component_base_real : (componentBases 8 : ℝ) = (4 : ℝ)^depth := by
  exact_mod_cast component_base

/-- The full binary alphabet is constructed from the actual finite policy.
No canonical digits, ordering, window validity, or moment-growth assertion is
supplied as an expanded-alphabet hypothesis. -/
theorem interval_certificate (hrows : Rows) (hdepth : DepthCondition) :
    ∃ (C : Finset ℤ) (start width : ℤ → ℝ),
      (∀ x ∈ C, 0 ≤ x ∧ x < componentBases 8) ∧
      (∀ x ∈ C, 0 ≤ start x ∧ 0 < width x ∧ width x < 1 ∧
        start x+width x ≤ 1) ∧
      IntervalOrderedModulo C (componentBases 8) start width ∧
      (componentBases 8 : ℝ)^targetExponent ≤
        ∑ x ∈ C, (width x)^(componentPowers 8) := by
  obtain ⟨C,start,width,σ,hσ,hcan,hgeom,horder,hmoment⟩ :=
    BinaryAlphabet.root_interval_certificate policy policy_valid
      (componentPowers 8) (1/4) growth targetExponent vector 1 depth
      (by decide) (by change (154942497274/1000000000000 : ℝ) ≤ 1; norm_num) (by norm_num)
      (by norm_num [growth]) vector_root seed_bound hrows hdepth
  refine ⟨C,start,width,?_,?_,?_,?_⟩
  · simpa only [component_base_int] using hcan
  · intro x hx
    obtain ⟨ha,hwlo,hwhi,hend⟩ := hgeom x hx
    exact ⟨ha,hσ.trans_le hwlo,by linarith,hend⟩
  · simpa only [component_base_int] using horder
  · simpa only [component_base_real] using hmoment

end RecordBinary
end Sarkozy
