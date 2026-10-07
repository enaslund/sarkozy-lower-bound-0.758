module

public import Sarkozy.BinaryRealData
public import Sarkozy.OddTarget

@[expose] public section
set_option backward.privateInPublic true

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
  ![349616982200708454170881917912074764076557979/500000000000000000000000000000000000000000000,
    1,
    809394467931618510215268351791771418191462819/1000000000000000000000000000000000000000000000,
    969163798318210016919607721111465573766834391/1000000000000000000000000000000000000000000000,
    968920243815913876773792488022890452184969079/1000000000000000000000000000000000000000000000,
    865025257737185121344044139872859039033169003/1000000000000000000000000000000000000000000000,
    479792926104558714830014310373378685857920283/500000000000000000000000000000000000000000000,
    22121266767555583012884267068241017762998171/25000000000000000000000000000000000000000000,
    349617260097008807072274893877747619883096699/500000000000000000000000000000000000000000000,
    174808605080516711349470515145044174641590177/250000000000000000000000000000000000000000000,
    401907393536425542921114511147796415109319479/500000000000000000000000000000000000000000000,
    979453448562296531046851733786740857132560121/1000000000000000000000000000000000000000000000,
    820202772234744165491749775656404571711182113/1000000000000000000000000000000000000000000000,
    40940834157294534889146230787916025354801627/50000000000000000000000000000000000000000000,
    962563210020967091750948847322876615484625967/1000000000000000000000000000000000000000000000,
    107823496154855862134891381590247039289438413/125000000000000000000000000000000000000000000,
    431041019101318594210758713259372602948802363/500000000000000000000000000000000000000000000,
    969551732588411275466380880289215947625699067/1000000000000000000000000000000000000000000000,
    172872145525928786883599045210522681594174387/200000000000000000000000000000000000000000000,
    3676398266414567668634021234277529248823811/3906250000000000000000000000000000000000000,
    188038125394125454663245843308722718150489919/200000000000000000000000000000000000000000000,
    17376606762821517346264175748080249149208057/20000000000000000000000000000000000000000000,
    887839894066534140809163333492985487226713281/1000000000000000000000000000000000000000000000,
    940248806391998397157214037558360869648518767/1000000000000000000000000000000000000000000000,
    869027069732727742301110462004275911175204511/1000000000000000000000000000000000000000000000]

noncomputable def vector (s : Fin 25) : ℝ := rationalVector s

noncomputable def growth : ℝ := 1430135321718334301514215293356149372101/500000000000000000000000000000000000000

def depth : ℕ := 100000000000000000000

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

/-- The binary base, kept symbolic: the kernel never evaluates `4^depth`. -/
theorem component_base : componentBases 8 = 4^depth := by
  have hbase : componentBases 8 = componentRoots 8 ^ (2 * componentDepths 8) :=
    componentBases.eq_1 8
  have hroot : componentRoots 8 = 2 := rfl
  have hdepth : componentDepths 8 = depth := rfl
  rw [hbase, hroot, hdepth, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num]

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
      (by decide)
      (by change (1549247890379023302829202/10000000000000000000000000 : ℝ) ≤ 1; norm_num)
      (by norm_num)
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
