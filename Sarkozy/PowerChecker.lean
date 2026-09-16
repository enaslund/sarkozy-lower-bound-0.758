import Sarkozy.ChainMoments

/-!
# Compact rational certificates for fractional powers

Short integer square-root ladders bring numbers close to one. An eighth-order
Taylor enclosure then replaces the much longer first-order ladders. The
checker only uses exact integer and rational arithmetic.
-/

namespace Sarkozy
namespace PowerChecker

open scoped BigOperators

def series (x : ℚ) : ℚ := ∑ i ∈ Finset.range 8, (1-x)^(i+1)/(i+1)
def error (x : ℚ) : ℚ := (1-x)^9/x
def lowerLog (x : ℚ) : ℚ := -series x-error x
def upperLog (x : ℚ) : ℚ := -series x+error x

theorem log_bounds (x : ℚ) (hx : 0 < x) (hx1 : x ≤ 1) :
    (lowerLog x : ℝ) ≤ Real.log x ∧ Real.log x ≤ (upperLog x : ℝ) := by
  have hxR : (0:ℝ) < x := by exact_mod_cast hx
  have hx1R : (x:ℝ) ≤ 1 := by exact_mod_cast hx1
  have hu : 0 ≤ 1-(x:ℝ) := by linarith
  have h := Real.abs_log_sub_add_sum_range_le
    (x := 1-(x:ℝ)) (by rw [abs_of_nonneg hu]; linarith) 8
  rw [abs_of_nonneg hu, sub_sub_cancel] at h
  have hh := abs_le.mp h
  norm_num only [Nat.reduceAdd] at hh
  constructor <;>
    simp only [lowerLog, upperLog, series, error, Rat.cast_add, Rat.cast_sub,
      Rat.cast_neg, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_one,
      Rat.cast_natCast] <;> linarith

theorem lower_ladder (D a : ℕ) (tail : List ℕ) (hD : 0 < D)
    (hpos : ∀ x ∈ a::tail, 0 < x)
    (hchain : (a::tail).IsChain (fun x y => y^2 ≤ x*D)) :
    (2:ℝ)^tail.length * Real.log ((tail.getLastD a : ℝ)/D) ≤ Real.log ((a:ℝ)/D) := by
  have hDR : (0:ℝ) < D := by exact_mod_cast hD
  induction tail generalizing a with
  | nil => simp
  | cons b tail ih =>
    have hab := (List.isChain_cons_cons.mp hchain).1
    have ht := (List.isChain_cons_cons.mp hchain).2
    have hp : ∀ x ∈ b::tail, 0 < x := fun x hx => hpos x (List.mem_cons_of_mem a hx)
    have haR : (0:ℝ) < a := by exact_mod_cast hpos a (by simp)
    have hbR : (0:ℝ) < b := by exact_mod_cast hp b (by simp)
    have habR : (b:ℝ)^2 ≤ (a:ℝ)*D := by exact_mod_cast hab
    have hs : ((b:ℝ)/D)^2 ≤ (a:ℝ)/D := by
      rw [div_pow]
      apply (div_le_div_iff₀ (by positivity) hDR).mpr
      convert mul_le_mul_of_nonneg_right habR hDR.le using 1 <;> ring
    have hl := Real.log_le_log (sq_pos_of_pos (div_pos hbR hDR)) hs
    rw [Real.log_pow] at hl
    have hi := mul_le_mul_of_nonneg_left (ih b hp ht) (by norm_num : (0:ℝ) ≤ 2)
    simp only [List.length_cons, List.getLastD_cons, pow_succ, Nat.cast_ofNat] at *
    nlinarith

theorem upper_ladder (D a : ℕ) (tail : List ℕ) (hD : 0 < D)
    (hpos : ∀ x ∈ a::tail, 0 < x)
    (hchain : (a::tail).IsChain (fun x y => x*D ≤ y^2)) :
    Real.log ((a:ℝ)/D) ≤ (2:ℝ)^tail.length * Real.log ((tail.getLastD a : ℝ)/D) := by
  have hDR : (0:ℝ) < D := by exact_mod_cast hD
  induction tail generalizing a with
  | nil => simp
  | cons b tail ih =>
    have hab := (List.isChain_cons_cons.mp hchain).1
    have ht := (List.isChain_cons_cons.mp hchain).2
    have hp : ∀ x ∈ b::tail, 0 < x := fun x hx => hpos x (List.mem_cons_of_mem a hx)
    have haR : (0:ℝ) < a := by exact_mod_cast hpos a (by simp)
    have hbR : (0:ℝ) < b := by exact_mod_cast hp b (by simp)
    have habR : (a:ℝ)*D ≤ (b:ℝ)^2 := by exact_mod_cast hab
    have hs : (a:ℝ)/D ≤ ((b:ℝ)/D)^2 := by
      rw [div_pow]
      apply (div_le_div_iff₀ hDR (by positivity)).mpr
      convert mul_le_mul_of_nonneg_right habR hDR.le using 1 <;> ring
    have hl := Real.log_le_log (div_pos haR hDR) hs
    rw [Real.log_pow] at hl
    have hi := mul_le_mul_of_nonneg_left (ih b hp ht) (by norm_num : (0:ℝ) ≤ 2)
    simp only [List.length_cons, List.getLastD_cons, pow_succ, Nat.cast_ofNat] at *
    nlinarith


structure Certificate where
  a0 : ℕ
  b0 : ℕ
  lows : List ℕ
  highs : List ℕ

def loEnd (D : ℕ) (c : Certificate) : ℚ := (c.lows.getLastD c.a0 : ℚ)/D
def hiEnd (D : ℕ) (c : Certificate) : ℚ := (c.highs.getLastD c.b0 : ℚ)/D

def Valid (D : ℕ) (f : ℚ) (c : Certificate) : Prop :=
  0 < D ∧ 0 ≤ f ∧
  (∀ x ∈ c.a0::c.lows, 0 < x) ∧ (∀ x ∈ c.b0::c.highs, 0 < x) ∧
  (c.a0::c.lows).IsChain (fun x y => y^2 ≤ x*D) ∧
  (c.b0::c.highs).IsChain (fun x y => x*D ≤ y^2) ∧
  c.lows.length = c.highs.length ∧
  (0 < loEnd D c ∧ loEnd D c ≤ 1) ∧ (0 < hiEnd D c ∧ hiEnd D c ≤ 1) ∧
  upperLog (hiEnd D c) ≤ f*lowerLog (loEnd D c)

instance (D : ℕ) (f : ℚ) (c : Certificate) : Decidable (Valid D f c) := by
  unfold Valid
  infer_instance

def check (D : ℕ) (f : ℚ) (c : Certificate) : Bool := decide (Valid D f c)

/-- Soundness of the exact finite checker, including its analytic error bound. -/
theorem sound (D : ℕ) (f : ℚ) (c : Certificate) (hc : Valid D f c) :
    (c.b0:ℝ)/D ≤ ((c.a0:ℝ)/D)^(f:ℝ) := by
  obtain ⟨hD,hf,hpa,hpb,hca,hcb,hlen,hlo,hhi,hcmp⟩ := hc
  have hDR : (0:ℝ) < D := by exact_mod_cast hD
  have haR : (0:ℝ) < c.a0 := by exact_mod_cast hpa c.a0 (by simp)
  have hbR : (0:ℝ) < c.b0 := by exact_mod_cast hpb c.b0 (by simp)
  have hfR : (0:ℝ) ≤ (f:ℝ) := by exact_mod_cast hf
  have hlow : (lowerLog (loEnd D c):ℝ) ≤
      Real.log ((c.lows.getLastD c.a0:ℝ)/D) := by
    simpa only [loEnd, Rat.cast_div, Rat.cast_natCast] using (log_bounds _ hlo.1 hlo.2).1
  have hhigh : Real.log ((c.highs.getLastD c.b0:ℝ)/D) ≤
      (upperLog (hiEnd D c):ℝ) := by
    simpa only [hiEnd, Rat.cast_div, Rat.cast_natCast] using (log_bounds _ hhi.1 hhi.2).2
  have hleft := (mul_le_mul_of_nonneg_left hlow
    (by positivity : (0:ℝ) ≤ 2^c.lows.length)).trans
      (lower_ladder D c.a0 c.lows hD hpa hca)
  have hright := (upper_ladder D c.b0 c.highs hD hpb hcb).trans
    (mul_le_mul_of_nonneg_left hhigh (by positivity : (0:ℝ) ≤ 2^c.highs.length))
  rw [← hlen] at hright
  have hcmpR : (upperLog (hiEnd D c):ℝ) ≤ (f:ℝ)*(lowerLog (loEnd D c):ℝ) := by
    exact_mod_cast hcmp
  apply (Real.log_le_log_iff (div_pos hbR hDR)
    (Real.rpow_pos_of_pos (div_pos haR hDR) (f:ℝ))).mp
  rw [Real.log_rpow (div_pos haR hDR)]
  calc
    Real.log ((c.b0:ℝ)/D) ≤ 2^c.lows.length*(upperLog (hiEnd D c):ℝ) := hright
    _ ≤ 2^c.lows.length*((f:ℝ)*(lowerLog (loEnd D c):ℝ)) :=
      mul_le_mul_of_nonneg_left hcmpR (by positivity)
    _ = (f:ℝ)*(2^c.lows.length*(lowerLog (loEnd D c):ℝ)) := by ring
    _ ≤ (f:ℝ)*Real.log ((c.a0:ℝ)/D) := mul_le_mul_of_nonneg_left hleft hfR

end PowerChecker
end Sarkozy
