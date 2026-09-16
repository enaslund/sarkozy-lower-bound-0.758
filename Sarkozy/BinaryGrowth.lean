import Sarkozy.Binary

/-!+# Exact binary moment accounting and positive-vector growth

The finite recurrence is proved by induction. There is no spectral theorem
or infinite limiting assumption in the growth certificate.
-/

namespace Sarkozy

open scoped BigOperators

/-- Distinct base-four branches have disjoint encoded digit sets. -/
theorem binaryJoin_disjoint (R : Finset ℤ) (C : ℤ → Finset ℤ)
    (hR : ∀ r ∈ R, 0 ≤ r ∧ r < 4) :
    Set.PairwiseDisjoint (↑R) (fun r => (C r).image fun x => r+4*x) := by
  intro r hr s hs hrs
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨x,hx,hxz⟩ := Finset.mem_image.mp hz
  obtain ⟨y,hy,hyz⟩ := Finset.mem_image.mp hz'
  have hrr := hR r hr
  have hss := hR s hs
  omega

/-- The parent moment is exactly the sum of the placed child moments. -/
theorem binaryJoin_moment (R : Finset ℤ) (C : ℤ → Finset ℤ)
    (w : ℤ → ℤ → ℝ) (f : ℝ) (hR : ∀ r ∈ R, 0 ≤ r ∧ r < 4) :
    ∑ x ∈ binaryJoin R C, (binaryJoinWidth w x)^f =
      ∑ r ∈ R, ∑ x ∈ C r, (w r x)^f := by
  unfold binaryJoin
  rw [Finset.sum_biUnion (binaryJoin_disjoint R C hR)]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_image (by
    intro x hx y hy he
    change r+4*x = r+4*y at he
    omega)]
  apply Finset.sum_congr rfl
  intro x hx
  rw [binaryJoin_width_eval w r x (hR r hr)]

/-- Scaling a child's widths scales its moment by the corresponding real
power. This applies equally to reflected or translated child intervals. -/
theorem binary_scaled_moment (C : Finset ℤ) (w : ℤ → ℝ) (u f : ℝ)
    (hu : 0 ≤ u) (hw : ∀ x ∈ C, 0 ≤ w x) :
    ∑ x ∈ C, (u*w x)^f = u^f * ∑ x ∈ C, (w x)^f := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  exact Real.mul_rpow hu (hw x hx)

/-- Translation and reflection preserve the exact moment, because their
residue map is injective and the inverse reconstructs the original width. -/
theorem binaryTransform_moment (C : Finset ℤ) (Q : ℤ) (reflect : Bool)
    (shift : ℤ) (w : ℤ → ℝ) (f : ℝ)
    (hC : ∀ x ∈ C, 0 ≤ x ∧ x < Q) :
    ∑ x ∈ C.image (binaryDigitTransform Q reflect shift),
      (binaryTransformWidth Q reflect shift w x)^f = ∑ x ∈ C, (w x)^f := by
  rw [Finset.sum_image (binaryDigitTransform_injective C Q reflect shift hC)]
  apply Finset.sum_congr rfl
  intro x hx
  rw [binaryTransformWidth_eval Q reflect shift w x (hC x hx)]

/-- Each singleton seed has moment at least the width of its window. -/
theorem binary_seed_moment (d f c v : ℝ) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hf : f ≤ 1) (hseed : c*v ≤ d) : c*v ≤ d^f :=
  hseed.trans (Real.self_le_rpow_of_le_one hd hd1 hf)

/-- A positive comparison vector supplies growth for any finite nonnegative
branch recurrence. The depth index starts at zero for the singleton seed. -/
theorem binary_moment_growth {S R : Type*} [Fintype R]
    (child : S → R → S) (weight : S → R → ℝ)
    (Z : ℕ → S → ℝ) (v : S → ℝ) (a c : ℝ)
    (hweight : ∀ s r, 0 ≤ weight s r) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hseed : ∀ s, c*v s ≤ Z 0 s)
    (hrow : ∀ s, a*v s ≤ ∑ r, weight s r * v (child s r))
    (hstep : ∀ n s, (∑ r, weight s r * Z n (child s r)) ≤ Z (n+1) s) :
    ∀ n s, c*a^n*v s ≤ Z n s := by
  intro n
  induction n with
  | zero => simpa using hseed
  | succ n ih =>
    intro s
    have hca : 0 ≤ c*a^n := mul_nonneg hc (pow_nonneg ha n)
    calc
      c*a^(n+1)*v s = (c*a^n)*(a*v s) := by ring
      _ ≤ (c*a^n)*(∑ r, weight s r * v (child s r)) :=
        mul_le_mul_of_nonneg_left (hrow s) hca
      _ = ∑ r, weight s r * (c*a^n*v (child s r)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        ring
      _ ≤ ∑ r, weight s r * Z n (child s r) := by
        apply Finset.sum_le_sum
        intro r hr
        exact mul_le_mul_of_nonneg_left (ih (child s r)) (hweight s r)
      _ ≤ Z (n+1) s := hstep n s

/-- The root normalization removes the comparison-vector factor. -/
theorem binary_root_growth {S R : Type*} [Fintype R]
    (child : S → R → S) (weight : S → R → ℝ)
    (Z : ℕ → S → ℝ) (v : S → ℝ) (a c : ℝ) (root : S)
    (hweight : ∀ s r, 0 ≤ weight s r) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hseed : ∀ s, c*v s ≤ Z 0 s)
    (hrow : ∀ s, a*v s ≤ ∑ r, weight s r * v (child s r))
    (hstep : ∀ n s, (∑ r, weight s r * Z n (child s r)) ≤ Z (n+1) s)
    (hroot : v root = 1) (n : ℕ) : c*a^n ≤ Z n root := by
  simpa [hroot] using
    binary_moment_growth child weight Z v a c hweight ha hc hseed hrow hstep n root

/-- The verifier's finite logarithmic depth inequality implies the required
power comparison after multiplying every final width by `θ`. -/
theorem binary_depth_log_certificate (c a θ α f : ℝ) (m : ℕ)
    (hc : 0 < c) (ha : 0 < a) (hθ : 0 < θ)
    (hlog : α*(m : ℝ)*Real.log 4 ≤ Real.log c +
      ((m-1 : ℕ) : ℝ)*Real.log a + f*Real.log θ) :
    ((4 : ℝ)^m)^α ≤ θ^f * (c*a^(m-1)) := by
  have h4 : (0 : ℝ) < 4 := by norm_num
  have hleft := Real.rpow_pos_of_pos (pow_pos h4 m) α
  have ht := Real.rpow_pos_of_pos hθ f
  have hright : 0 < θ^f * (c*a^(m-1)) :=
    mul_pos ht (mul_pos hc (pow_pos ha _))
  apply (Real.log_le_log_iff hleft hright).mp
  rw [Real.log_rpow (pow_pos h4 m), Real.log_pow,
    Real.log_mul (ne_of_gt ht) (ne_of_gt (mul_pos hc (pow_pos ha _))),
    Real.log_rpow hθ,
    Real.log_mul (ne_of_gt hc) (ne_of_gt (pow_pos ha _)), Real.log_pow]
  nlinarith

/-- A verified moment-growth lower bound and finite logarithmic depth
comparison supply the actual shrunken alphabet moment used by the CRT
criterion. -/
theorem binary_root_moment_of_log (C : Finset ℤ) (w : ℤ → ℝ)
    (c a θ α f : ℝ) (m : ℕ) (hc : 0 < c) (ha : 0 < a) (hθ : 0 < θ)
    (hw : ∀ x ∈ C, 0 ≤ w x)
    (hgrowth : c*a^(m-1) ≤ ∑ x ∈ C, (w x)^f)
    (hlog : α*(m : ℝ)*Real.log 4 ≤ Real.log c +
      ((m-1 : ℕ) : ℝ)*Real.log a + f*Real.log θ) :
    ((4 : ℝ)^m)^α ≤ ∑ x ∈ C, (θ*w x)^f := by
  rw [binary_scaled_moment C w θ f hθ.le hw]
  exact (binary_depth_log_certificate c a θ α f m hc ha hθ hlog).trans
    (mul_le_mul_of_nonneg_left hgrowth (Real.rpow_nonneg hθ.le _))

end Sarkozy
