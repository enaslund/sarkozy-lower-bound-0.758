import Sarkozy.Words

/-!
# Converting separated intervals into integer ranks

An interval starts at `a x` and has width `w x`. Modular square differences
force the first interval to end before the second starts. A common lower width
bound `δ` turns their left endpoints into bounded integer ranks by rounding down
after division by `δ`.
-/

namespace Sarkozy

/-- Modular square differences order the associated intervals from left to right. -/
def IntervalOrderedModulo (C : Finset ℤ) (M : ℤ) (a w : ℤ → ℝ) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
    (∃ z : ℤ, M ∣ (y - x - z ^ 2)) → a x + w x ≤ a y

/-- Round an interval's starting point down in units of the minimum width. -/
noncomputable def intervalRank (δ : ℝ) (a : ℤ → ℝ) (x : ℤ) : ℤ :=
  ⌊a x / δ⌋

/-- Positive interval widths force strict increases of the rounded rank. -/
theorem intervalRank_ranked (C : Finset ℤ) (M : ℤ) (a w : ℤ → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hw : ∀ x ∈ C, δ ≤ w x)
    (horder : IntervalOrderedModulo C M a w) :
    RankedModulo C M (intervalRank δ a) := by
  intro x hx y hy hxy hsquare
  have hgap : a x + δ ≤ a y := by
    have := horder x hx y hy hxy hsquare
    linarith [hw x hx]
  have hdiv : a x / δ + 1 ≤ a y / δ := by
    simpa [add_div, ne_of_gt hδ] using div_le_div_of_nonneg_right hgap (le_of_lt hδ)
  have hfloor := Int.floor_mono hdiv
  rw [Int.floor_add_one] at hfloor
  dsimp [intervalRank]
  omega

/-- Intervals lying inside the unit interval give ranks below `ceil(1/δ)`. -/
theorem intervalRank_bounds (C : Finset ℤ) (a w : ℤ → ℝ) (δ : ℝ)
    (hδ : 0 < δ)
    (hgeometry : ∀ x ∈ C, 0 ≤ a x ∧ δ ≤ w x ∧ a x + w x ≤ 1) :
    ∀ x ∈ C, 0 ≤ intervalRank δ a x ∧ intervalRank δ a x < ⌈1 / δ⌉ := by
  intro x hx
  obtain ⟨ha,hw,hend⟩ := hgeometry x hx
  dsimp [intervalRank]
  constructor
  · exact Int.floor_nonneg.mpr (div_nonneg ha (le_of_lt hδ))
  · apply Int.floor_lt.mpr
    have ha1 : a x < 1 := by linarith
    exact lt_of_lt_of_le ((div_lt_div_iff_of_pos_right hδ).mpr ha1) (Int.le_ceil _)

/-- An explicit finite interval certificate produces a ranked alphabet. -/
theorem interval_rank_certificate (C : Finset ℤ) (M : ℤ) (a w : ℤ → ℝ) (δ : ℝ)
    (hδ : 0 < δ)
    (hgeometry : ∀ x ∈ C, 0 ≤ a x ∧ δ ≤ w x ∧ a x + w x ≤ 1)
    (horder : IntervalOrderedModulo C M a w) :
    0 < (⌈1 / δ⌉ : ℤ) ∧
    (∀ x ∈ C, 0 ≤ intervalRank δ a x ∧ intervalRank δ a x < ⌈1 / δ⌉) ∧
    RankedModulo C M (intervalRank δ a) := by
  refine ⟨Int.ceil_pos.mpr (one_div_pos.mpr hδ),
    intervalRank_bounds C a w δ hδ hgeometry, ?_⟩
  exact intervalRank_ranked C M a w δ hδ (fun x hx => (hgeometry x hx).2.1) horder

/-- A finite interval certificate at square modulus gives arbitrarily long
square-difference-free integer sets by the fully proved word construction. -/
theorem interval_word_realization (C : Finset ℤ) (B : ℤ) (a w : ℤ → ℝ) (δ : ℝ)
    (hB : 0 < B) (hsquare : ∃ s : ℤ, B = s ^ 2)
    (hC : ∀ x ∈ C, 0 ≤ x ∧ x < B) (hδ : 0 < δ)
    (hgeometry : ∀ x ∈ C, 0 ≤ a x ∧ δ ≤ w x ∧ a x + w x ≤ 1)
    (horder : IntervalOrderedModulo C B a w) (k : ℕ) :
    ∃ A : Finset ℤ, A.card = C.card ^ k ∧
      (∀ x ∈ A, 1 ≤ x ∧ x ≤ (B * ⌈1 / δ⌉) ^ k) ∧ SquareDifferenceFree A := by
  obtain ⟨hh,hr,hCr⟩ := interval_rank_certificate C B a w δ hδ hgeometry horder
  exact ranked_word_realization C B ⌈1 / δ⌉ (intervalRank δ a)
    hB hh hsquare hC hr hCr k

/-- Starting point of an interval obtained by putting a tail interval inside the
interval attached to the low digit. -/
noncomputable def joinIntervalStart (B : ℤ) (a w b : ℤ → ℝ) (x : ℤ) : ℝ :=
  a (x % B) + w (x % B) * b (x / B)

/-- Width of an affine-nested interval. -/
noncomputable def joinIntervalWidth (B : ℤ) (w v : ℤ → ℝ) (x : ℤ) : ℝ :=
  w (x % B) * v (x / B)

theorem joinIntervalStart_eval (B : ℤ) (a w b : ℤ → ℝ) (x y : ℤ)
    (hB : 0 < B) (hx : 0 ≤ x ∧ x < B) :
    joinIntervalStart B a w b (joinDigit B (x,y)) = a x + w x * b y := by
  simp [joinIntervalStart, joinDigit, Int.add_mul_ediv_left _ _ (ne_of_gt hB),
    Int.ediv_eq_zero_of_lt hx.1 hx.2, Int.emod_eq_of_lt hx.1 hx.2]

theorem joinIntervalWidth_eval (B : ℤ) (w v : ℤ → ℝ) (x y : ℤ)
    (hB : 0 < B) (hx : 0 ≤ x ∧ x < B) :
    joinIntervalWidth B w v (joinDigit B (x,y)) = w x * v y := by
  simp [joinIntervalWidth, joinDigit, Int.add_mul_ediv_left _ _ (ne_of_gt hB),
    Int.ediv_eq_zero_of_lt hx.1 hx.2, Int.emod_eq_of_lt hx.1 hx.2]

/-- Affine nesting preserves the modular ordering of intervals. The resulting
width is the product of the digit widths, so one may subsequently retain any
collection of words with sufficiently large width. -/
theorem interval_join (C D : Finset ℤ) (B P : ℤ) (a w b v : ℤ → ℝ)
    (hB : 0 < B) (hsquare : ∃ s : ℤ, B = s ^ 2)
    (hC : ∀ x ∈ C, 0 ≤ x ∧ x < B)
    (hD : ∀ x ∈ D, 0 ≤ x ∧ x < P)
    (hgeomC : ∀ x ∈ C, 0 ≤ a x ∧ 0 < w x ∧ a x + w x ≤ 1)
    (hgeomD : ∀ x ∈ D, 0 ≤ b x ∧ 0 < v x ∧ b x + v x ≤ 1)
    (horderC : IntervalOrderedModulo C B a w)
    (horderD : IntervalOrderedModulo D P b v) :
    let E := (C ×ˢ D).image (joinDigit B)
    E.card = C.card * D.card ∧
    (∀ x ∈ E, 0 ≤ x ∧ x < B * P) ∧
    (∀ x ∈ E, 0 ≤ joinIntervalStart B a w b x ∧
      0 < joinIntervalWidth B w v x ∧
      joinIntervalStart B a w b x + joinIntervalWidth B w v x ≤ 1) ∧
    IntervalOrderedModulo E (B * P) (joinIntervalStart B a w b)
      (joinIntervalWidth B w v) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_iff.mpr (joinDigit_injOn C D B hB hC), Finset.card_product]
  · intro z hz
    obtain ⟨⟨x,y⟩, hxy, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
    have hxc := hC x hx
    have hyc := hD y hy
    dsimp [joinDigit]
    constructor
    · exact add_nonneg hxc.1 (mul_nonneg (le_of_lt hB) hyc.1)
    · have hy1 : y ≤ P - 1 := by omega
      nlinarith [mul_le_mul_of_nonneg_left hy1 (le_of_lt hB)]
  · intro z hz
    obtain ⟨⟨x,y⟩, hxy, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
    rw [joinIntervalStart_eval B a w b x y hB (hC x hx),
      joinIntervalWidth_eval B w v x y hB (hC x hx)]
    obtain ⟨ha,hw,hend⟩ := hgeomC x hx
    obtain ⟨hb,hv,hend'⟩ := hgeomD y hy
    refine ⟨add_nonneg ha (mul_nonneg (le_of_lt hw) hb), mul_pos hw hv, ?_⟩
    nlinarith [mul_le_mul_of_nonneg_left hend' (le_of_lt hw)]
  · intro i hi j hj hij hs
    obtain ⟨⟨x,u⟩, hxu, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨⟨y,z⟩, hyz, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hx,hu⟩ := Finset.mem_product.mp hxu
    obtain ⟨hy,hz⟩ := Finset.mem_product.mp hyz
    rw [joinIntervalStart_eval B a w b x u hB (hC x hx),
      joinIntervalWidth_eval B w v x u hB (hC x hx),
      joinIntervalStart_eval B a w b y z hB (hC y hy)]
    obtain ⟨q,t,ht⟩ := hs
    dsimp [joinDigit] at hij ht
    by_cases hxy : x = y
    · subst y
      have huz : u ≠ z := by intro he; exact hij (by rw [he])
      obtain ⟨s,hs⟩ := hsquare
      have hroot : s ∣ q := by
        apply (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp
        refine ⟨z - u - P * t, ?_⟩
        nlinarith [ht]
      obtain ⟨q, rfl⟩ := hroot
      have htail : P ∣ z - u - q ^ 2 := by
        refine ⟨t, ?_⟩
        have heq : B * (z - u - q ^ 2) = B * (P * t) := by
          rw [hs] at ht ⊢
          nlinarith [ht]
        exact (mul_left_cancel₀ (ne_of_gt hB) heq)
      have hord := horderD u hu z hz huz ⟨q, htail⟩
      have hw := (hgeomC x hx).2.1
      nlinarith [mul_le_mul_of_nonneg_left hord (le_of_lt hw)]
    · have hlow : B ∣ y - x - q ^ 2 := by
        refine ⟨P * t - z + u, ?_⟩
        nlinarith [ht]
      have hord := horderC x hx y hy hxy ⟨q, hlow⟩
      have hgu := hgeomD u hu
      have hgz := hgeomD z hz
      have hw := (hgeomC x hx).2.1
      have hwy := (hgeomC y hy).2.1
      have hleft := mul_le_mul_of_nonneg_left hgu.2.2 (le_of_lt hw)
      have hright := mul_nonneg (le_of_lt hwy) hgz.1
      nlinarith

/-- Restricting an interval construction to a finite collection of sufficiently
wide words gives an explicit finite ranked certificate. -/
theorem interval_subset_rank_certificate (C D : Finset ℤ) (M : ℤ)
    (a w : ℤ → ℝ) (δ : ℝ) (hDC : D ⊆ C) (hδ : 0 < δ)
    (hgeometry : ∀ x ∈ C, 0 ≤ a x ∧ a x + w x ≤ 1)
    (hwidth : ∀ x ∈ D, δ ≤ w x)
    (horder : IntervalOrderedModulo C M a w) :
    0 < (⌈1 / δ⌉ : ℤ) ∧
    (∀ x ∈ D, 0 ≤ intervalRank δ a x ∧ intervalRank δ a x < ⌈1 / δ⌉) ∧
    RankedModulo D M (intervalRank δ a) := by
  apply interval_rank_certificate D M a w δ hδ
  · intro x hx
    have hxC := hDC hx
    exact ⟨(hgeometry x hxC).1, hwidth x hx, (hgeometry x hxC).2⟩
  · intro x hx y hy hxy hsquare
    exact horder x (hDC hx) y (hDC hy) hxy hsquare

/-- Canonical integers encoding all fixed-length words over `C`. -/
def intervalWords (C : Finset ℤ) (B : ℤ) : ℕ → Finset ℤ
  | 0 => {0}
  | k + 1 => (C ×ˢ intervalWords C B k).image (joinDigit B)

/-- Starting point of the affine interval attached to a word. -/
noncomputable def wordIntervalStart (B : ℤ) (a w : ℤ → ℝ) : ℕ → ℤ → ℝ
  | 0 => fun _ => 0
  | k + 1 => joinIntervalStart B a w (wordIntervalStart B a w k)

/-- The interval width of a word is the product of its digit widths. -/
noncomputable def wordIntervalWidth (B : ℤ) (w : ℤ → ℝ) : ℕ → ℤ → ℝ
  | 0 => fun _ => 1
  | k + 1 => joinIntervalWidth B w (wordIntervalWidth B w k)

/-- Affine nesting gives interval certificates for all fixed-length words,
retaining the varying width of every individual word. -/
theorem interval_words (C : Finset ℤ) (B : ℤ) (a w : ℤ → ℝ)
    (hB : 0 < B) (hsquare : ∃ s : ℤ, B = s ^ 2)
    (hC : ∀ x ∈ C, 0 ≤ x ∧ x < B)
    (hgeom : ∀ x ∈ C, 0 ≤ a x ∧ 0 < w x ∧ a x + w x ≤ 1)
    (horder : IntervalOrderedModulo C B a w) (k : ℕ) :
    (intervalWords C B k).card = C.card ^ k ∧
    (∀ x ∈ intervalWords C B k, 0 ≤ x ∧ x < B ^ k) ∧
    (∀ x ∈ intervalWords C B k, 0 ≤ wordIntervalStart B a w k x ∧
      0 < wordIntervalWidth B w k x ∧
      wordIntervalStart B a w k x + wordIntervalWidth B w k x ≤ 1) ∧
    IntervalOrderedModulo (intervalWords C B k) (B ^ k)
      (wordIntervalStart B a w k) (wordIntervalWidth B w k) := by
  induction k with
  | zero =>
    refine ⟨by simp [intervalWords], ?_, ?_, ?_⟩
    · simp [intervalWords]
    · simp [intervalWords, wordIntervalStart, wordIntervalWidth]
    · intro x hx y hy hxy _
      simp only [intervalWords, Finset.mem_singleton] at hx hy
      exact (hxy (hx.trans hy.symm)).elim
  | succ k ih =>
    have hj := interval_join C (intervalWords C B k) B (B ^ k) a w
      (wordIntervalStart B a w k) (wordIntervalWidth B w k) hB hsquare
      hC ih.2.1 hgeom ih.2.2.1 horder ih.2.2.2
    simpa only [intervalWords, wordIntervalStart, wordIntervalWidth, pow_succ', ih.1] using hj

/-- Uniform lower and upper digit widths give the corresponding power bounds
for every fixed-length word, while retaining the exact individual widths. -/
theorem wordIntervalWidth_bounds (C : Finset ℤ) (B : ℤ) (w : ℤ → ℝ)
    (hB : 0 < B) (hC : ∀ x ∈ C, 0 ≤ x ∧ x < B)
    (lo hi : ℝ) (hlo : 0 ≤ lo) (hw : ∀ x ∈ C, lo ≤ w x ∧ w x ≤ hi)
    (k : ℕ) :
    ∀ x ∈ intervalWords C B k,
      lo ^ k ≤ wordIntervalWidth B w k x ∧ wordIntervalWidth B w k x ≤ hi ^ k := by
  induction k with
  | zero => simp [wordIntervalWidth]
  | succ k ih =>
    intro z hz
    obtain ⟨⟨x,y⟩, hxy, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
    simp only [wordIntervalWidth]
    rw [joinIntervalWidth_eval B w (wordIntervalWidth B w k) x y hB (hC x hx)]
    have hxw := hw x hx
    have hyw := ih y hy
    have hw0 : 0 ≤ w x := hlo.trans hxw.1
    have hhi0 : 0 ≤ hi := hw0.trans hxw.2
    have hyw0 : 0 ≤ wordIntervalWidth B w k y := (pow_nonneg hlo k).trans hyw.1
    constructor
    · simpa only [pow_succ'] using mul_le_mul hxw.1 hyw.1 (pow_nonneg hlo k) hw0
    · simpa only [pow_succ'] using mul_le_mul hxw.2 hyw.2 hyw0 hhi0

/-- Nonnegative digit widths give nonnegative widths to all words. -/
theorem wordIntervalWidth_nonneg (C : Finset ℤ) (B : ℤ) (w : ℤ → ℝ)
    (hB : 0 < B) (hC : ∀ x ∈ C, 0 ≤ x ∧ x < B)
    (hw : ∀ x ∈ C, 0 ≤ w x) (k : ℕ) :
    ∀ x ∈ intervalWords C B k, 0 ≤ wordIntervalWidth B w k x := by
  induction k with
  | zero => simp [wordIntervalWidth]
  | succ k ih =>
    intro z hz
    obtain ⟨⟨x,y⟩, hxy, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
    simp only [wordIntervalWidth]
    rw [joinIntervalWidth_eval B w (wordIntervalWidth B w k) x y hB (hC x hx)]
    exact mul_nonneg (hw x hx) (ih y hy)

/-- Moment factorization also holds when only a subset of the possible tails
is extended by one digit. -/
theorem children_moment (C D : Finset ℤ) (B : ℤ) (w : ℤ → ℝ)
    (hB : 0 < B) (hC : ∀ x ∈ C, 0 ≤ x ∧ x < B)
    (hw : ∀ x ∈ C, 0 ≤ w x) (f : ℝ) (k : ℕ)
    (hD : D ⊆ intervalWords C B k) :
    ∑ z ∈ (C ×ˢ D).image (joinDigit B), (wordIntervalWidth B w (k + 1) z) ^ f =
      (∑ x ∈ C, (w x) ^ f) * ∑ y ∈ D, (wordIntervalWidth B w k y) ^ f := by
  rw [Finset.sum_image (joinDigit_injOn C D B hB hC), Finset.sum_product]
  calc
    _ = ∑ x ∈ C, ∑ y ∈ D, (w x) ^ f * (wordIntervalWidth B w k y) ^ f := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      simp only [wordIntervalWidth]
      rw [joinIntervalWidth_eval B w (wordIntervalWidth B w k) x y hB (hC x hx)]
      exact Real.mul_rpow (hw x hx) (wordIntervalWidth_nonneg C B w hB hC hw k y (hD hy))
    _ = _ := by simp_rw [← Finset.mul_sum]; rw [← Finset.sum_mul]

/-- The moment sum of all word widths factors exactly as a power of the
single-digit moment sum. This identity does not need an entropy approximation. -/
theorem wordIntervalWidth_moment (C : Finset ℤ) (B : ℤ) (w : ℤ → ℝ)
    (hB : 0 < B) (hC : ∀ x ∈ C, 0 ≤ x ∧ x < B)
    (hw : ∀ x ∈ C, 0 ≤ w x) (f : ℝ) (k : ℕ) :
    ∑ x ∈ intervalWords C B k, (wordIntervalWidth B w k x) ^ f =
      (∑ x ∈ C, (w x) ^ f) ^ k := by
  induction k with
  | zero => simp [intervalWords, wordIntervalWidth]
  | succ k ih =>
    simpa only [intervalWords, ih, pow_succ'] using
      children_moment C (intervalWords C B k) B w hB hC hw f k (fun _ hx => hx)

end Sarkozy
