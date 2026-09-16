import Sarkozy.Intervals

/-!
# Selecting words at a width threshold

This file replaces asymptotic type counting by a finite stopping construction:
keep extending a word while its interval is wider than a threshold, and retain
it the first time its width crosses that threshold.
-/

namespace Sarkozy

/-- A finite branching-mass recurrence must release a substantial amount of
mass at some depth if all active mass has vanished at the final depth. -/
theorem finite_mass_selection (q L : ℝ) (m t : ℕ → ℝ) (K : ℕ)
    (hq : 0 < q) (hL : q ≤ L) (hm0 : m 0 = 1) (hmK : m K = 0)
    (hm : ∀ k ≤ K, 0 ≤ m k)
    (hstep : ∀ k < K, m (k + 1) + t k = L * m k) :
    ∃ k < K, q ^ (k + 1) ≤ t k * ((K : ℝ) + 1) := by
  by_contra hnone
  push Not at hnone
  have hinv : ∀ k ≤ K,
      q ^ k * ((K : ℝ) + 1 - k) ≤ m k * ((K : ℝ) + 1) := by
    intro k
    induction k with
    | zero => simp [hm0]
    | succ k ih =>
      intro hk
      have hk' : k < K := by omega
      have ih' := ih (by omega)
      have hsmall := hnone k hk'
      have hmul := mul_le_mul_of_nonneg_left ih' (le_of_lt hq)
      have hscale := mul_le_mul_of_nonneg_right hL (hm k (by omega))
      have hscale' := mul_le_mul_of_nonneg_right hscale (by positivity : 0 ≤ (K : ℝ) + 1)
      have hrec := congrArg (fun z : ℝ => z * ((K : ℝ) + 1)) (hstep k hk')
      rw [pow_succ'] at hsmall ⊢
      push_cast
      nlinarith
  have hlast := hinv K (le_refl K)
  rw [hmK] at hlast
  have := pow_pos hq K
  simp only [add_sub_cancel_left, mul_one, zero_mul] at hlast
  linarith

/-- Active words are still wider than the threshold; only active words branch. -/
noncomputable def activeWords (C : Finset ℤ) (B : ℤ) (w : ℤ → ℝ) (δ : ℝ) :
    ℕ → Finset ℤ
  | 0 => {0}
  | k + 1 => by
    classical
    exact ((C ×ˢ activeWords C B w δ k).image (joinDigit B)).filter
      (fun x => δ < wordIntervalWidth B w (k + 1) x)

/-- Terminal words at index `k` have length `k+1`: their parent is active, but
their own width has reached or crossed the threshold. -/
noncomputable def terminalWords (C : Finset ℤ) (B : ℤ) (w : ℤ → ℝ) (δ : ℝ)
    (k : ℕ) : Finset ℤ := by
  classical
  exact ((C ×ˢ activeWords C B w δ k).image (joinDigit B)).filter
    (fun x => wordIntervalWidth B w (k + 1) x ≤ δ)

theorem activeWords_subset (C : Finset ℤ) (B : ℤ) (w : ℤ → ℝ) (δ : ℝ)
    (k : ℕ) : activeWords C B w δ k ⊆ intervalWords C B k := by
  classical
  induction k with
  | zero => simp [activeWords, intervalWords]
  | succ k ih =>
    exact (Finset.filter_subset _ _).trans
      (Finset.image_subset_image (Finset.product_subset_product_right ih))

theorem activeWords_width (C : Finset ℤ) (B : ℤ) (w : ℤ → ℝ) (δ : ℝ)
    (hδ : δ < 1) (k : ℕ) :
    ∀ x ∈ activeWords C B w δ k, δ < wordIntervalWidth B w k x := by
  cases k with
  | zero => intro x hx; simpa [wordIntervalWidth] using hδ
  | succ k => exact fun _ hx => (Finset.mem_filter.mp hx).2

theorem terminalWords_subset (C : Finset ℤ) (B : ℤ) (w : ℤ → ℝ) (δ : ℝ)
    (k : ℕ) : terminalWords C B w δ k ⊆ intervalWords C B (k + 1) := by
  classical
  exact (Finset.filter_subset _ _).trans
    (Finset.image_subset_image (Finset.product_subset_product_right
      (activeWords_subset C B w δ k)))

/-- Terminal widths differ from the threshold by at most one digit-width factor. -/
theorem terminalWords_width (C : Finset ℤ) (B : ℤ) (w : ℤ → ℝ) (δ σ : ℝ)
    (hB : 0 < B) (hC : ∀ x ∈ C, 0 ≤ x ∧ x < B)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hσ : 0 < σ) (hw : ∀ x ∈ C, σ ≤ w x)
    (k : ℕ) :
    ∀ z ∈ terminalWords C B w δ k,
      δ * σ < wordIntervalWidth B w (k + 1) z ∧
      wordIntervalWidth B w (k + 1) z ≤ δ := by
  intro z hz
  have hz' := Finset.mem_filter.mp hz
  refine ⟨?_, hz'.2⟩
  obtain ⟨⟨x,y⟩, hxy, rfl⟩ := Finset.mem_image.mp hz'.1
  obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
  simp only [wordIntervalWidth]
  rw [joinIntervalWidth_eval B w (wordIntervalWidth B w k) x y hB (hC x hx)]
  have hparent := activeWords_width C B w δ hδ1 k y hy
  have hlow := mul_lt_mul_of_pos_left hparent hσ
  have hhigh := mul_le_mul_of_nonneg_right (hw x hx) (le_of_lt (hδ0.trans hparent))
  nlinarith

/-- Active and terminal moment masses exactly partition the children. -/
theorem stopping_moment_step (C : Finset ℤ) (B : ℤ) (w : ℤ → ℝ) (δ f : ℝ)
    (hB : 0 < B) (hC : ∀ x ∈ C, 0 ≤ x ∧ x < B)
    (hw : ∀ x ∈ C, 0 ≤ w x) (k : ℕ) :
    (∑ z ∈ activeWords C B w δ (k + 1), (wordIntervalWidth B w (k + 1) z) ^ f) +
      (∑ z ∈ terminalWords C B w δ k, (wordIntervalWidth B w (k + 1) z) ^ f) =
      (∑ x ∈ C, (w x) ^ f) *
        ∑ z ∈ activeWords C B w δ k, (wordIntervalWidth B w k z) ^ f := by
  classical
  rw [← children_moment C (activeWords C B w δ k) B w hB hC hw f k
    (activeWords_subset C B w δ k)]
  simp only [activeWords, terminalWords]
  simpa only [not_lt] using Finset.sum_filter_add_sum_filter_not
    ((C ×ˢ activeWords C B w δ k).image (joinDigit B))
    (fun z => δ < wordIntervalWidth B w (k + 1) z)
    (fun z => (wordIntervalWidth B w (k + 1) z) ^ f)

/-- A moment inequality selects many words at one bounded length, all with
width at least `δ*σ`. This is a finite, entropy-free selection theorem. -/
theorem stopping_selection (C : Finset ℤ) (B : ℤ) (w : ℤ → ℝ)
    (q f δ σ ρ : ℝ) (K : ℕ)
    (hB : 0 < B) (hC : ∀ x ∈ C, 0 ≤ x ∧ x < B)
    (hq : 0 < q) (hf : 0 ≤ f) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hσ : 0 < σ)
    (hw : ∀ x ∈ C, σ ≤ w x ∧ w x ≤ ρ) (hdepth : ρ ^ K ≤ δ)
    (hmoment : q ≤ ∑ x ∈ C, (w x) ^ f) :
    ∃ (k : ℕ) (D : Finset ℤ), 1 ≤ k ∧ k ≤ K ∧
      D ⊆ intervalWords C B k ∧
      (∀ x ∈ D, δ * σ ≤ wordIntervalWidth B w k x) ∧
      q ^ k ≤ (D.card : ℝ) * δ ^ f * ((K : ℝ) + 1) := by
  have hw0 : ∀ x ∈ C, 0 ≤ w x := fun x hx => (le_of_lt hσ).trans (hw x hx).1
  have hactive : activeWords C B w δ K = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hgt := activeWords_width C B w δ hδ1 K x hx
    have hle := (wordIntervalWidth_bounds C B w hB hC σ ρ (le_of_lt hσ) hw K x
      (activeWords_subset C B w δ K hx)).2
    linarith
  let m : ℕ → ℝ := fun k =>
    ∑ x ∈ activeWords C B w δ k, (wordIntervalWidth B w k x) ^ f
  let t : ℕ → ℝ := fun k =>
    ∑ x ∈ terminalWords C B w δ k, (wordIntervalWidth B w (k + 1) x) ^ f
  have hm0 : m 0 = 1 := by simp [m, activeWords, wordIntervalWidth]
  have hmK : m K = 0 := by simp [m, hactive]
  have hm : ∀ k ≤ K, 0 ≤ m k := by
    intro k _
    apply Finset.sum_nonneg
    intro x hx
    exact Real.rpow_nonneg
      (wordIntervalWidth_nonneg C B w hB hC hw0 k x
        (activeWords_subset C B w δ k hx)) f
  have hstep : ∀ k < K,
      m (k + 1) + t k = (∑ x ∈ C, (w x) ^ f) * m k := by
    intro k _
    exact stopping_moment_step C B w δ f hB hC hw0 k
  obtain ⟨k,hk,hsel⟩ := finite_mass_selection q (∑ x ∈ C, (w x) ^ f) m t K
    hq hmoment hm0 hmK hm hstep
  refine ⟨k + 1, terminalWords C B w δ k, by omega, by omega,
    terminalWords_subset C B w δ k, ?_, ?_⟩
  · intro x hx
    exact le_of_lt (terminalWords_width C B w δ σ hB hC hδ0 hδ1 hσ
      (fun y hy => (hw y hy).1) k x hx).1
  · have htbound : t k ≤ ((terminalWords C B w δ k).card : ℝ) * δ ^ f := by
      calc
        t k ≤ ∑ x ∈ terminalWords C B w δ k, δ ^ f := by
          apply Finset.sum_le_sum
          intro x hx
          have hwidth := (terminalWords_width C B w δ σ hB hC hδ0 hδ1 hσ
            (fun y hy => (hw y hy).1) k x hx)
          apply Real.rpow_le_rpow _ hwidth.2 hf
          exact le_of_lt ((mul_pos hδ0 hσ).trans hwidth.1)
        _ = _ := by simp
    exact hsel.trans (mul_le_mul_of_nonneg_right htbound (by positivity))

/-- Separated interval data and a moment inequality give a bounded-length
ranked alphabet with the cardinality supplied by stopping-word selection. -/
theorem interval_stopping_ranked (C : Finset ℤ) (B : ℤ) (a w : ℤ → ℝ)
    (q f δ σ ρ : ℝ) (K : ℕ)
    (hB : 0 < B) (hsquare : ∃ s : ℤ, B = s ^ 2)
    (hC : ∀ x ∈ C, 0 ≤ x ∧ x < B)
    (hgeom : ∀ x ∈ C, 0 ≤ a x ∧ a x + w x ≤ 1)
    (horder : IntervalOrderedModulo C B a w)
    (hq : 0 < q) (hf : 0 ≤ f) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hσ : 0 < σ)
    (hw : ∀ x ∈ C, σ ≤ w x ∧ w x ≤ ρ) (hdepth : ρ ^ K ≤ δ)
    (hmoment : q ≤ ∑ x ∈ C, (w x) ^ f) :
    ∃ (k : ℕ) (D : Finset ℤ) (r : ℤ → ℤ),
      1 ≤ k ∧ k ≤ K ∧
      (∀ x ∈ D, 0 ≤ x ∧ x < B ^ k) ∧
      (∀ x ∈ D, 0 ≤ r x ∧ r x < ⌈1 / (δ * σ)⌉) ∧
      RankedModulo D (B ^ k) r ∧
      q ^ k ≤ (D.card : ℝ) * δ ^ f * ((K : ℝ) + 1) := by
  obtain ⟨k,D,hk0,hkK,hD,hwidth,hcard⟩ := stopping_selection C B w q f δ σ ρ K
    hB hC hq hf hδ0 hδ1 hσ hw hdepth hmoment
  have hgeom' : ∀ x ∈ C, 0 ≤ a x ∧ 0 < w x ∧ a x + w x ≤ 1 := by
    intro x hx
    exact ⟨(hgeom x hx).1, hσ.trans_le (hw x hx).1, (hgeom x hx).2⟩
  have hwords := interval_words C B a w hB hsquare hC hgeom' horder k
  have hranked := interval_subset_rank_certificate (intervalWords C B k) D (B ^ k)
    (wordIntervalStart B a w k) (wordIntervalWidth B w k) (δ * σ) hD (mul_pos hδ0 hσ)
    (fun x hx => ⟨(hwords.2.2.1 x hx).1, (hwords.2.2.1 x hx).2.2⟩)
    hwidth hwords.2.2.2
  exact ⟨k,D,intervalRank (δ * σ) (wordIntervalStart B a w k),hk0,hkK,
    (fun x hx => hwords.2.1 x (hD hx)), hranked.2.1, hranked.2.2, hcard⟩

end Sarkozy
