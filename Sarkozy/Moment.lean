import Sarkozy.Intervals
import Sarkozy.Certificate
import Sarkozy.Growth
import Sarkozy.Stopping

/-! Combining width-selected finite word blocks into an asymptotic bound. -/

namespace Sarkozy

open scoped BigOperators

/-- The final combination step for word blocks selected at a common width.
The selection hypothesis will be discharged by the stopping-word lemma. -/
theorem exponent_of_selected_words {ι : Type*} [Fintype ι] [Nonempty ι]
    (C : ι → Finset ℤ) (B : ι → ℕ) (a w : ι → ℤ → ℝ)
    (f : ι → ℝ) (α σ ρ : ℝ)
    (hB : ∀ i, 1 < B i)
    (hcop : Pairwise (fun i j => (B i).Coprime (B j)))
    (hsquare : ∀ i, ∃ s : ℕ, B i = s ^ 2)
    (hC : ∀ i, ∀ x ∈ C i, 0 ≤ x ∧ x < B i)
    (hσ : 0 < σ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hgeom : ∀ i, ∀ x ∈ C i,
      0 ≤ a i x ∧ σ ≤ w i x ∧ w i x ≤ ρ ∧ a i x + w i x ≤ 1)
    (horder : ∀ i, IntervalOrderedModulo (C i) (B i) (a i) (w i))
    (hα : 0 ≤ α) (hgap : α < ∑ i, f i)
    (hselect : ∀ i K, 0 < K → ∃ k : ℕ, ∃ D : Finset ℤ,
      0 < k ∧ k ≤ K ∧ D ⊆ intervalWords (C i) (B i) k ∧
      (∀ x ∈ D, (ρ ^ K) * σ ≤ wordIntervalWidth (B i) (w i) k x) ∧
      (((B i) ^ k : ℕ) : ℝ) ^ α ≤ D.card * (ρ ^ K) ^ (f i) * ((K : ℝ) + 1)) :
    LowerBoundExponent α := by
  classical
  let n := Fintype.card ι
  let c : ℝ := ((n : ℝ) + 1) * (1 / σ + 1)
  have hc : 0 < c := by dsimp [c]; positivity
  have hev := eventually_moment_budget ρ (c ^ α) α (∑ i, f i)
    hρ hρ1 (Real.rpow_pos_of_pos hc _) hgap n
  obtain ⟨K, hbudget, hK⟩ := (hev.and (Filter.eventually_gt_atTop 0)).exists
  let δ : ℝ := ρ ^ K
  have hδ : 0 < δ := pow_pos hρ K
  have hδ1 : δ ≤ 1 := pow_le_one₀ hρ.le hρ1.le
  choose k D hk hkK hsub hwidth hsize using fun i => hselect i K hK
  let M : ι → ℕ := fun i => (B i) ^ (k i)
  let H : ℕ := ⌈1 / (δ * σ)⌉₊
  let J : ι → ℕ := fun _ => H - 1
  let r : ι → ℤ → ℤ := fun i => intervalRank (δ * σ)
    (wordIntervalStart (B i) (a i) (w i) (k i))
  have hH : 1 ≤ H := by
    have : 0 < H := Nat.ceil_pos.mpr (by positivity)
    omega
  have hdata (i : ι) := interval_words (C i) (B i) (a i) (w i)
    (by exact_mod_cast (show 0 < B i by have := hB i; omega))
    (by obtain ⟨s,hs⟩ := hsquare i; exact ⟨(s : ℤ), by exact_mod_cast hs⟩)
    (hC i) (fun x hx => ⟨(hgeom i x hx).1,
      hσ.trans_le (hgeom i x hx).2.1, (hgeom i x hx).2.2.2⟩) (horder i) (k i)
  have hcan : ∀ i, ∀ x ∈ D i, 0 ≤ x ∧ x < M i := by
    intro i x hx
    simpa only [M, Nat.cast_pow] using (hdata i).2.1 x (hsub i hx)
  have hrankdata (i : ι) := interval_subset_rank_certificate
    (intervalWords (C i) (B i) (k i)) (D i) ((B i : ℤ) ^ (k i))
    (wordIntervalStart (B i) (a i) (w i) (k i))
    (wordIntervalWidth (B i) (w i) (k i)) (δ * σ) (hsub i) (by positivity)
    (fun x hx => ⟨((hdata i).2.2.1 x hx).1, ((hdata i).2.2.1 x hx).2.2⟩)
    (hwidth i) (hdata i).2.2.2
  have hrange : ∀ i, ∀ x ∈ D i, 0 ≤ r i x ∧ r i x ≤ J i := by
    intro i x hx
    have ht := (hrankdata i).2.1 x hx
    have hceil : (H : ℤ) = ⌈1 / (δ * σ)⌉ :=
      Int.natCast_ceil_eq_ceil (by positivity)
    have hsubH : ((H - 1 : ℕ) : ℤ) = (H : ℤ) - 1 := by omega
    dsimp [r, J]
    rw [hsubH, hceil]
    exact ⟨ht.1, by omega⟩
  have hranked : ∀ i, RankedModulo (D i) (M i) (r i) := by
    intro i
    simpa only [M, Nat.cast_pow, r] using (hrankdata i).2.2
  have hM : ∀ i, 0 < M i := fun i => pow_pos (by have := hB i; omega) _
  have hM1 : ∀ i, 1 < M i := fun i => one_lt_pow₀ (hB i) (Nat.ne_of_gt (hk i))
  have hprod : 1 < ∏ i, M i := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hle : M i ≤ ∏ j, M j :=
      Finset.single_le_prod' (fun j _ => (hM1 j).le) (Finset.mem_univ i)
    exact (hM1 i).trans_le hle
  have hMcop : Pairwise (fun i j => (M i).Coprime (M j)) := by
    intro i j hij
    exact (hcop hij).pow _ _
  have hMsq : ∀ i, ∃ s : ℕ, M i = s ^ 2 := by
    intro i
    obtain ⟨s,hs⟩ := hsquare i
    refine ⟨s ^ k i, ?_⟩
    simp only [M, hs, ← pow_mul, Nat.mul_comm]
  apply crt_alphabet_exponent D M J r hM hprod hMcop hMsq hcan hrange hranked α hα
  have hcards : ((∏ i, M i : ℕ) : ℝ) ^ α ≤
      (∏ i, (D i).card : ℕ) * δ ^ (∑ i, f i) * ((K : ℝ) + 1) ^ n := by
    have hp := Finset.prod_le_prod (s := Finset.univ)
      (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg (M i)) α)
      (fun i _ => hsize i)
    simpa only [← Nat.cast_prod, Real.finsetProd_rpow Finset.univ
      (fun i => (M i : ℝ)) (fun i _ => Nat.cast_nonneg _) α,
      Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hδ,
      Finset.prod_const, Finset.card_univ, n, δ, M] using hp
  have hrank : ((1 + ∑ i, J i : ℕ) : ℝ) ≤ c / δ := by
    have hh := ceiling_rank_budget n σ δ hσ hδ hδ1
    simpa only [J, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Nat.cast_id, H, c, n] using hh
  have hgrowth := weighted_growth_budget (∏ i, M i : ℕ) (∏ i, (D i).card : ℕ)
    (1 + ∑ i, J i : ℕ) δ c α (∑ i, f i) (((K : ℝ) + 1) ^ n)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hδ hc hα hcards hbudget hrank
  simpa only [Nat.cast_mul] using hgrowth

/-- The finite interval-moment criterion. Every assumption concerns the
given finite alphabets and real numerical parameters. The word selection,
CRT combination, amplification, and all-`N` conclusion are proved here. -/
theorem interval_moment_exponent {ι : Type*} [Fintype ι] [Nonempty ι]
    (C : ι → Finset ℤ) (B : ι → ℕ) (a w : ι → ℤ → ℝ)
    (f : ι → ℝ) (α σ ρ : ℝ)
    (hB : ∀ i, 1 < B i)
    (hcop : Pairwise (fun i j => (B i).Coprime (B j)))
    (hsquare : ∀ i, ∃ s : ℕ, B i = s ^ 2)
    (hC : ∀ i, ∀ x ∈ C i, 0 ≤ x ∧ x < B i)
    (hσ : 0 < σ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hgeom : ∀ i, ∀ x ∈ C i,
      0 ≤ a i x ∧ σ ≤ w i x ∧ w i x ≤ ρ ∧ a i x + w i x ≤ 1)
    (horder : ∀ i, IntervalOrderedModulo (C i) (B i) (a i) (w i))
    (hα : 0 ≤ α) (hf : ∀ i, 0 ≤ f i)
    (hmoment : ∀ i, (B i : ℝ) ^ α ≤ ∑ x ∈ C i, (w i x) ^ (f i))
    (hgap : α < ∑ i, f i) : LowerBoundExponent α := by
  apply exponent_of_selected_words C B a w f α σ ρ hB hcop hsquare hC
    hσ hρ hρ1 hgeom horder hα hgap
  intro i K hK
  obtain ⟨k,D,hk,hkK,hsub,hw,hs⟩ := stopping_selection (C i) (B i) (w i)
    ((B i : ℝ) ^ α) (f i) (ρ ^ K) σ ρ K
    (by exact_mod_cast (show 0 < B i by have := hB i; omega)) (hC i)
    (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < B i by have := hB i; omega)) α)
    (hf i) (pow_pos hρ K) (pow_lt_one₀ hρ.le hρ1 (Nat.ne_of_gt hK)) hσ
    (fun x hx => ⟨(hgeom i x hx).2.1, (hgeom i x hx).2.2.1⟩) le_rfl (hmoment i)
  refine ⟨k,D,by omega,hkK,hsub,hw,?_⟩
  simpa only [Nat.cast_pow, Real.rpow_pow_comm (Nat.cast_nonneg (B i))] using hs

end Sarkozy
