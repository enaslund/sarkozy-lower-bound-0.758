import Sarkozy.Ranked

/-!
# Base-square word lifting of ranked residues

Digits are read from least significant to most significant, and their ranks in
that same order form the most significant to least significant rank digits.
A square modulus permits cancelling an equal first digit from a modular square.
-/

namespace Sarkozy

/-- Join a low digit and a tail in base `B`. -/
def joinDigit (B : ℤ) (p : ℤ × ℤ) : ℤ := p.1 + B * p.2

/-- Rank the low digit first, then the tail, whose ranks are below `H`. -/
def joinRank (B H : ℤ) (r t : ℤ → ℤ) (x : ℤ) : ℤ :=
  r (x % B) * H + t (x / B)

theorem joinRank_eval (B H : ℤ) (r t : ℤ → ℤ) (x y : ℤ)
    (hB : 0 < B) (hx : 0 ≤ x ∧ x < B) :
    joinRank B H r t (joinDigit B (x,y)) = r x * H + t y := by
  simp [joinRank, joinDigit, Int.add_mul_ediv_left _ _ (ne_of_gt hB),
    Int.ediv_eq_zero_of_lt hx.1 hx.2, Int.emod_eq_of_lt hx.1 hx.2]

/-- Joining two canonical digit sets is injective. -/
theorem joinDigit_injOn (C D : Finset ℤ) (B : ℤ) (hB : 0 < B)
    (hC : ∀ x ∈ C, 0 ≤ x ∧ x < B) :
    Set.InjOn (joinDigit B) (↑(C ×ˢ D) : Set (ℤ × ℤ)) := by
  rintro ⟨x,u⟩ hx ⟨y,v⟩ hy heq
  have hxc := hC x (Finset.mem_product.mp hx).1
  have hyc := hC y (Finset.mem_product.mp hy).1
  have hmod := congrArg (fun n : ℤ => n % B) heq
  simp only [joinDigit, Int.add_mul_emod_self_left,
    Int.emod_eq_of_lt hxc.1 hxc.2, Int.emod_eq_of_lt hyc.1 hyc.2] at hmod
  have huv : u = v := by dsimp [joinDigit] at heq; nlinarith
  simp [hmod, huv]

/-- A low ranked digit and a ranked tail produce a ranked set at product modulus.
The low modulus must be a square, so a square divisible by it has a divisible root. -/
theorem ranked_join (C D : Finset ℤ) (B P h H : ℤ) (r t : ℤ → ℤ)
    (hB : 0 < B) (_hP : 0 < P) (_hh : 0 < h) (hH : 0 < H)
    (hsquare : ∃ s : ℤ, B = s ^ 2)
    (hC : ∀ x ∈ C, 0 ≤ x ∧ x < B)
    (hD : ∀ x ∈ D, 0 ≤ x ∧ x < P)
    (hr : ∀ x ∈ C, 0 ≤ r x ∧ r x < h)
    (ht : ∀ x ∈ D, 0 ≤ t x ∧ t x < H)
    (hCr : RankedModulo C B r) (hDt : RankedModulo D P t) :
    let E := (C ×ˢ D).image (joinDigit B)
    E.card = C.card * D.card ∧
    (∀ x ∈ E, 0 ≤ x ∧ x < B * P) ∧
    (∀ x ∈ E, 0 ≤ joinRank B H r t x ∧ joinRank B H r t x < h * H) ∧
    RankedModulo E (B * P) (joinRank B H r t) := by
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
    rw [joinRank_eval B H r t x y hB (hC x hx)]
    have hxr := hr x hx
    have hyt := ht y hy
    constructor
    · exact add_nonneg (mul_nonneg hxr.1 (le_of_lt hH)) hyt.1
    · have hxr1 : r x ≤ h - 1 := by omega
      nlinarith [mul_le_mul_of_nonneg_right hxr1 (le_of_lt hH)]
  · intro a ha b hb hab hs
    obtain ⟨⟨x,u⟩, hxu, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨⟨y,v⟩, hyv, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hx,hu⟩ := Finset.mem_product.mp hxu
    obtain ⟨hy,hv⟩ := Finset.mem_product.mp hyv
    rw [joinRank_eval B H r t x u hB (hC x hx),
      joinRank_eval B H r t y v hB (hC y hy)]
    obtain ⟨z, q, hq⟩ := hs
    dsimp [joinDigit] at hab hq
    by_cases hxy : x = y
    · subst y
      have huv : u ≠ v := by intro he; exact hab (by rw [he])
      obtain ⟨s,hs⟩ := hsquare
      have hroot : s ∣ z := by
        apply (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp
        refine ⟨v - u - P * q, ?_⟩
        nlinarith [hq]
      obtain ⟨w, rfl⟩ := hroot
      have htail : P ∣ v - u - w ^ 2 := by
        refine ⟨q, ?_⟩
        have heq : B * (v - u - w ^ 2) = B * (P * q) := by
          rw [hs] at hq ⊢
          nlinarith [hq]
        exact (mul_left_cancel₀ (ne_of_gt hB) heq)
      have hlt := hDt u hu v hv huv ⟨w, htail⟩
      linarith
    · have hlow : B ∣ y - x - z ^ 2 := by
        refine ⟨P * q - v + u, ?_⟩
        nlinarith [hq]
      have hlt := hCr x hx y hy hxy ⟨z, hlow⟩
      have huR := ht u hu
      have hvR := ht v hv
      have hr1 : r x + 1 ≤ r y := by omega
      nlinarith [mul_le_mul_of_nonneg_right hr1 (le_of_lt hH)]

/-- Every word length admits canonical ranked residues with multiplicative
cardinality and the corresponding power bound on ranks. -/
theorem ranked_words (C : Finset ℤ) (B h : ℤ) (r : ℤ → ℤ)
    (hB : 0 < B) (hh : 0 < h) (hsquare : ∃ s : ℤ, B = s ^ 2)
    (hC : ∀ x ∈ C, 0 ≤ x ∧ x < B)
    (hr : ∀ x ∈ C, 0 ≤ r x ∧ r x < h) (hCr : RankedModulo C B r)
    (k : ℕ) :
    ∃ (D : Finset ℤ) (t : ℤ → ℤ),
      D.card = C.card ^ k ∧
      (∀ x ∈ D, 0 ≤ x ∧ x < B ^ k) ∧
      (∀ x ∈ D, 0 ≤ t x ∧ t x < h ^ k) ∧
      RankedModulo D (B ^ k) t := by
  induction k with
  | zero =>
    refine ⟨{0}, fun _ => 0, by simp, ?_, ?_, ?_⟩
    · simp
    · simp
    · intro x hx y hy hxy _
      simp only [Finset.mem_singleton] at hx hy
      exact (hxy (hx.trans hy.symm)).elim
  | succ k ih =>
    obtain ⟨D,t,hcard,hcan,hrange,hranked⟩ := ih
    have hj := ranked_join C D B (B ^ k) h (h ^ k) r t hB (pow_pos hB k)
      hh (pow_pos hh k) hsquare hC hcan hr hrange hCr hranked
    refine ⟨(C ×ˢ D).image (joinDigit B), joinRank B (h ^ k) r t, ?_, ?_, ?_, ?_⟩
    · simpa [hcard, pow_succ, Nat.mul_comm] using hj.1
    · simpa [pow_succ, mul_comm] using hj.2.1
    · simpa [pow_succ, mul_comm] using hj.2.2.1
    · simpa [pow_succ, mul_comm] using hj.2.2.2

/-- The word construction gives `|C|^k` square-difference-free integers below
`(B*h)^k`. All finite certificate properties are explicit hypotheses. -/
theorem ranked_word_realization (C : Finset ℤ) (B h : ℤ) (r : ℤ → ℤ)
    (hB : 0 < B) (hh : 0 < h) (hsquare : ∃ s : ℤ, B = s ^ 2)
    (hC : ∀ x ∈ C, 0 ≤ x ∧ x < B)
    (hr : ∀ x ∈ C, 0 ≤ r x ∧ r x < h) (hCr : RankedModulo C B r)
    (k : ℕ) :
    ∃ A : Finset ℤ, A.card = C.card ^ k ∧
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ (B * h) ^ k) ∧ SquareDifferenceFree A := by
  obtain ⟨D,t,hcard,hcan,hrange,hranked⟩ :=
    ranked_words C B h r hB hh hsquare hC hr hCr k
  have hrange' : ∀ x ∈ D, 0 ≤ t x ∧ t x ≤ h ^ k - 1 := by
    intro x hx
    have := hrange x hx
    omega
  obtain ⟨A,hAcard,hAbound,hAfree⟩ := reverseRank_realization D (B ^ k)
    (h ^ k - 1) t (pow_pos hB k) hcan hrange' hranked
  refine ⟨A, hAcard.trans hcard, ?_, hAfree⟩
  simpa [mul_pow] using hAbound

end Sarkozy
