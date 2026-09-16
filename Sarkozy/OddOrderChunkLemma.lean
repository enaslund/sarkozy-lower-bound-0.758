import Sarkozy.OddOrderCertificate

/-!
# Combining sequential checks of fixed-size row blocks

Every row index belongs to a checked block by quotient and remainder. The last
block may be shorter, and extra empty blocks do not affect the conclusion.
-/

namespace Sarkozy.OddOrder

/-- Pointwise indexed checks imply the sequential Boolean check. -/
theorem allIndexed_of_pointwise {α : Type} (P : ℕ → α → Bool)
    (offset : ℕ) (rows : List α)
    (h : ∀ k (hk : k < rows.length), P (offset+k) rows[k] = true) :
    allIndexed P offset rows = true := by
  induction rows generalizing offset with
  | nil => rfl
  | cons a rows ih =>
    apply Bool.and_eq_true_iff.mpr
    constructor
    · have hh := h 0 (by simp)
      change P (offset+0) a = true at hh
      simpa only [Nat.add_zero] using hh
    · apply ih
      intro k hk
      have hh := h (k+1) (by simpa using hk)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

/-- Finite checks of all consecutive blocks imply the full indexed row check. -/
theorem allIndexed_of_blocks {α : Type} (P : ℕ → α → Bool)
    (rows : List α) (b c : ℕ) (hb : 0 < b) (hlen : rows.length ≤ c*b)
    (hblocks : ∀ i : Fin c,
      allIndexed P (i.val*b) ((rows.drop (i.val*b)).take b) = true) :
    allIndexed P 0 rows = true := by
  apply allIndexed_of_pointwise
  intro k hk
  have hi : k/b < c := by
    apply (Nat.div_lt_iff_lt_mul hb).mpr
    simpa [Nat.mul_comm] using lt_of_lt_of_le hk hlen
  let i : Fin c := ⟨k/b, hi⟩
  have hj : k % b < b := Nat.mod_lt k hb
  have hsum : i.val*b + k%b = k := by
    simpa [i, Nat.mul_comm] using Nat.div_add_mod k b
  have hwithin : k%b < ((rows.drop (i.val*b)).take b).length := by
    simp only [List.length_take, List.length_drop]
    omega
  have h := allIndexed_sound P (i.val*b) ((rows.drop (i.val*b)).take b)
    (hblocks i) (k%b) hwithin
  simpa only [List.getElem_take, List.getElem_drop, hsum, Nat.zero_add] using h

end Sarkozy.OddOrder
