import Mathlib

/-!
# Reverse-rank realization of ranked residues

This file formalizes the finite conversion in `METHODS.md`. A rank which
increases along modular square differences lets us choose one integer
representative of every residue, with no positive square differences.

The hypotheses are mathematical properties of arbitrary finite data; no
computational certificate or unproved axiom is used here.
-/

namespace Sarkozy

/-- No difference between two members is the square of a nonzero integer. -/
def SquareDifferenceFree (A : Finset ℤ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z : ℤ, z ≠ 0 → y - x ≠ z ^ 2

/-- Ranks increase whenever distinct residues have a modular square difference.
The possible square residues include zero. -/
def RankedModulo (C : Finset ℤ) (M : ℤ) (r : ℤ → ℤ) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
    (∃ z : ℤ, M ∣ (y - x - z ^ 2)) → r x < r y

/-- Choose the integer representative in the block opposite to its rank. -/
def reverseRank (M K : ℤ) (r : ℤ → ℤ) (x : ℤ) : ℤ :=
  1 + x + M * (K - r x)

/-- The integer set obtained by choosing the reverse-rank representatives. -/
def reverseRankSet (C : Finset ℤ) (M K : ℤ) (r : ℤ → ℤ) : Finset ℤ :=
  C.image (reverseRank M K r)

/-- Distinct canonical residues give distinct reverse-rank representatives. -/
theorem reverseRank_injOn (C : Finset ℤ) (M K : ℤ) (r : ℤ → ℤ)
    (hM : 0 < M) (hcanonical : ∀ x ∈ C, 0 ≤ x ∧ x < M) :
    Set.InjOn (reverseRank M K r) (↑C : Set ℤ) := by
  intro x hx y hy heq
  have hxc := hcanonical x hx
  have hyc := hcanonical y hy
  dsimp [reverseRank] at heq
  rcases lt_trichotomy (r x) (r y) with hlt | he | hgt
  · have hg : 0 ≤ r y - r x - 1 := by omega
    have hp := mul_nonneg (le_of_lt hM) hg
    nlinarith
  · rw [he] at heq
    linarith
  · have hg : 0 ≤ r x - r y - 1 := by omega
    have hp := mul_nonneg (le_of_lt hM) hg
    nlinarith

/-- Canonical residues and ranks between `0` and `K` give the claimed interval. -/
theorem reverseRank_bounds (M K : ℤ) (r : ℤ → ℤ) (x : ℤ)
    (hM : 0 < M) (hx : 0 ≤ x ∧ x < M) (hr : 0 ≤ r x ∧ r x ≤ K) :
    1 ≤ reverseRank M K r x ∧ reverseRank M K r x ≤ M * (K + 1) := by
  constructor
  · have hp := mul_nonneg (le_of_lt hM) (sub_nonneg.mpr hr.2)
    dsimp [reverseRank]
    linarith
  · have hp := mul_nonneg (le_of_lt hM) hr.1
    have hupper : x ≤ M - 1 := by omega
    dsimp [reverseRank]
    nlinarith

/-- The conversion keeps every residue. -/
theorem reverseRankSet_card (C : Finset ℤ) (M K : ℤ) (r : ℤ → ℤ)
    (hM : 0 < M) (hcanonical : ∀ x ∈ C, 0 ≤ x ∧ x < M) :
    (reverseRankSet C M K r).card = C.card := by
  apply Finset.card_image_iff.mpr
  exact reverseRank_injOn C M K r hM hcanonical

/-- A modular square difference would force the representative difference to
be negative, contradicting its being a nonzero square. -/
theorem reverseRankSet_squareDifferenceFree
    (C : Finset ℤ) (M K : ℤ) (r : ℤ → ℤ)
    (hM : 0 < M) (hcanonical : ∀ x ∈ C, 0 ≤ x ∧ x < M)
    (hranked : RankedModulo C M r) :
    SquareDifferenceFree (reverseRankSet C M K r) := by
  intro a ha b hb z hz hsq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
  have hxy : x ≠ y := by
    intro he
    subst y
    have hzsq : 0 < z ^ 2 := sq_pos_of_ne_zero hz
    simp only [sub_self] at hsq
    linarith
  have hmod : M ∣ (y - x - z ^ 2) := by
    refine ⟨r y - r x, ?_⟩
    dsimp [reverseRank] at hsq
    nlinarith
  have hr := hranked x hx y hy hxy ⟨z, hmod⟩
  have hg : 0 ≤ r y - r x - 1 := by omega
  have hp := mul_nonneg (le_of_lt hM) hg
  have hxc := hcanonical x hx
  have hyc := hcanonical y hy
  have hupper : y ≤ M - 1 := by omega
  dsimp [reverseRank] at hsq
  nlinarith [sq_nonneg z]

/-- The finite construction: realize every ranked residue as an integer in
`[1, M * (K + 1)]`, without losing cardinality or admitting square differences. -/
theorem reverseRank_realization
    (C : Finset ℤ) (M K : ℤ) (r : ℤ → ℤ)
    (hM : 0 < M) (hcanonical : ∀ x ∈ C, 0 ≤ x ∧ x < M)
    (hrange : ∀ x ∈ C, 0 ≤ r x ∧ r x ≤ K)
    (hranked : RankedModulo C M r) :
    ∃ A : Finset ℤ,
      A.card = C.card ∧
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ M * (K + 1)) ∧
      SquareDifferenceFree A := by
  refine ⟨reverseRankSet C M K r, reverseRankSet_card C M K r hM hcanonical, ?_,
    reverseRankSet_squareDifferenceFree C M K r hM hcanonical hranked⟩
  intro a ha
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  exact reverseRank_bounds M K r x hM (hcanonical x hx) (hrange x hx)

end Sarkozy
