import Sarkozy.OddTarget

/-!
# From finite integer low-point data to an odd interval certificate

Rows contain two packed canonical prime-adic low words and integer interval
endpoints with a common denominator. This bridge preserves the exact support
size and every real-power moment while turning finite integer comparisons
into the low-support hypotheses used by the proved free-digit lift.
-/

namespace Sarkozy

open scoped BigOperators

/-- Realize an indexed integer certificate for either depth-three odd component.
The order hypothesis refers only to its packed low words, before free digits
or CRT are introduced. All resulting moments are preserved exactly. -/
theorem record_odd_finite_certificate
    (j : Fin 2) (n D : ℕ) (point : Fin n → Fin 2 → ℕ)
    (start width : Fin n → ℕ)
    (hD : 0 < D)
    (hpoint : ∀ k i, point k i < (recordOddPrimes j i)^3)
    (hinj : Function.Injective point)
    (hwidth : ∀ k, 0 < width k ∧ width k < D)
    (hend : ∀ k, start k + width k ≤ D)
    (horder : ∀ k l, k ≠ l →
      (∀ i, PrimeLowRelated (recordOddPrimes j i) 3 (point k i : ℤ) (point l i : ℤ)) →
      start k + width k ≤ start l) :
    ∃ (S : Finset (RecordOddWord j)) (left widthS : RecordOddWord j → ℝ),
      S.card = n ∧
      (∀ a ∈ S, 0 ≤ left a ∧ 0 < widthS a ∧ widthS a < 1 ∧
        left a + widthS a ≤ 1) ∧
      (∀ a ∈ S, ∀ b ∈ S, a ≠ b →
        (∀ i, PrimeLowRelated (recordOddPrimes j i) 3 (a i) (b i)) →
        left a + widthS a ≤ left b) ∧
      ∀ f : ℝ, (∑ a ∈ S, (widthS a)^f) =
        ∑ k : Fin n, ((width k : ℝ) / D)^f := by
  classical
  let encode : Fin n → RecordOddWord j := fun k i => ⟨point k i, hpoint k i⟩
  have hencode : Function.Injective encode := by
    intro k l heq
    apply hinj
    funext i
    exact congrArg Fin.val (congrFun heq i)
  let S := Finset.univ.image encode
  let left : RecordOddWord j → ℝ :=
    Function.extend encode (fun k => (start k : ℝ) / D) (fun _ => 0)
  let widthS : RecordOddWord j → ℝ :=
    Function.extend encode (fun k => (width k : ℝ) / D) (fun _ => 0)
  have hleft (k : Fin n) : left (encode k) = (start k : ℝ) / D :=
    hencode.extend_apply _ _ k
  have hw (k : Fin n) : widthS (encode k) = (width k : ℝ) / D :=
    hencode.extend_apply _ _ k
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  refine ⟨S, left, widthS, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hencode]
    simp
  · intro a ha
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ha
    rw [hleft, hw]
    refine ⟨div_nonneg (by positivity) hDR.le,
      div_pos (by exact_mod_cast (hwidth k).1) hDR,
      (div_lt_one hDR).mpr (by exact_mod_cast (hwidth k).2), ?_⟩
    rw [← add_div, div_le_one hDR]
    exact_mod_cast hend k
  · intro a ha b hb hab hrel
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hb
    have hkl : k ≠ l := fun h => hab (congrArg encode h)
    have hr : start k + width k ≤ start l := horder k l hkl hrel
    rw [hleft, hw, hleft, ← add_div]
    exact (div_le_div_iff_of_pos_right hDR).mpr (by exact_mod_cast hr)
  · intro f
    dsimp [S]
    rw [Finset.sum_image hencode.injOn]
    exact Finset.sum_congr rfl (fun k _ => by rw [hw])

end Sarkozy
