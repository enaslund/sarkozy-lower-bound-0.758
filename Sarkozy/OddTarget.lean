import Sarkozy.OddLift
import Sarkozy.ReducedTarget

/-!
# A modular interface for unexpanded odd low supports

Both depth-three odd alphabets are constructed by the formal prime-coordinate
free-digit lift. This interface takes their low supports, interval geometry,
first-difference order and scalar moments, together with an expanded binary
certificate. All six prime chains and their numerical moments are supplied
by library proofs. The concrete odd and binary inputs are also proved in the
library and assembled into the unconditional result in `Sarkozy.FullTarget`.
-/

namespace Sarkozy

open scoped BigOperators

def recordOddPrimes : Fin 2 → Fin 2 → ℕ := ![![5, 43], ![19, 23]]

def recordOddRoots : Fin 2 → ℕ := ![215, 437]

abbrev RecordOddWord (j : Fin 2) := OddWord (recordOddPrimes j) (fun _ => 3)

def recordOddIndex (j : Fin 2) : Fin 9 := Fin.natAdd 6 (Fin.castAdd 1 j)

theorem recordOddPrimes_prime (j : Fin 2) : ∀ i, (recordOddPrimes j i).Prime := by
  fin_cases j <;> decide

theorem recordOddPrimes_pos (j : Fin 2) : ∀ i, 0 < recordOddPrimes j i := by
  intro i
  exact (recordOddPrimes_prime j i).pos

theorem recordOddPrimes_coprime (j : Fin 2) :
    Pairwise (fun i k => (recordOddPrimes j i).Coprime (recordOddPrimes j k)) := by
  unfold Pairwise
  fin_cases j <;> decide

theorem recordOdd_modulus (j : Fin 2) :
    (∏ i, recordOddPrimes j i ^ (2 * 3)) = componentBases (recordOddIndex j) := by
  fin_cases j <;>
    norm_num [recordOddPrimes, recordOddIndex, componentBases, componentRoots,
      componentDepths, Fin.prod_univ_succ, Fin.natAdd, Fin.castAdd]

theorem recordOdd_free_factor (j : Fin 2) :
    (∏ i, recordOddPrimes j i ^ 3) = recordOddRoots j ^ 3 := by
  fin_cases j <;> norm_num [recordOddPrimes, recordOddRoots, Fin.prod_univ_succ]

/-- Construct either record odd component from its correlated low support. -/
theorem record_odd_interval_alphabet (j : Fin 2) (S : Finset (RecordOddWord j))
    (left width : RecordOddWord j → ℝ)
    (hgeometry : ∀ a ∈ S, 0 ≤ left a ∧ 0 < width a ∧ width a < 1 ∧
      left a + width a ≤ 1)
    (horder : ∀ a ∈ S, ∀ b ∈ S, a ≠ b →
      (∀ i, PrimeLowRelated (recordOddPrimes j i) 3 (a i) (b i)) →
      left a + width a ≤ left b) :
    ∃ (C : Finset ℤ) (a w : ℤ → ℝ),
      C.card = S.card * recordOddRoots j ^ 3 ∧
      (∀ x ∈ C, 0 ≤ x ∧ x < componentBases (recordOddIndex j)) ∧
      (∀ x ∈ C, 0 ≤ a x ∧ 0 < w x ∧ w x < 1 ∧ a x + w x ≤ 1) ∧
      IntervalOrderedModulo C (componentBases (recordOddIndex j)) a w ∧
      ∀ f : ℝ, (∑ x ∈ C, (w x) ^ f) =
        (recordOddRoots j ^ 3 : ℕ) * ∑ x ∈ S, (width x) ^ f := by
  have h := odd_prime_interval_lift (recordOddPrimes j) (fun _ => 3)
    (recordOddPrimes_prime j) (recordOddPrimes_pos j) (recordOddPrimes_coprime j)
    S left width hgeometry horder
  simpa only [recordOdd_modulus, recordOdd_free_factor] using h

/-- The record exponent with both odd prime-coordinate expansions discharged.
The supplied odd hypotheses refer only to the low supports. -/
theorem target_exponent_of_odd_low_supports
    (S : (j : Fin 2) → Finset (RecordOddWord j))
    (left width : (j : Fin 2) → RecordOddWord j → ℝ)
    (hgeometry : ∀ j, ∀ a ∈ S j, 0 ≤ left j a ∧ 0 < width j a ∧ width j a < 1 ∧
      left j a + width j a ≤ 1)
    (horder : ∀ j, ∀ a ∈ S j, ∀ b ∈ S j, a ≠ b →
      (∀ i, PrimeLowRelated (recordOddPrimes j i) 3 (a i) (b i)) →
      left j a + width j a ≤ left j b)
    (hmoment : ∀ j,
      (componentBases (recordOddIndex j) : ℝ) ^ targetExponent ≤
        (recordOddRoots j ^ 3 : ℕ) *
          ∑ x ∈ S j, (width j x) ^ (componentPowers (recordOddIndex j)))
    (CB : Finset ℤ) (aB wB : ℤ → ℝ)
    (hCB : ∀ x ∈ CB, 0 ≤ x ∧ x < componentBases 8)
    (hgeomB : ∀ x ∈ CB, 0 ≤ aB x ∧ 0 < wB x ∧ wB x < 1 ∧ aB x + wB x ≤ 1)
    (horderB : IntervalOrderedModulo CB (componentBases 8) aB wB)
    (hmomentB : (componentBases 8 : ℝ) ^ targetExponent ≤
      ∑ x ∈ CB, (wB x) ^ (componentPowers 8)) :
    LowerBoundExponent targetExponent := by
  classical
  have hodd (j : Fin 2) := record_odd_interval_alphabet j (S j) (left j) (width j)
    (hgeometry j) (horder j)
  choose Co ao wo hcard hcan hgeom hord hmom using hodd
  let C : Fin 3 → Finset ℤ := Fin.append Co (fun _ : Fin 1 => CB)
  let a : Fin 3 → ℤ → ℝ := Fin.append ao (fun _ : Fin 1 => aB)
  let w : Fin 3 → ℤ → ℝ := Fin.append wo (fun _ : Fin 1 => wB)
  have hbindex (j : Fin 1) : Fin.natAdd 6 (Fin.natAdd 2 j) = (8 : Fin 9) := by
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rfl
  apply target_exponent_of_three_interval_certificates C a w
  · intro i
    refine Fin.addCases (m := 2) (n := 1) (fun j => ?_) (fun j => ?_) i
    · simpa [C, recordOddIndex] using hcan j
    · rw [hbindex]
      simpa only [C, Fin.append_right] using hCB
  · intro i
    refine Fin.addCases (m := 2) (n := 1) (fun j => ?_) (fun j => ?_) i
    · simpa [C, a, w] using hgeom j
    · simpa [C, a, w] using hgeomB
  · intro i
    refine Fin.addCases (m := 2) (n := 1) (fun j => ?_) (fun j => ?_) i
    · simpa [C, a, w, recordOddIndex] using hord j
    · rw [hbindex]
      simpa only [C, a, w, Fin.append_right] using horderB
  · intro i
    refine Fin.addCases (m := 2) (n := 1) (fun j => ?_) (fun j => ?_) i
    · simpa [C, w, hmom, recordOddIndex] using hmoment j
    · rw [hbindex]
      simpa only [C, w, Fin.append_right] using hmomentB

end Sarkozy
