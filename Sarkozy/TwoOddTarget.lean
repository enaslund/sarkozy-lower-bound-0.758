import Sarkozy.BinaryRows
import Sarkozy.BinaryDepth

/-!
# A modular interface for the two odd components

All six prime chains and the full record binary component are constructed and
verified. This interface takes two expanded odd interval certificates; the
low-support interface in `RecordTarget` additionally constructs their lifts.
Both concrete odd certificates are proved in the library and assembled into
the unconditional result in `Sarkozy.FullTarget`.
-/

namespace Sarkozy

open scoped BigOperators

/-- The fixed record binary component satisfies every interval-alphabet
hypothesis, including its numerical moment, without assumptions. -/
theorem record_binary_interval_certificate :
    ∃ (C : Finset ℤ) (start width : ℤ → ℝ),
      (∀ x ∈ C, 0 ≤ x ∧ x < componentBases 8) ∧
      (∀ x ∈ C, 0 ≤ start x ∧ 0 < width x ∧ width x < 1 ∧ start x+width x ≤ 1) ∧
      IntervalOrderedModulo C (componentBases 8) start width ∧
      (componentBases 8 : ℝ)^targetExponent ≤
        ∑ x ∈ C, (width x)^(componentPowers 8) :=
  RecordBinary.interval_certificate RecordBinary.rows_verified RecordBinary.depth_condition

/-- Combine two odd certificates with the seven proved chain and binary components. -/
theorem target_exponent_of_two_odd_interval_certificates
    (C : Fin 2 → Finset ℤ) (a w : Fin 2 → ℤ → ℝ)
    (hC : ∀ i, ∀ x ∈ C i, 0 ≤ x ∧ x < componentBases (recordOddIndex i))
    (hgeom : ∀ i, ∀ x ∈ C i,
      0 ≤ a i x ∧ 0 < w i x ∧ w i x < 1 ∧ a i x+w i x ≤ 1)
    (horder : ∀ i, IntervalOrderedModulo (C i) (componentBases (recordOddIndex i))
      (a i) (w i))
    (hmoment : ∀ i, (componentBases (recordOddIndex i) : ℝ)^targetExponent ≤
      ∑ x ∈ C i, (w i x)^(componentPowers (recordOddIndex i))) :
    LowerBoundExponent targetExponent := by
  classical
  obtain ⟨CB,aB,wB,hCB,hgeomB,horderB,hmomentB⟩ := record_binary_interval_certificate
  let D : Fin 3 → Finset ℤ := Fin.append C (fun _ : Fin 1 => CB)
  let A : Fin 3 → ℤ → ℝ := Fin.append a (fun _ : Fin 1 => aB)
  let W : Fin 3 → ℤ → ℝ := Fin.append w (fun _ : Fin 1 => wB)
  have hbindex (j : Fin 1) : Fin.natAdd 6 (Fin.natAdd 2 j) = (8 : Fin 9) := by
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rfl
  apply target_exponent_of_three_interval_certificates D A W
  · intro i
    refine Fin.addCases (m := 2) (n := 1) (fun j => ?_) (fun j => ?_) i
    · simpa [D, recordOddIndex] using hC j
    · rw [hbindex]
      simpa only [D, Fin.append_right] using hCB
  · intro i
    refine Fin.addCases (m := 2) (n := 1) (fun j => ?_) (fun j => ?_) i
    · simpa [D, A, W] using hgeom j
    · simpa [D, A, W] using hgeomB
  · intro i
    refine Fin.addCases (m := 2) (n := 1) (fun j => ?_) (fun j => ?_) i
    · simpa [D, A, W, recordOddIndex] using horder j
    · rw [hbindex]
      simpa only [D, A, W, Fin.append_right] using horderB
  · intro i
    refine Fin.addCases (m := 2) (n := 1) (fun j => ?_) (fun j => ?_) i
    · simpa [D, W, recordOddIndex] using hmoment j
    · rw [hbindex]
      simpa only [D, W, Fin.append_right] using hmomentB

end Sarkozy
