import Sarkozy.OddOrderChecks215

/-!
# The actual 215 low certificate has correctly ordered square edges

All integer geometry and edge-order hypotheses for this concrete depth-three
support are discharged here. Its power-moment inequality is a separate
numerical theorem. The rows retain all original widths and are indexed by
increasing right endpoint for efficient finite checking.
-/

namespace Sarkozy.OddOrder215

open OddOrder

noncomputable def row (k : Fin 4913) : Entry := rows.get (Fin.cast rows_size.symm k)

noncomputable def point (k : Fin 4913) (c : Fin 2) : ℕ := ![(row k).1.1.1, (row k).1.1.2] c

noncomputable def start (k : Fin 4913) : ℕ := (row k).1.2.1

noncomputable def width (k : Fin 4913) : ℕ := (row k).1.2.2

theorem denominator_pos : 0 < denominator := by decide +kernel

theorem row_bounds (k : Fin 4913) :
    (row k).1.1.1 < 125 ∧ (row k).1.1.2 < 79507 ∧
    0 < width k ∧ width k < denominator ∧ start k + width k ≤ denominator := by
  apply (OddData.valid_iff 125 79507 denominator (row k).1).mp
  exact List.all_eq_true.mp rows_valid _ (List.get_mem _ _)

theorem point_bounds (k : Fin 4913) (c : Fin 2) :
    point k c < (recordOddPrimes 0 c)^3 := by
  have h := row_bounds k
  fin_cases c
  · change (row k).1.1.1 < 125
    exact h.1
  · change (row k).1.1.2 < 79507
    exact h.2.1

theorem width_bounds (k : Fin 4913) : 0 < width k ∧ width k < denominator :=
  ⟨(row_bounds k).2.2.1, (row_bounds k).2.2.2.1⟩

theorem endpoint_bound (k : Fin 4913) : start k + width k ≤ denominator :=
  (row_bounds k).2.2.2.2

/-- Every semantic square edge has its entire source interval before the target. -/
theorem low_order : ∀ k l : Fin 4913, k ≠ l →
    (∀ c, PrimeLowRelated (recordOddPrimes 0 c) 3 (point k c : ℤ) (point l c : ℤ)) →
    start k + width k ≤ start l := by
  intro k l hne hrel
  have h := interval_order_of_checked_rows 5 43 3 (by decide) (by decide)
    rows G5 G43 endpointTable sources_checked targets_checked endpoints_sorted
  change entryEnd (rows.get (Fin.cast rows_size.symm k)) ≤
    entryStart (rows.get (Fin.cast rows_size.symm l))
  apply h _ _ (fun heq => hne (Fin.cast_injective _ heq))
  intro c
  fin_cases c
  · exact hrel 0
  · exact hrel 1

theorem point_injective : Function.Injective point := by
  have h := point_injective_of_order 4913 (recordOddPrimes 0) 3
    (fun k c => (point k c : ℤ)) start width (fun k => (width_bounds k).1) low_order
  intro k l heq
  apply h
  funext c
  exact congrArg (fun x : ℕ => (x : ℤ)) (congrFun heq c)

end Sarkozy.OddOrder215
