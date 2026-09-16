import Sarkozy.OddCertificate
import Sarkozy.OddFiniteCertificate

/-!
# Integer representation for odd low-certificate rows

A row contains two packed low words, an interval start numerator, and its
width numerator. All four entries are natural numbers. The single-row checker
has no square-edge or moment content; those independent obligations are not
silently included in its name or specification.
-/

namespace Sarkozy.OddData

abbrev Row := (ℕ × ℕ) × (ℕ × ℕ)

def valid (base0 base1 denominator : ℕ) (row : Row) : Bool :=
  decide (row.1.1 < base0 ∧ row.1.2 < base1 ∧
    0 < row.2.2 ∧ row.2.2 < denominator ∧ row.2.1 + row.2.2 ≤ denominator)

/-- The Boolean unary check is exactly the integer coordinate/interval check. -/
theorem valid_iff (base0 base1 denominator : ℕ) (row : Row) :
    valid base0 base1 denominator row = true ↔
      row.1.1 < base0 ∧ row.1.2 < base1 ∧
      0 < row.2.2 ∧ row.2.2 < denominator ∧ row.2.1 + row.2.2 ≤ denominator := by
  simp [valid]

/-- A checked array provides the stated bounds for every indexed row. -/
theorem bounds_of_all (base0 base1 denominator : ℕ) (rows : Array Row)
    (h : rows.all (valid base0 base1 denominator) = true) (k : Fin rows.size) :
    rows[k].1.1 < base0 ∧ rows[k].1.2 < base1 ∧
      0 < rows[k].2.2 ∧ rows[k].2.2 < denominator ∧
      rows[k].2.1 + rows[k].2.2 ≤ denominator :=
  (valid_iff _ _ _ _).mp (Array.all_eq_true.mp h k.val k.isLt)

/-- List-based checking avoids repeated random access while evaluating a large
literal certificate in the kernel. -/
theorem bounds_of_list_all (base0 base1 denominator : ℕ) (rows : List Row)
    (h : rows.all (valid base0 base1 denominator) = true) (k : Fin rows.length) :
    (rows.get k).1.1 < base0 ∧ (rows.get k).1.2 < base1 ∧
      0 < (rows.get k).2.2 ∧ (rows.get k).2.2 < denominator ∧
      (rows.get k).2.1 + (rows.get k).2.2 ≤ denominator :=
  (valid_iff _ _ _ _).mp (List.all_eq_true.mp h _ (List.get_mem _ _))

def key (base0 : ℕ) (row : Row) : ℕ := row.1.1 + base0 * row.1.2

/-- Linear adjacent-key checks imply that every two different indices have
different low-coordinate pairs. Interval endpoint data play no role. -/
theorem pair_injective_of_sorted (base0 : ℕ) (rows : List Row)
    (h : (rows.map (key base0)).IsChain (· < ·)) :
    Function.Injective (fun k : Fin rows.length => (rows.get k).1) := by
  have hm : StrictMono (fun k : Fin rows.length => key base0 (rows.get k)) := by
    intro a b hab
    have hp := List.isChain_iff_pairwise.mp h
    have hlt := List.pairwise_iff_getElem.mp hp a.val b.val
      (by simpa using a.isLt) (by simpa using b.isLt) hab
    simpa using hlt
  intro a b hab
  apply hm.injective
  exact congrArg (fun q : ℕ × ℕ => q.1 + base0 * q.2) hab

end Sarkozy.OddData
