import Sarkozy.OddData
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Sort

/-!
# Transporting odd width moments through a histogram

The geometry certificate keeps a point, start and width in each row. A moment
depends only on the multiset of widths. These lemmas connect the indexed rows
to a histogram whose entries are `(widthNumerator, multiplicity)`.

Equality of merge-sorted lists is a convenient finite kernel check for the
multiset comparison. No computation of the more expensive `List.Perm`
decision procedure is required. These transport lemmas impose no restrictions
on the denominator or power; numerical lower bounds remain separate.
-/

namespace Sarkozy.OddMoments

open scoped BigOperators

/-- Expand a width histogram, with width first and multiplicity second. -/
def histogramExpansion (hist : List (ℕ × ℕ)) : List ℕ :=
  hist.flatMap (fun wc => List.replicate wc.2 wc.1)

/-- A sorted-list equality proves multiset equality for any Boolean comparator.
The comparator itself needs no order laws for this implication. -/
theorem perm_of_mergeSort_eq {α : Type*} (le : α → α → Bool) (a b : List α)
    (h : a.mergeSort le = b.mergeSort le) : a.Perm b := by
  have hs : (a.mergeSort le).Perm b := by
    rw [h]
    exact List.mergeSort_perm b le
  exact (List.mergeSort_perm a le).symm.trans hs

/-- Passing from the certificate's fixed `Fin n` indexing to its row list
preserves the sum of any real-valued row function. -/
theorem indexed_sum_eq_list {α : Type*} (rows : List α) {n : ℕ}
    (hsize : rows.length = n) (g : α → ℝ) :
    (∑ k : Fin n, g (rows.get (Fin.cast hsize.symm k))) = (rows.map g).sum := by
  subst n
  simpa using (Fin.sum_univ_fun_getElem rows g)

/-- The indexed moment is the sum over the row list's width numerators. -/
theorem indexed_width_moment_eq_list (rows : List OddData.Row) {n : ℕ}
    (hsize : rows.length = n) (D : ℕ) (f : ℝ) :
    (∑ k : Fin n, (((rows.get (Fin.cast hsize.symm k)).2.2 : ℝ) / D)^f) =
      ((rows.map (fun row => row.2.2)).map (fun w : ℕ => ((w : ℝ) / D)^f)).sum := by
  simpa only [List.map_map, Function.comp_def] using
    indexed_sum_eq_list rows hsize (fun row => ((row.2.2 : ℝ) / D)^f)

/-- Expanding a histogram and summing a function agrees with weighting that
function by the multiplicity of each histogram entry. -/
theorem histogram_sum_eq_weighted (hist : List (ℕ × ℕ)) (g : ℕ → ℝ) :
    ((histogramExpansion hist).map g).sum =
      (hist.map (fun wc => (wc.2 : ℝ) * g wc.1)).sum := by
  induction hist with
  | nil => simp [histogramExpansion]
  | cons wc hist ih =>
    simpa [histogramExpansion, nsmul_eq_mul] using
      congrArg (fun z => (wc.2 : ℝ) * g wc.1 + z) ih

/-- Real-power moments take the same multiplicity-weighted form. -/
theorem histogram_moment_eq_weighted (hist : List (ℕ × ℕ)) (D : ℕ) (f : ℝ) :
    ((histogramExpansion hist).map (fun w : ℕ => ((w : ℝ) / D)^f)).sum =
      (hist.map (fun wc => (wc.2 : ℝ) * ((wc.1 : ℝ) / D)^f)).sum :=
  histogram_sum_eq_weighted hist (fun w : ℕ => ((w : ℝ) / D)^f)

/-- A kernel-checked equality of sorted width lists transports the complete
indexed moment to its histogram, without changing the geometry row order. -/
theorem indexed_width_moment_eq_histogram (rows : List OddData.Row) {n : ℕ}
    (hsize : rows.length = n) (hist : List (ℕ × ℕ)) (D : ℕ) (f : ℝ)
    (hsorted : (rows.map (fun row => row.2.2)).mergeSort (fun a b => a ≤ b) =
      (histogramExpansion hist).mergeSort (fun a b => a ≤ b)) :
    (∑ k : Fin n, (((rows.get (Fin.cast hsize.symm k)).2.2 : ℝ) / D)^f) =
      (hist.map (fun wc => (wc.2 : ℝ) * ((wc.1 : ℝ) / D)^f)).sum := by
  rw [indexed_width_moment_eq_list rows hsize D f]
  have hp := perm_of_mergeSort_eq (fun a b : ℕ => a ≤ b)
    (rows.map (fun row => row.2.2)) (histogramExpansion hist) hsorted
  exact ((hp.map (fun w : ℕ => ((w : ℝ) / D)^f)).sum_eq).trans
    (histogram_moment_eq_weighted hist D f)

end Sarkozy.OddMoments
