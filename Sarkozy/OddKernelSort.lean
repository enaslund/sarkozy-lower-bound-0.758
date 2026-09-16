import Mathlib.Data.List.Sort

/-!
# A kernel-reducible multiset check for width lists

The pinned Lean library's well-founded sorting implementation does not reduce
in the kernel at the required concrete equality check. This small sorter uses
structural recursion only. Its output is proved to be a permutation of its
input for every fuel, so even insufficient fuel cannot validate a false
multiset equality. No sortedness theorem for this implementation is needed.
-/

namespace Sarkozy.OddKernelSort

/-- A structural split with no dependent lengths or termination proofs. -/
def split : ℕ → List ℕ → List ℕ × List ℕ
  | 0, xs => ([], xs)
  | _+1, [] => ([], [])
  | n+1, x::xs => let halves := split n xs; (x::halves.1, halves.2)

theorem split_append (n : ℕ) (xs : List ℕ) :
    (split n xs).1 ++ (split n xs).2 = xs := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    cases xs with
    | nil => rfl
    | cons x xs => simp only [split, List.cons_append, ih]

/-- Fuelled merge; exhaustion preserves the remaining entries by appending. -/
def merge : ℕ → List ℕ → List ℕ → List ℕ
  | 0, xs, ys => xs ++ ys
  | _+1, [], ys => ys
  | _+1, xs, [] => xs
  | n+1, x::xs, y::ys =>
    if x ≤ y then x::merge n xs (y::ys) else y::merge n (x::xs) ys

theorem merge_perm (fuel : ℕ) (xs ys : List ℕ) :
    (merge fuel xs ys).Perm (xs ++ ys) := by
  induction fuel generalizing xs ys with
  | zero => exact List.Perm.refl _
  | succ fuel ih =>
    cases xs with
    | nil => simp [merge]
    | cons x xs =>
      cases ys with
      | nil => simp [merge]
      | cons y ys =>
        simp only [merge]
        split
        · exact (ih xs (y::ys)).cons x
        · exact ((ih (x::xs) ys).cons y).trans List.perm_middle.symm

/-- Merge-sort recursion consumes explicit fuel, avoiding well-founded
recursors. Equal outputs certify equal multisets at any fuel value. -/
def sort : ℕ → List ℕ → List ℕ
  | 0, xs => xs
  | _+1, [] => []
  | _+1, [x] => [x]
  | fuel+1, x::y::xs =>
    let halves := split ((x::y::xs).length / 2) (x::y::xs)
    let left := sort fuel halves.1
    let right := sort fuel halves.2
    merge (x::y::xs).length left right

theorem sort_perm (fuel : ℕ) (xs : List ℕ) : (sort fuel xs).Perm xs := by
  induction fuel generalizing xs with
  | zero => exact List.Perm.refl _
  | succ fuel ih =>
    cases xs with
    | nil => exact List.Perm.refl _
    | cons x xs =>
      cases xs with
      | nil => exact List.Perm.refl _
      | cons y xs =>
        unfold sort
        exact (merge_perm _ _ _).trans
          (((ih _).append (ih _)).trans (List.Perm.of_eq (split_append _ _)))

theorem perm_of_sort_eq (fuel : ℕ) (xs ys : List ℕ)
    (h : sort fuel xs = sort fuel ys) : xs.Perm ys := by
  have hs : (sort fuel xs).Perm ys := by rw [h]; exact sort_perm fuel ys
  exact (sort_perm fuel xs).symm.trans hs

/-- If the comparison list is already in the desired order, only one sort is
needed. No sortedness hypothesis is required for soundness. -/
theorem perm_of_sort_eq_list (fuel : ℕ) (xs ys : List ℕ)
    (h : sort fuel xs = ys) : xs.Perm ys :=
  (sort_perm fuel xs).symm.trans (List.Perm.of_eq h)

example : sort 2 [3, 2, 1] = [1, 2, 3] := by decide +kernel

end Sarkozy.OddKernelSort
