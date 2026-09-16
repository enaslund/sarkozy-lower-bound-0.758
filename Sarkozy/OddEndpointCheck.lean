import Sarkozy.OddOrderCertificate

/-!
# Boolean checking of adjacent endpoint inequalities

The Boolean check separates finite computation from construction of the
proposition's recursive decidability proof. The soundness theorem is generic;
its use does not expand one proof constructor for every concrete row.
-/

namespace Sarkozy.OddOrder

/-- Every consecutive pair of natural endpoints is nondecreasing. -/
def adjacentLE : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: xs => decide (a ≤ b) && adjacentLE (b :: xs)

/-- Accepted adjacent comparisons give the usual mathematical chain. -/
theorem adjacentLE_sound (xs : List ℕ) :
    adjacentLE xs = true → xs.IsChain (· ≤ ·) := by
  induction xs with
  | nil => intro _; exact .nil
  | cons a xs ih =>
      cases xs with
      | nil => intro _; exact .singleton _
      | cons b xs =>
          intro h
          change (decide (a ≤ b) && adjacentLE (b :: xs)) = true at h
          have hh := Bool.and_eq_true_iff.mp h
          exact .cons_cons (of_decide_eq_true hh.1) (ih hh.2)

end Sarkozy.OddOrder
