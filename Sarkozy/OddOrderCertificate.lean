import Sarkozy.OddOrder
import Sarkozy.OddData

/-!
# Executable representation of compressed odd order certificates

Balanced lookup trees are arbitrary finite data. Their shape need not be
verified: the source checks establish the prefix containment and endpoint
identities required by the mathematical argument. All large-row passes are
sequential, avoiding quadratic repeated list access during kernel reduction.
-/

namespace Sarkozy.OddOrder

inductive MaskTree where
  | empty
  | node (left : MaskTree) (key value : ℕ) (right : MaskTree)

def MaskTree.lookup : MaskTree → ℕ → ℕ
  | .empty, _ => 0
  | .node left key value right, query =>
      if query < key then left.lookup query
      else if key < query then right.lookup query else value

/-- A sentinel digit distinguishes prefixes of different lengths. No
injectivity theorem for this encoding is needed by the conservative checker. -/
def prefixCode (p : ℕ) (digits : List ℤ) : ℕ :=
  digits.foldl (fun acc digit => p * acc + digit.toNat) 1

def prefixLookup (p : ℕ) (table : MaskTree) (digits : List ℤ) : ℕ :=
  table.lookup (prefixCode p digits)

/-- A low-point/interval row and its proposed predecessor cutoff. -/
abbrev Entry := OddData.Row × ℕ

def entryPoint (r : Entry) (c : Fin 2) : ℤ := ![(r.1.1.1 : ℤ), (r.1.1.2 : ℤ)] c

def entryStart (r : Entry) : ℕ := r.1.2.1

def entryWidth (r : Entry) : ℕ := r.1.2.2

def entryEnd (r : Entry) : ℕ := entryStart r + entryWidth r

/-- A sequential finite universal check with an explicitly tracked index. -/
def allIndexed {α : Type} (P : ℕ → α → Bool) : ℕ → List α → Bool
  | _, [] => true
  | offset, a :: as => P offset a && allIndexed P (offset+1) as

theorem allIndexed_sound {α : Type} (P : ℕ → α → Bool)
    (offset : ℕ) (as : List α) (h : allIndexed P offset as = true)
    (k : ℕ) (hk : k < as.length) : P (offset+k) as[k] = true := by
  induction as generalizing offset k with
  | nil => simp at hk
  | cons a as ih =>
      have hs := Bool.and_eq_true_iff.mp h
      cases k with
      | zero => simpa using hs.1
      | succ k =>
          have hr := ih (offset+1) hs.2 k (by simpa using hk)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr

def sourceCheck (p0 p1 e : ℕ) (G0 G1 : List ℤ → ℕ) (E : MaskTree)
    (i : ℕ) (r : Entry) : Bool :=
  sourceCovered G0 p0 e (entryPoint r 0) [] i &&
    (sourceCovered G1 p1 e (entryPoint r 1) [] i &&
      decide (E.lookup i = entryEnd r))

def targetCheck (n p0 p1 e : ℕ) (G0 G1 : List ℤ → ℕ) (E : MaskTree)
    (i : ℕ) (r : Entry) : Bool :=
  decide (r.2 ≤ n) &&
    ((decide (r.2 = 0) || decide (E.lookup (r.2-1) ≤ entryStart r)) &&
      belowOrSelf (predecessors G0 p0 e (entryPoint r 0) [] &&&
        predecessors G1 p1 e (entryPoint r 1) []) r.2 i)

/-- Successful finite checks imply every semantic two-prime square edge has
its source interval entirely before its target interval. -/
theorem interval_order_of_checked_rows
    (p0 p1 e : ℕ) (hp0 : 0 < p0) (hp1 : 0 < p1)
    (rows : List Entry) (G0 G1 : List ℤ → ℕ) (E : MaskTree)
    (hsource : allIndexed (sourceCheck p0 p1 e G0 G1 E) 0 rows = true)
    (htarget : allIndexed (targetCheck rows.length p0 p1 e G0 G1 E) 0 rows = true)
    (hsorted : (rows.map entryEnd).IsChain (· ≤ ·)) :
    ∀ k l : Fin rows.length, k ≠ l →
      (∀ c : Fin 2, PrimeLowRelated (![p0,p1] c) e
        (entryPoint (rows.get k) c) (entryPoint (rows.get l) c)) →
      entryEnd (rows.get k) ≤ entryStart (rows.get l) := by
  have hs (k : Fin rows.length) :
      sourceCovered G0 p0 e (entryPoint (rows.get k) 0) [] k.val = true ∧
      sourceCovered G1 p1 e (entryPoint (rows.get k) 1) [] k.val = true ∧
      E.lookup k.val = entryEnd (rows.get k) := by
    have h := allIndexed_sound _ 0 rows hsource k.val k.isLt
    simpa only [Nat.zero_add, List.get_eq_getElem, sourceCheck, Bool.and_eq_true, decide_eq_true_eq] using h
  have ht (k : Fin rows.length) :
      (rows.get k).2 ≤ rows.length ∧
      ((rows.get k).2 = 0 ∨ E.lookup ((rows.get k).2-1) ≤ entryStart (rows.get k)) ∧
      belowOrSelf (predecessors G0 p0 e (entryPoint (rows.get k) 0) [] &&&
        predecessors G1 p1 e (entryPoint (rows.get k) 1) []) (rows.get k).2 k.val = true := by
    have h := allIndexed_sound _ 0 rows htarget k.val k.isLt
    simpa only [Nat.zero_add, List.get_eq_getElem, targetCheck, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq] using h
  let cut : Fin rows.length → Fin (rows.length+1) := fun k => ⟨(rows.get k).2, by
    have := (ht k).1
    omega⟩
  have hm : Monotone (fun k : Fin rows.length => entryEnd (rows.get k)) := by
    apply monotone_iff_forall_lt.mpr
    intro a b hab
    have hp := List.isChain_iff_pairwise.mp hsorted
    have hlt := List.pairwise_iff_getElem.mp hp a.val b.val
      (by simpa using a.isLt) (by simpa using b.isLt) hab
    simpa using hlt
  apply interval_order_of_masks rows.length ![p0,p1] (by
    intro c
    fin_cases c
    · exact hp0
    · exact hp1) e (fun k c => entryPoint (rows.get k) c)
      (fun k => entryStart (rows.get k)) (fun k => entryWidth (rows.get k))
      ![G0,G1] cut hm
  · intro k hpos
    have hb := (ht k).2.1
    have hne : (rows.get k).2 ≠ 0 := by
      change 0 < (rows.get k).2 at hpos
      omega
    have he := (hs ⟨(cut k).val-1, by have := (cut k).isLt; omega⟩).2.2
    change E.lookup ((rows.get k).2-1) = _ at he
    change entryEnd (rows.get _) ≤ entryStart (rows.get k)
    rw [← he]
    exact hb.resolve_left hne
  · intro k c
    fin_cases c
    · exact (hs k).1
    · exact (hs k).2.1
  · intro k
    exact (ht k).2.2

/-- Equal low words are related at every depth. -/
theorem primeLowRelated_refl (p : ℤ) (e : ℕ) (a : ℤ) : PrimeLowRelated p e a a := by
  induction e generalizing a with
  | zero => trivial
  | succ e ih => simpa only [PrimeLowRelated, ite_true] using ih (a/p)

/-- An ordered positive-width certificate cannot contain duplicate low points. -/
theorem point_injective_of_order (n : ℕ) (p : Fin 2 → ℕ) (e : ℕ)
    (point : Fin n → Fin 2 → ℤ) (start width : Fin n → ℕ)
    (hwidth : ∀ k, 0 < width k)
    (horder : ∀ k l, k ≠ l →
      (∀ c, PrimeLowRelated (p c) e (point k c) (point l c)) →
      start k + width k ≤ start l) : Function.Injective point := by
  intro k l heq
  by_contra hne
  have hrel (c : Fin 2) : PrimeLowRelated (p c) e (point k c) (point l c) := by
    rw [congrFun heq c]
    exact primeLowRelated_refl _ _ _
  have hrev (c : Fin 2) : PrimeLowRelated (p c) e (point l c) (point k c) := by
    rw [congrFun heq c]
    exact primeLowRelated_refl _ _ _
  have hf := horder k l hne hrel
  have hb := horder l k (Ne.symm hne) hrev
  have hp := hwidth k
  omega

end Sarkozy.OddOrder
