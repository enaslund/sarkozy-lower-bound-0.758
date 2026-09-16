import Sarkozy.OddCertificate

/-!
# Compressed checks for odd low-word edge ordering

A pre mask may overestimate its source set. Checking membership of each
source in its own prime-specific pre masks is sufficient: the two masks
of possible predecessors are intersected, and every retained source other
than the target must lie before a certified endpoint cutoff.
-/

namespace Sarkozy.OddOrder

/-- Union of finite sets represented by natural-number bit masks. -/
def maskUnion (xs : List ℕ) : ℕ := xs.foldr (fun a b => a ||| b) 0

theorem testBit_maskUnion (xs : List ℕ) (i : ℕ) :
    (maskUnion xs).testBit i = true ↔ ∃ m ∈ xs, m.testBit i = true := by
  induction xs with
  | nil => simp [maskUnion]
  | cons x xs ih =>
      change (x ||| maskUnion xs).testBit i = true ↔ _
      simp [Nat.testBit_or, ih]

/-- Integer residue selected by a square root at a first differing digit. -/
def candidate (p : ℕ) (b : ℤ) (z : ℕ) : ℤ :=
  (b % (p : ℤ) - (z : ℤ)^2) % (p : ℤ)

theorem candidate_eq_of_square (p : ℕ) (a b : ℤ) (z : ℕ)
    (h : (p : ℤ) ∣ b % (p : ℤ) - a % (p : ℤ) - (z : ℤ)^2) :
    candidate p b z = a % (p : ℤ) := by
  have hd : (p : ℤ) ∣ (b % (p : ℤ) - (z : ℤ)^2) - a % (p : ℤ) := by
    convert h using 1 <;> ring
  have hm := Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    (Int.dvd_iff_emod_eq_zero.mp hd)
  simpa [candidate] using hm

/-- Check that a source's bit occurs in all its nonempty low-digit prefixes.
The zero-depth case checks the supplied pre itself. -/
def sourceCovered (G : List ℤ → ℕ) (p : ℕ) : ℕ → ℤ → List ℤ → ℕ → Bool
  | 0, _, pre, i => (G pre).testBit i
  | e + 1, a, pre, i =>
      let next := pre ++ [a % (p : ℤ)]
      (G next).testBit i && sourceCovered G p e (a / (p : ℤ)) next i

/-- Overapproximate the sources related to the target at this prime.
Equal digits recurse; all finite square-root witnesses at a different digit
contribute the matching pre mask. -/
def predecessors (G : List ℤ → ℕ) (p : ℕ) : ℕ → ℤ → List ℤ → ℕ
  | 0, _, pre => G pre
  | e + 1, b, pre =>
      maskUnion ((List.range p).map fun z =>
        if candidate p b z = b % (p : ℤ) then 0
        else G (pre ++ [candidate p b z])) |||
      predecessors G p e (b / (p : ℤ)) (pre ++ [b % (p : ℤ)])

/-- Prefix containment alone makes the predecessor mask sound. It need not
be an exact partition, and equality of low words remains permitted. -/
theorem predecessors_sound (G : List ℤ → ℕ) (p e : ℕ) (a b : ℤ)
    (pre : List ℤ) (i : ℕ)
    (hc : sourceCovered G p e a pre i = true)
    (hr : PrimeLowFinite p e a b) :
    (predecessors G p e b pre).testBit i = true := by
  induction e generalizing a b pre with
  | zero => exact hc
  | succ e ih =>
      have hs := Bool.and_eq_true_iff.mp hc
      rw [predecessors, Nat.testBit_or, Bool.or_eq_true]
      by_cases hab : a % (p : ℤ) = b % (p : ℤ)
      · right
        have ht : PrimeLowFinite p e (a / (p : ℤ)) (b / (p : ℤ)) := by
          simpa only [PrimeLowFinite, if_pos hab] using hr
        apply ih _ _ _ ?_ ht
        simpa only [hab] using hs.2
      · left
        have ht : FiniteSquareResidue p (b % (p : ℤ) - a % (p : ℤ)) := by
          simpa only [PrimeLowFinite, if_neg hab] using hr
        obtain ⟨z,hz⟩ := ht
        have hz' := candidate_eq_of_square p a b z.val hz
        have hne : candidate p b z.val ≠ b % (p : ℤ) := by simpa only [hz'] using hab
        apply (testBit_maskUnion _ _).mpr
        refine ⟨G (pre ++ [candidate p b z.val]), ?_, ?_⟩
        · apply List.mem_map.mpr
          refine ⟨z.val, List.mem_range.mpr z.isLt, ?_⟩
          simp only [if_neg hne]
        · simpa only [hz'] using hs.1

/-- A mask is contained in the interval pre plus the target's own bit. -/
def belowOrSelf (mask cutoff target : ℕ) : Bool :=
  decide (mask &&& ((2^cutoff - 1) ||| 2^target) = mask)

theorem belowOrSelf_sound (mask cutoff target source : ℕ)
    (h : belowOrSelf mask cutoff target = true)
    (hm : mask.testBit source = true) : source < cutoff ∨ source = target := by
  have he : mask &&& ((2^cutoff - 1) ||| 2^target) = mask := of_decide_eq_true h
  have hb := congrArg (fun m : ℕ => m.testBit source) he
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_two_pow_sub_one,
    Nat.testBit_two_pow, hm, Bool.true_and, Bool.or_eq_true, decide_eq_true_eq] at hb
  exact hb.elim Or.inl (fun hs => Or.inr hs.symm)

/-- Generic order certificate after sources have been indexed by increasing
right endpoint. Only one endpoint comparison is needed for each target. -/
theorem interval_order_of_masks
    (n : ℕ) (p : Fin 2 → ℕ) (hp : ∀ c, 0 < p c) (e : ℕ)
    (point : Fin n → Fin 2 → ℤ) (start width : Fin n → ℕ)
    (G : Fin 2 → List ℤ → ℕ) (cutoff : Fin n → Fin (n+1))
    (hend : Monotone (fun k => start k + width k))
    (hcut : ∀ k, ∀ h : 0 < (cutoff k).val,
      start ⟨(cutoff k).val - 1, by have := (cutoff k).isLt; omega⟩ +
      width ⟨(cutoff k).val - 1, by have := (cutoff k).isLt; omega⟩ ≤ start k)
    (hcovered : ∀ k c, sourceCovered (G c) (p c) e (point k c) [] k.val = true)
    (hchecked : ∀ k, belowOrSelf
      (predecessors (G 0) (p 0) e (point k 0) [] &&&
        predecessors (G 1) (p 1) e (point k 1) []) (cutoff k).val k.val = true) :
    ∀ k l, k ≠ l →
      (∀ c, PrimeLowRelated (p c) e (point k c) (point l c)) →
      start k + width k ≤ start l := by
  intro k l hne hrel
  have hbit (c : Fin 2) := predecessors_sound (G c) (p c) e (point k c)
    (point l c) [] k.val (hcovered k c)
    ((primeLowFinite_iff (p c) (hp c) e _ _).mpr (hrel c))
  have hboth : (predecessors (G 0) (p 0) e (point l 0) [] &&&
      predecessors (G 1) (p 1) e (point l 1) []).testBit k.val = true := by
    simp only [Nat.testBit_and, hbit, Bool.true_and]
  have hlt : k.val < (cutoff l).val := by
    rcases belowOrSelf_sound _ _ _ _ (hchecked l) hboth with h | h
    · exact h
    · exact False.elim (hne (Fin.ext h))
  have hpos : 0 < (cutoff l).val := by omega
  exact (hend (show k ≤ ⟨(cutoff l).val - 1, by have := (cutoff l).isLt; omega⟩
    from by change k.val ≤ (cutoff l).val - 1; omega)).trans (hcut l hpos)

end Sarkozy.OddOrder
