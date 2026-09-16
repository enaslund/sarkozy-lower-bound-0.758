import Sarkozy.OddLift

/-!
# Finite reflection for the odd-prime low-word relation

The conceptual lifting theorem quantifies over arbitrary integer square roots.
For certificate checking, each root can be reduced to the canonical interval
`[0,p)`. This file proves that replacement, and a recursive decidable relation
with exactly the same first-differing-digit semantics.
-/

namespace Sarkozy

/-- A finite witness that an integer is a square modulo `p`. -/
def FiniteSquareResidue (p : ℕ) (a : ℤ) : Prop :=
  ∃ z : Fin p, (p : ℤ) ∣ a - (z.val : ℤ) ^ 2

instance (p : ℕ) (a : ℤ) : Decidable (FiniteSquareResidue p a) :=
  inferInstanceAs (Decidable (∃ z : Fin p, (p : ℤ) ∣ a - (z.val : ℤ) ^ 2))

/-- Reducing an arbitrary integer square root modulo `p` is complete. -/
theorem finiteSquareResidue_iff (p : ℕ) (hp : 0 < p) (a : ℤ) :
    FiniteSquareResidue p a ↔ ∃ z : ℤ, (p : ℤ) ∣ a - z ^ 2 := by
  constructor
  · rintro ⟨z,hz⟩
    exact ⟨z.val,hz⟩
  · rintro ⟨z,hz⟩
    have hpz : (0 : ℤ) < p := by exact_mod_cast hp
    have hr0 := Int.emod_nonneg z (ne_of_gt hpz)
    have hr1 := Int.emod_lt_of_pos z hpz
    let r : Fin p := ⟨(z % (p : ℤ)).toNat, by omega⟩
    have hr : (r.val : ℤ) = z % (p : ℤ) := by
      dsimp [r]
      exact Int.toNat_of_nonneg hr0
    refine ⟨r, ?_⟩
    apply Int.dvd_iff_emod_eq_zero.mpr
    rw [hr]
    have hmod := Int.dvd_iff_emod_eq_zero.mp hz
    simpa only [pow_two, Int.sub_emod, Int.mul_emod, Int.emod_emod] using hmod

/-- Decidable low-word square relation; equality recurses independently in
this prime coordinate and a first difference uses a finite square witness. -/
def PrimeLowFinite (p : ℕ) : ℕ → ℤ → ℤ → Prop
  | 0, _, _ => True
  | e + 1, a, b =>
      if a % (p : ℤ) = b % (p : ℤ) then
        PrimeLowFinite p e (a / (p : ℤ)) (b / (p : ℤ))
      else FiniteSquareResidue p (b % (p : ℤ) - a % (p : ℤ))

instance primeLowFiniteDecidable (p e : ℕ) (a b : ℤ) :
    Decidable (PrimeLowFinite p e a b) := by
  induction e generalizing a b with
  | zero => exact isTrue trivial
  | succ e ih =>
      unfold PrimeLowFinite
      exact dite _ (fun h => by rw [if_pos h]; exact ih _ _)
        (fun h => by rw [if_neg h]; infer_instance)

/-- The finite checker preserves the conceptual relation exactly. No primality
assumption is needed for this reflection step. -/
theorem primeLowFinite_iff (p : ℕ) (hp : 0 < p) (e : ℕ) (a b : ℤ) :
    PrimeLowFinite p e a b ↔ PrimeLowRelated (p : ℤ) e a b := by
  induction e generalizing a b with
  | zero => rfl
  | succ e ih =>
      simp only [PrimeLowFinite, PrimeLowRelated]
      split_ifs with h
      · exact ih _ _
      · exact finiteSquareResidue_iff p hp _

end Sarkozy
