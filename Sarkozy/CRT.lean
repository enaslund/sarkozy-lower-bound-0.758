import Sarkozy.Ranked

/-!
# Finite Chinese-remainder composition

Pairwise coprime moduli allow independently chosen ranked residues to be
combined. Cardinalities multiply, ranks add, and reverse-rank realization
gives a square-difference-free set of the resulting size.
-/

namespace Sarkozy

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The canonical CRT representative of a tuple of nonnegative residues.
Its behavior on negative input is immaterial to the construction. -/
noncomputable def crtResidue (M : ι → ℕ) (hM : ∀ i, 0 < M i)
    (hcop : Pairwise (fun i j => (M i).Coprime (M j))) (x : ι → ℤ) : ℤ :=
  (Nat.chineseRemainderOfFinset (fun i => (x i).toNat) M Finset.univ
    (fun i _ => ne_of_gt (hM i)) (fun _ _ _ _ hij => hcop hij)).val

theorem crtResidue_bounds (M : ι → ℕ) (hM : ∀ i, 0 < M i)
    (hcop : Pairwise (fun i j => (M i).Coprime (M j))) (x : ι → ℤ) :
    0 ≤ crtResidue M hM hcop x ∧ crtResidue M hM hcop x < (∏ i, M i : ℕ) := by
  constructor
  · exact Int.natCast_nonneg _
  · unfold crtResidue
    exact_mod_cast Nat.chineseRemainderOfFinset_lt_prod (fun i => (x i).toNat) M
      (fun i _ => ne_of_gt (hM i)) (fun i _ j _ hij => hcop hij)

/-- Each coordinate can be recovered by taking a remainder. -/
theorem crtResidue_emod (M : ι → ℕ) (hM : ∀ i, 0 < M i)
    (hcop : Pairwise (fun i j => (M i).Coprime (M j))) (x : ι → ℤ)
    (hx : ∀ i, 0 ≤ x i ∧ x i < M i) (i : ι) :
    crtResidue M hM hcop x % (M i : ℤ) = x i := by
  have heq := (Nat.chineseRemainderOfFinset (fun j => (x j).toNat) M Finset.univ
    (fun j _ => ne_of_gt (hM j)) (fun j _ k _ hjk => hcop hjk)).property i
    (Finset.mem_univ i)
  have heq' := Int.natCast_modEq_iff.mpr heq
  simpa only [crtResidue, Int.ModEq, Int.ofNat_toNat, max_eq_left (hx i).1,
    Int.emod_eq_of_lt (hx i).1 (hx i).2] using heq'

/-- All CRT combinations of the local finite sets. -/
noncomputable def crtResidueSet (C : ι → Finset ℤ) (M : ι → ℕ)
    (hM : ∀ i, 0 < M i) (hcop : Pairwise (fun i j => (M i).Coprime (M j))) :
    Finset ℤ := by
  classical
  exact Finset.univ.image (fun x : (i : ι) → {z // z ∈ C i} =>
    crtResidue M hM hcop (fun i => (x i).val))

/-- The combined rank is the sum of the ranks of the recovered coordinates. -/
noncomputable def crtRank (M : ι → ℕ) (r : ι → ℤ → ℤ) (x : ℤ) : ℤ :=
  ∑ i, r i (x % (M i : ℤ))

theorem crtResidueSet_card (C : ι → Finset ℤ) (M : ι → ℕ)
    (hM : ∀ i, 0 < M i) (hcop : Pairwise (fun i j => (M i).Coprime (M j)))
    (hcanonical : ∀ i, ∀ x ∈ C i, 0 ≤ x ∧ x < M i) :
    (crtResidueSet C M hM hcop).card = ∏ i, (C i).card := by
  classical
  unfold crtResidueSet
  rw [Finset.card_image_iff.mpr ?_]
  · simp only [Finset.card_univ, Fintype.card_pi, Fintype.card_coe]
  · intro x _ y _ hxy
    funext i
    apply Subtype.ext
    have heq := congrArg (fun z : ℤ => z % (M i : ℤ)) hxy
    simpa only [crtResidue_emod M hM hcop _
      (fun j => hcanonical j _ (x j).property),
      crtResidue_emod M hM hcop _ (fun j => hcanonical j _ (y j).property)] using heq

theorem crtResidueSet_canonical (C : ι → Finset ℤ) (M : ι → ℕ)
    (hM : ∀ i, 0 < M i) (hcop : Pairwise (fun i j => (M i).Coprime (M j))) :
    ∀ x ∈ crtResidueSet C M hM hcop, 0 ≤ x ∧ x < (∏ i, M i : ℕ) := by
  classical
  intro x hx
  obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
  exact crtResidue_bounds M hM hcop _

theorem crtResidueSet_coordinate (C : ι → Finset ℤ) (M : ι → ℕ)
    (hM : ∀ i, 0 < M i) (hcop : Pairwise (fun i j => (M i).Coprime (M j)))
    (hcanonical : ∀ i, ∀ x ∈ C i, 0 ≤ x ∧ x < M i)
    {x : ℤ} (hx : x ∈ crtResidueSet C M hM hcop) (i : ι) :
    x % (M i : ℤ) ∈ C i := by
  classical
  obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
  rw [crtResidue_emod M hM hcop _ (fun j => hcanonical j _ (y j).property)]
  exact (y i).property

theorem crtResidueSet_ext (C : ι → Finset ℤ) (M : ι → ℕ)
    (hM : ∀ i, 0 < M i) (hcop : Pairwise (fun i j => (M i).Coprime (M j)))
    (hcanonical : ∀ i, ∀ x ∈ C i, 0 ≤ x ∧ x < M i)
    {x y : ℤ} (hx : x ∈ crtResidueSet C M hM hcop)
    (hy : y ∈ crtResidueSet C M hM hcop)
    (heq : ∀ i, x % (M i : ℤ) = y % (M i : ℤ)) : x = y := by
  classical
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hy
  have hab : a = b := by
    funext i
    apply Subtype.ext
    simpa only [crtResidue_emod M hM hcop _
      (fun j => hcanonical j _ (a j).property),
      crtResidue_emod M hM hcop _ (fun j => hcanonical j _ (b j).property)] using heq i
  rw [hab]

/-- Modular square differences project to modular square differences. -/
theorem squareDifference_emod {M P x y z : ℤ} (hMP : M ∣ P)
    (hsq : P ∣ y - x - z ^ 2) : M ∣ y % M - x % M - z ^ 2 := by
  have hproj := hMP.trans hsq
  have hmod : y % M - x % M - z ^ 2 ≡ y - x - z ^ 2 [ZMOD M] :=
    ((Int.mod_modEq y M).sub (Int.mod_modEq x M)).sub Int.ModEq.rfl
  exact Int.modEq_zero_iff_dvd.mp (hmod.trans hproj.modEq_zero_int)

/-- CRT composition preserves the strict rank condition: every coordinate
rank is nondecreasing and at least one increases. -/
theorem crtResidueSet_ranked (C : ι → Finset ℤ) (M : ι → ℕ)
    (r : ι → ℤ → ℤ) (hM : ∀ i, 0 < M i)
    (hcop : Pairwise (fun i j => (M i).Coprime (M j)))
    (hcanonical : ∀ i, ∀ x ∈ C i, 0 ≤ x ∧ x < M i)
    (hranked : ∀ i, RankedModulo (C i) (M i) (r i)) :
    RankedModulo (crtResidueSet C M hM hcop) (∏ i, M i : ℕ) (crtRank M r) := by
  classical
  intro x hx y hy hxy hsquare
  obtain ⟨z, hz⟩ := hsquare
  have hxm := crtResidueSet_coordinate C M hM hcop hcanonical hx
  have hym := crtResidueSet_coordinate C M hM hcop hcanonical hy
  have hlocal (i : ι) : (M i : ℤ) ∣ y % (M i : ℤ) - x % (M i : ℤ) - z ^ 2 := by
    apply squareDifference_emod _ hz
    exact_mod_cast Finset.dvd_prod_of_mem M (Finset.mem_univ i)
  have hstrict (i : ι) (hi : x % (M i : ℤ) ≠ y % (M i : ℤ)) :
      r i (x % (M i : ℤ)) < r i (y % (M i : ℤ)) :=
    hranked i _ (hxm i) _ (hym i) hi ⟨z, hlocal i⟩
  have hle (i : ι) : r i (x % (M i : ℤ)) ≤ r i (y % (M i : ℤ)) := by
    by_cases hi : x % (M i : ℤ) = y % (M i : ℤ)
    · rw [hi]
    · exact (hstrict i hi).le
  have hsome : ∃ i, x % (M i : ℤ) ≠ y % (M i : ℤ) := by
    by_contra! heq
    exact hxy (crtResidueSet_ext C M hM hcop hcanonical hx hy heq)
  obtain ⟨i, hi⟩ := hsome
  exact Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ i, hstrict i hi⟩

theorem crtRank_bounds (C : ι → Finset ℤ) (M : ι → ℕ)
    (r : ι → ℤ → ℤ) (K : ι → ℤ) (hM : ∀ i, 0 < M i)
    (hcop : Pairwise (fun i j => (M i).Coprime (M j)))
    (hcanonical : ∀ i, ∀ x ∈ C i, 0 ≤ x ∧ x < M i)
    (hrange : ∀ i, ∀ x ∈ C i, 0 ≤ r i x ∧ r i x ≤ K i)
    {x : ℤ} (hx : x ∈ crtResidueSet C M hM hcop) :
    0 ≤ crtRank M r x ∧ crtRank M r x ≤ ∑ i, K i := by
  have hm := crtResidueSet_coordinate C M hM hcop hcanonical hx
  exact ⟨Finset.sum_nonneg (fun i _ => (hrange i _ (hm i)).1),
    Finset.sum_le_sum (fun i _ => (hrange i _ (hm i)).2)⟩

/-- The finite-family construction. Each local residue is retained independently;
the integer set has product cardinality and lies in the claimed interval. -/
theorem crt_reverseRank_realization (C : ι → Finset ℤ) (M : ι → ℕ)
    (r : ι → ℤ → ℤ) (K : ι → ℤ) (hM : ∀ i, 0 < M i)
    (hcop : Pairwise (fun i j => (M i).Coprime (M j)))
    (hcanonical : ∀ i, ∀ x ∈ C i, 0 ≤ x ∧ x < M i)
    (hrange : ∀ i, ∀ x ∈ C i, 0 ≤ r i x ∧ r i x ≤ K i)
    (hranked : ∀ i, RankedModulo (C i) (M i) (r i)) :
    ∃ A : Finset ℤ,
      A.card = ∏ i, (C i).card ∧
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ (∏ i, M i : ℕ) * ((∑ i, K i) + 1)) ∧
      SquareDifferenceFree A := by
  have hprod : (0 : ℤ) < (∏ i, M i : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => hM i)
  obtain ⟨A, hcard, hbound, hfree⟩ := reverseRank_realization
    (crtResidueSet C M hM hcop) (∏ i, M i : ℕ) (∑ i, K i) (crtRank M r)
    hprod (crtResidueSet_canonical C M hM hcop)
    (fun _ hx => crtRank_bounds C M r K hM hcop hcanonical hrange hx)
    (crtResidueSet_ranked C M r hM hcop hcanonical hranked)
  exact ⟨A, hcard.trans (crtResidueSet_card C M hM hcop hcanonical), hbound, hfree⟩

end Sarkozy
