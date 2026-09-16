import Sarkozy.Intervals
import Sarkozy.CRT
import Sarkozy.FiniteAlphabets

/-!
# Interleaving restricted and free prime-adic digits

The restricted low word and the free word are represented as canonical
base-`p` integers. Their digits occupy the even and odd positions,
respectively. The low-word relation is inspected separately at each prime.
-/

namespace Sarkozy

/-- Interleave the first `e` base-`p` digits of `a` and `u`. -/
def oddInterleave (p : ℤ) : ℕ → ℤ → ℤ → ℤ
  | 0, _, _ => 0
  | e + 1, a, u => a % p + p * (u % p) + p ^ 2 * oddInterleave p e (a / p) (u / p)

/-- Equal low words are allowed. Otherwise inspect their first different
base-`p` digit, starting at the least significant position. -/
def PrimeLowRelated (p : ℤ) : ℕ → ℤ → ℤ → Prop
  | 0, _, _ => True
  | e + 1, a, b =>
      if a % p = b % p then PrimeLowRelated p e (a / p) (b / p)
      else ∃ z : ℤ, p ∣ (b % p - a % p - z ^ 2)

/-- A common restricted digit forces the first free digits to agree.
After cancelling them, the remaining difference is again a modular square. -/
theorem odd_free_digit_descent (p P u v x y : ℤ)
    (hp : Prime p) (hpos : 0 < p)
    (hu : 0 ≤ u ∧ u < p) (hv : 0 ≤ v ∧ v < p)
    (hs : ∃ z : ℤ, p ^ 2 * P ∣ (p * (v - u) + p ^ 2 * (y - x) - z ^ 2)) :
    u = v ∧ ∃ z : ℤ, P ∣ (y - x - z ^ 2) := by
  obtain ⟨z,t,ht⟩ := hs
  have hpz : p ∣ z := by
    apply hp.dvd_of_dvd_pow (n := 2)
    refine ⟨v - u + p * (y - x) - p * P * t, ?_⟩
    nlinarith [ht]
  obtain ⟨z, rfl⟩ := hpz
  have heq : v - u = p * (P * t - y + x + z ^ 2) := by
    have hmul : p * (v - u) = p * (p * (P * t - y + x + z ^ 2)) := by
      nlinarith [ht]
    exact mul_left_cancel₀ (ne_of_gt hpos) hmul
  have huv : u = v := by
    have hmod : v % p = u % p := Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
      (Int.dvd_iff_emod_eq_zero.mp ⟨P * t - y + x + z ^ 2, heq⟩)
    simpa only [Int.emod_eq_of_lt hu.1 hu.2, Int.emod_eq_of_lt hv.1 hv.2] using hmod.symm
  refine ⟨huv, z, t, ?_⟩
  have hmul : p ^ 2 * (y - x - z ^ 2) = p ^ 2 * (P * t) := by
    rw [huv] at ht
    nlinarith [ht]
  exact mul_left_cancel₀ (pow_ne_zero 2 (ne_of_gt hpos)) hmul

theorem odd_tail_canonical (p a : ℤ) (e : ℕ) (hpos : 0 < p)
    (ha : 0 ≤ a ∧ a < p ^ (e + 1)) :
    0 ≤ a / p ∧ a / p < p ^ e := by
  refine ⟨Int.ediv_nonneg ha.1 hpos.le, ?_⟩
  apply (Int.ediv_lt_iff_lt_mul hpos).mpr
  simpa only [pow_succ] using ha.2

theorem odd_modulus_succ (p : ℤ) (e : ℕ) :
    p ^ (2 * (e + 1)) = p ^ 2 * p ^ (2 * e) := by
  rw [show 2 * (e + 1) = 2 + 2 * e by omega, pow_add]

/-- Interleaving always produces a canonical residue, even if its inputs
have extra digits beyond the specified depth. -/
theorem oddInterleave_bounds (p : ℤ) (hpos : 0 < p) (e : ℕ) (a u : ℤ) :
    0 ≤ oddInterleave p e a u ∧ oddInterleave p e a u < p ^ (2 * e) := by
  induction e generalizing a u with
  | zero => simp [oddInterleave]
  | succ e ih =>
    have ha0 := Int.emod_nonneg a (ne_of_gt hpos)
    have hau := Int.emod_lt_of_pos a hpos
    have hu0 := Int.emod_nonneg u (ne_of_gt hpos)
    have huu := Int.emod_lt_of_pos u hpos
    have ht := ih (a / p) (u / p)
    have hlow : 0 ≤ a % p + p * (u % p) ∧ a % p + p * (u % p) < p ^ 2 := by
      constructor
      · exact add_nonneg ha0 (mul_nonneg hpos.le hu0)
      · have hu1 : u % p ≤ p - 1 := by omega
        have hmul := mul_le_mul_of_nonneg_left hu1 hpos.le
        nlinarith
    rw [oddInterleave, odd_modulus_succ]
    refine ⟨add_nonneg hlow.1 (mul_nonneg (sq_nonneg p) ht.1), ?_⟩
    have ht1 : oddInterleave p e (a / p) (u / p) ≤ p ^ (2 * e) - 1 := by omega
    have hmul := mul_le_mul_of_nonneg_left ht1 (sq_nonneg p)
    nlinarith

private theorem odd_join_injective (p a b x y : ℤ) (hpos : 0 < p)
    (ha : 0 ≤ a ∧ a < p) (hb : 0 ≤ b ∧ b < p)
    (heq : a + p * x = b + p * y) : a = b ∧ x = y := by
  have hmod := congrArg (fun n : ℤ => n % p) heq
  simp only [Int.add_mul_emod_self_left,
    Int.emod_eq_of_lt ha.1 ha.2, Int.emod_eq_of_lt hb.1 hb.2] at hmod
  refine ⟨hmod, ?_⟩
  have hmul : p * x = p * y := by omega
  exact mul_left_cancel₀ (ne_of_gt hpos) hmul

/-- The low word and free word are both recoverable from their interleaving. -/
theorem oddInterleave_injective (p : ℤ) (hpos : 0 < p)
    (e : ℕ) (a b u v : ℤ)
    (ha : 0 ≤ a ∧ a < p ^ e) (hb : 0 ≤ b ∧ b < p ^ e)
    (hu : 0 ≤ u ∧ u < p ^ e) (hv : 0 ≤ v ∧ v < p ^ e)
    (heq : oddInterleave p e a u = oddInterleave p e b v) : a = b ∧ u = v := by
  induction e generalizing a b u v with
  | zero => simp only [pow_zero] at ha hb hu hv; omega
  | succ e ih =>
    have hrem (x : ℤ) : 0 ≤ x % p ∧ x % p < p :=
      ⟨Int.emod_nonneg _ (ne_of_gt hpos), Int.emod_lt_of_pos _ hpos⟩
    obtain ⟨hab,ht⟩ := odd_join_injective p (a % p) (b % p)
      (u % p + p * oddInterleave p e (a / p) (u / p))
      (v % p + p * oddInterleave p e (b / p) (v / p)) hpos (hrem a) (hrem b)
      (by simp only [oddInterleave] at heq; nlinarith [heq])
    obtain ⟨huv,htail⟩ := odd_join_injective p (u % p) (v % p)
      (oddInterleave p e (a / p) (u / p)) (oddInterleave p e (b / p) (v / p))
      hpos (hrem u) (hrem v) ht
    have hi := ih (a / p) (b / p) (u / p) (v / p)
      (odd_tail_canonical p a e hpos ha) (odd_tail_canonical p b e hpos hb)
      (odd_tail_canonical p u e hpos hu) (odd_tail_canonical p v e hpos hv) htail
    exact ⟨Int.ext_ediv_emod hi.1 hab, Int.ext_ediv_emod hi.2 huv⟩

/-- A square difference between interleaved words implies the low-word
relation. In addition, different free copies of the same low word cannot
have a square difference. This is the prime-coordinate lifting step. -/
theorem oddInterleave_square_relation (p : ℤ) (hp : Prime p) (hpos : 0 < p)
    (e : ℕ) (a b u v : ℤ)
    (ha : 0 ≤ a ∧ a < p ^ e) (hb : 0 ≤ b ∧ b < p ^ e)
    (hu : 0 ≤ u ∧ u < p ^ e) (hv : 0 ≤ v ∧ v < p ^ e)
    (hs : ∃ z : ℤ, p ^ (2 * e) ∣
      (oddInterleave p e b v - oddInterleave p e a u - z ^ 2)) :
    PrimeLowRelated p e a b ∧ (a = b → u = v) := by
  induction e generalizing a b u v with
  | zero =>
    refine ⟨trivial, ?_⟩
    simp only [pow_zero] at hu hv
    omega
  | succ e ih =>
    have hurem : 0 ≤ u % p ∧ u % p < p :=
      ⟨Int.emod_nonneg _ (ne_of_gt hpos), Int.emod_lt_of_pos _ hpos⟩
    have hvrem : 0 ≤ v % p ∧ v % p < p :=
      ⟨Int.emod_nonneg _ (ne_of_gt hpos), Int.emod_lt_of_pos _ hpos⟩
    obtain ⟨z,t,ht⟩ := hs
    rw [odd_modulus_succ] at ht
    simp only [oddInterleave] at ht
    by_cases hab : a % p = b % p
    · have hdescent := odd_free_digit_descent p (p ^ (2 * e))
        (u % p) (v % p) (oddInterleave p e (a / p) (u / p))
        (oddInterleave p e (b / p) (v / p)) hp hpos hurem hvrem
        (show ∃ z : ℤ, p ^ 2 * p ^ (2 * e) ∣
            p * (v % p - u % p) + p ^ 2 *
              (oddInterleave p e (b / p) (v / p) -
                oddInterleave p e (a / p) (u / p)) - z ^ 2 from by
          refine ⟨z,t,?_⟩
          rw [hab] at ht
          nlinarith [ht])
      obtain ⟨hfree,hsq⟩ := hdescent
      have htail := ih (a / p) (b / p) (u / p) (v / p)
        (odd_tail_canonical p a e hpos ha) (odd_tail_canonical p b e hpos hb)
        (odd_tail_canonical p u e hpos hu) (odd_tail_canonical p v e hpos hv) hsq
      refine ⟨by simpa only [PrimeLowRelated, if_pos hab] using htail.1, ?_⟩
      intro heq
      apply Int.ext_ediv_emod (htail.2 (congrArg (fun x : ℤ => x / p) heq)) hfree
    · refine ⟨?_, ?_⟩
      · simp only [PrimeLowRelated, if_neg hab]
        refine ⟨z, p * p ^ (2 * e) * t - v % p + u % p -
          p * oddInterleave p e (b / p) (v / p) +
          p * oddInterleave p e (a / p) (u / p), ?_⟩
        nlinarith [ht]
      · intro heq
        exact (hab (congrArg (fun x : ℤ => x % p) heq)).elim

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- One canonical base-prime word at every prime coordinate. Depths may differ. -/
abbrev OddWord (p e : ι → ℕ) := (i : ι) → Fin (p i ^ e i)

omit [Fintype ι] in
theorem oddWord_bounds (p e : ι → ℕ) (a : OddWord p e) (i : ι) :
    0 ≤ (a i : ℤ) ∧ (a i : ℤ) < (p i : ℤ) ^ e i := by
  refine ⟨Int.natCast_nonneg _, ?_⟩
  exact_mod_cast (a i).isLt

/-- Explicit CRT encoding of an arbitrary low point and an arbitrary free
point. A support may impose any dependencies between the low coordinates. -/
noncomputable def oddCRTEncode (p e : ι → ℕ) (hpos : ∀ i, 0 < p i)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (a u : OddWord p e) : ℤ :=
  crtResidue (fun i => p i ^ (2 * e i)) (fun i => pow_pos (hpos i) _)
    (fun _ _ hij => (hcop hij).pow _ _)
    (fun i => oddInterleave (p i) (e i) (a i) (u i))

theorem oddCRTEncode_bounds (p e : ι → ℕ) (hpos : ∀ i, 0 < p i)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j))) (a u : OddWord p e) :
    0 ≤ oddCRTEncode p e hpos hcop a u ∧
      oddCRTEncode p e hpos hcop a u < (∏ i, p i ^ (2 * e i) : ℕ) := by
  exact crtResidue_bounds _ _ _ _

theorem odd_modulus_product (p e : ι → ℕ) :
    (∏ i, p i ^ (2 * e i)) = (∏ i, p i ^ e i) ^ 2 := by
  calc
    (∏ i, p i ^ (2 * e i)) = ∏ i, (p i ^ e i) ^ 2 := by
      apply Finset.prod_congr rfl
      intro i _
      rw [← pow_mul, Nat.mul_comm]
    _ = (∏ i, p i ^ e i) ^ 2 := Finset.prod_pow _ _ _

theorem oddCRTEncode_emod (p e : ι → ℕ) (hpos : ∀ i, 0 < p i)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (a u : OddWord p e) (i : ι) :
    oddCRTEncode p e hpos hcop a u % (p i ^ (2 * e i) : ℕ) =
      oddInterleave (p i) (e i) (a i) (u i) := by
  apply crtResidue_emod
  intro j
  simpa only [Nat.cast_pow] using
    oddInterleave_bounds (p j) (by exact_mod_cast hpos j) (e j) (a j) (u j)

theorem oddCRTEncode_injective (p e : ι → ℕ) (hpos : ∀ i, 0 < p i)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j))) :
    Function.Injective (fun au : OddWord p e × OddWord p e =>
      oddCRTEncode p e hpos hcop au.1 au.2) := by
  rintro ⟨a,u⟩ ⟨b,v⟩ heq
  have hlocal (i : ι) : (a i : ℤ) = b i ∧ (u i : ℤ) = v i := by
    have hmod := congrArg (fun z : ℤ => z % (p i ^ (2 * e i) : ℕ)) heq
    simp only [oddCRTEncode_emod] at hmod
    exact oddInterleave_injective (p i) (by exact_mod_cast hpos i) (e i)
      (a i) (b i) (u i) (v i) (oddWord_bounds p e a i) (oddWord_bounds p e b i)
      (oddWord_bounds p e u i) (oddWord_bounds p e v i) hmod
  have hab : a = b := by
    funext i
    apply Fin.ext
    exact_mod_cast (hlocal i).1
  have huv : u = v := by
    funext i
    apply Fin.ext
    exact_mod_cast (hlocal i).2
  exact Prod.ext hab huv

/-- The necessary low-word relation at every prime, with no common
first-difference index imposed across the prime coordinates. -/
theorem oddCRTEncode_square_relation (p e : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hpos : ∀ i, 0 < p i)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (a b u v : OddWord p e)
    (hs : ∃ z : ℤ, ((∏ i, p i ^ (2 * e i) : ℕ) : ℤ) ∣
      (oddCRTEncode p e hpos hcop b v - oddCRTEncode p e hpos hcop a u - z ^ 2)) :
    (∀ i, PrimeLowRelated (p i) (e i) (a i) (b i)) ∧ (a = b → u = v) := by
  obtain ⟨z,hz⟩ := hs
  have hlocal (i : ι) : PrimeLowRelated (p i) (e i) (a i) (b i) ∧
      ((a i : ℤ) = b i → (u i : ℤ) = v i) := by
    have hdiv : (p i ^ (2 * e i) : ℕ) ∣ (∏ j, p j ^ (2 * e j) : ℕ) :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    have hdiv' : ((p i ^ (2 * e i) : ℕ) : ℤ) ∣
        ((∏ j, p j ^ (2 * e j) : ℕ) : ℤ) := by exact_mod_cast hdiv
    have hm := squareDifference_emod hdiv' hz
    rw [oddCRTEncode_emod, oddCRTEncode_emod] at hm
    have hpi : Prime (p i : ℤ) := by
      simpa only [Int.prime_iff_natAbs_prime, Int.natAbs_natCast] using hp i
    exact oddInterleave_square_relation (p i) hpi (by exact_mod_cast hpos i)
      (e i) (a i) (b i) (u i) (v i)
      (oddWord_bounds p e a i) (oddWord_bounds p e b i)
      (oddWord_bounds p e u i) (oddWord_bounds p e v i)
      ⟨z, by simpa only [Nat.cast_pow] using hm⟩
  refine ⟨fun i => (hlocal i).1, ?_⟩
  intro hab
  funext i
  apply Fin.ext
  have hi := (hlocal i).2 (by rw [hab])
  exact_mod_cast hi

/-- Full prime-coordinate free-digit lift for an arbitrary correlated finite
support of low points. The exact cardinality and every interval moment are
multiplied by the number of independent free words. -/
theorem odd_prime_interval_lift (p e : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hpos : ∀ i, 0 < p i)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : Finset (OddWord p e)) (left width : OddWord p e → ℝ)
    (hgeometry : ∀ a ∈ S, 0 ≤ left a ∧ 0 < width a ∧ width a < 1 ∧
      left a + width a ≤ 1)
    (horder : ∀ a ∈ S, ∀ b ∈ S, a ≠ b →
      (∀ i, PrimeLowRelated (p i) (e i) (a i) (b i)) →
      left a + width a ≤ left b) :
    ∃ (C : Finset ℤ) (a w : ℤ → ℝ),
      C.card = S.card * (∏ i, p i ^ e i) ∧
      (∀ x ∈ C, 0 ≤ x ∧ x < (∏ i, p i ^ (2 * e i) : ℕ)) ∧
      (∀ x ∈ C, 0 ≤ a x ∧ 0 < w x ∧ w x < 1 ∧ a x + w x ≤ 1) ∧
      IntervalOrderedModulo C (∏ i, p i ^ (2 * e i) : ℕ) a w ∧
      ∀ f : ℝ, (∑ x ∈ C, (w x) ^ f) =
        ((∏ i, p i ^ e i : ℕ) : ℝ) * ∑ x ∈ S, (width x) ^ f := by
  classical
  let κ := {x // x ∈ S} × OddWord p e
  let digit : κ → ℤ := fun au => oddCRTEncode p e hpos hcop au.1.val au.2
  have hinj : Function.Injective digit := by
    rintro ⟨a,u⟩ ⟨b,v⟩ heq
    have hpair : (a.val,u) = (b.val,v) := by
      apply oddCRTEncode_injective p e hpos hcop
      exact heq
    have hab : a.val = b.val := congrArg (fun x : OddWord p e × OddWord p e => x.1) hpair
    have huv : u = v := congrArg (fun x : OddWord p e × OddWord p e => x.2) hpair
    exact Prod.ext (Subtype.ext hab) huv
  have hordered : ∀ au bv : κ, au ≠ bv →
      (∃ z : ℤ, ((∏ i, p i ^ (2 * e i) : ℕ) : ℤ) ∣
        (digit bv - digit au - z ^ 2)) →
      left au.1.val + width au.1.val ≤ left bv.1.val := by
    intro au bv hneq hs
    have hlow := oddCRTEncode_square_relation p e hp hpos hcop
      au.1.val bv.1.val au.2 bv.2 hs
    have hab : au.1.val ≠ bv.1.val := by
      intro heq
      exact hneq (Prod.ext (Subtype.ext heq) (hlow.2 heq))
    exact horder _ au.1.property _ bv.1.property hab hlow.1
  obtain ⟨C,a,w,hcard,hcan,hgeom,hord,hmoment⟩ :=
    realize_indexed_interval_alphabet digit (fun au : κ => left au.1.val)
      (fun au : κ => width au.1.val) (∏ i, p i ^ (2 * e i)) hinj
      (fun au => oddCRTEncode_bounds p e hpos hcop au.1.val au.2)
      (fun au => hgeometry _ au.1.property) hordered
  refine ⟨C,a,w,?_,hcan,hgeom,hord,?_⟩
  · simpa only [κ, Fintype.card_prod, Fintype.card_coe, Fintype.card_pi,
      Fintype.card_fin] using hcard
  · intro f
    rw [hmoment]
    simp only [κ, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Fintype.card_pi, Fintype.card_fin]
    rw [← Finset.mul_sum]
    congr 1
    exact Finset.sum_coe_sort S (fun x => (width x) ^ f)

end Sarkozy
