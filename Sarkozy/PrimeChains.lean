import Sarkozy.Intervals

/-!
# Prime-square alphabets from ordered low-digit chains

A chain modulo a prime supplies its low digits; the upper base-prime digit
is unrestricted. All intervals have equal width, and their order is the
order of the low-digit chain. Concrete checks below use kernel `decide`.
-/

namespace Sarkozy

/-- The unrestricted upper digit above one entry of a low-digit chain. -/
def primeChainDigit {p t : ℕ} (s : Fin t → Fin p) (v : Fin t × Fin p) : ℤ :=
  (s v.1).val + (p : ℤ) * v.2.val

def primeChainDigits {p t : ℕ} (s : Fin t → Fin p) : Finset ℤ :=
  Finset.univ.image (primeChainDigit s)

noncomputable def primeChainStart {p t : ℕ} (s : Fin t → Fin p) : ℤ → ℝ :=
  Function.extend (primeChainDigit s) (fun v => (v.1.val : ℝ) / t) (fun _ => 0)

noncomputable def primeChainWidth (t : ℕ) (_ : ℤ) : ℝ := 1 / t

theorem primeChainDigit_mod {p t : ℕ} (s : Fin t → Fin p) (v : Fin t × Fin p) :
    primeChainDigit s v % p = (s v.1).val := by
  have h0 : (0 : ℤ) ≤ (s v.1).val := by omega
  have hlt : ((s v.1).val : ℤ) < p := by exact_mod_cast (s v.1).isLt
  simp [primeChainDigit, Int.emod_eq_of_lt h0 hlt]

theorem primeChainDigit_injective {p t : ℕ} (hp : 0 < p) (s : Fin t → Fin p)
    (hs : Function.Injective s) : Function.Injective (primeChainDigit s) := by
  intro v u h
  have hlow := congrArg (fun x : ℤ => x % p) h
  rw [primeChainDigit_mod, primeChainDigit_mod] at hlow
  have hi : v.1 = u.1 := hs (Fin.ext (by exact_mod_cast hlow))
  have hu : v.2 = u.2 := by
    apply Fin.ext
    dsimp [primeChainDigit] at h
    rw [hi] at h
    have : (v.2.val : ℤ) = u.2.val := by nlinarith
    exact_mod_cast this
  exact Prod.ext hi hu

theorem primeChainStart_eval {p t : ℕ} (hp : 0 < p) (s : Fin t → Fin p)
    (hs : Function.Injective s) (v : Fin t × Fin p) :
    primeChainStart s (primeChainDigit s v) = (v.1.val : ℝ) / t :=
  (primeChainDigit_injective hp s hs).extend_apply _ _ v

theorem primeChainDigits_card {p t : ℕ} (hp : 0 < p) (s : Fin t → Fin p)
    (hs : Function.Injective s) : (primeChainDigits s).card = t * p := by
  rw [primeChainDigits, Finset.card_image_of_injective _ (primeChainDigit_injective hp s hs)]
  simp

theorem primeChainDigit_bounds {p t : ℕ} (hp : 0 < p) (s : Fin t → Fin p)
    (v : Fin t × Fin p) :
    0 ≤ primeChainDigit s v ∧ primeChainDigit s v < (p : ℤ)^2 := by
  have hs0 : (0 : ℤ) ≤ (s v.1).val := by omega
  have hslt : ((s v.1).val : ℤ) < p := by exact_mod_cast (s v.1).isLt
  have hu0 : (0 : ℤ) ≤ v.2.val := by omega
  have hult : (v.2.val : ℤ) < p := by exact_mod_cast v.2.isLt
  dsimp [primeChainDigit]
  constructor <;> nlinarith

theorem primeChainDigits_bounds {p t : ℕ} (hp : 0 < p) (s : Fin t → Fin p) :
    ∀ x ∈ primeChainDigits s, 0 ≤ x ∧ x < (p : ℤ)^2 := by
  intro x hx
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
  exact primeChainDigit_bounds hp s v

/-- A nonzero square edge modulo `p²` cannot preserve the low digit. -/
theorem prime_square_edge_low_ne {p : ℕ} (hp : p.Prime) (x y z : ℤ)
    (hx : 0 ≤ x ∧ x < (p : ℤ)^2) (hy : 0 ≤ y ∧ y < (p : ℤ)^2)
    (hxy : x ≠ y) (hroot : (p : ℤ)^2 ∣ y - x - z^2) :
    x % p ≠ y % p := by
  intro hmod
  have hpdiff : (p : ℤ) ∣ y - x := by
    apply Int.dvd_iff_emod_eq_zero.mpr
    rw [Int.sub_emod, ← hmod, sub_self, Int.zero_emod]
  have hproot : (p : ℤ) ∣ y - x - z^2 := dvd_trans (dvd_pow_self _ (by decide : 2 ≠ 0)) hroot
  have hpz2 : (p : ℤ) ∣ z^2 := by
    have := dvd_sub hpdiff hproot
    simpa using this
  have hpz : (p : ℤ) ∣ z := (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow hpz2
  have hp2z2 : (p : ℤ)^2 ∣ z^2 := pow_dvd_pow_of_dvd hpz 2
  have hp2diff : (p : ℤ)^2 ∣ y - x := by
    have := dvd_add hroot hp2z2
    simpa using this
  obtain ⟨k, hk⟩ := hp2diff
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hpp : 0 < (p : ℤ)^2 := by positivity
  have : k = 0 := by nlinarith
  subst k
  simp at hk
  omega

/-- The only finite input is the orientation of square edges between low digits. -/
def PrimeChainOrdered {p t : ℕ} (s : Fin t → Fin p) : Prop :=
  ∀ i j : Fin t, i ≠ j → ∀ z : ZMod p,
    (s j).val - (s i).val = z^2 → i < j

instance {p t : ℕ} [NeZero p] (s : Fin t → Fin p) : Decidable (PrimeChainOrdered s) := by
  unfold PrimeChainOrdered
  infer_instance

theorem primeChain_interval_ordered {p t : ℕ} (hp : p.Prime) (ht : 0 < t)
    (s : Fin t → Fin p) (hs : Function.Injective s) (horder : PrimeChainOrdered s) :
    IntervalOrderedModulo (primeChainDigits s) ((p : ℤ)^2)
      (primeChainStart s) (primeChainWidth t) := by
  intro x hx y hy hxy ⟨z, hz⟩
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hy
  have hlow := prime_square_edge_low_ne hp _ _ z
    (primeChainDigit_bounds hp.pos s u) (primeChainDigit_bounds hp.pos s v) hxy hz
  rw [primeChainDigit_mod, primeChainDigit_mod] at hlow
  have hij : u.1 ≠ v.1 := by intro h; apply hlow; rw [h]
  have hproot : (p : ℤ) ∣ primeChainDigit s v - primeChainDigit s u - z^2 :=
    dvd_trans (dvd_pow_self _ (by decide : 2 ≠ 0)) hz
  have hcast := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hproot
  have heq : ((s v.1).val : ZMod p) - (s u.1).val = (z : ZMod p)^2 := by
    push_cast at hcast
    simpa [primeChainDigit] using sub_eq_zero.mp hcast
  have hlt := horder u.1 v.1 hij (z : ZMod p) heq
  rw [primeChainStart_eval hp.pos s hs, primeChainStart_eval hp.pos s hs]
  dsimp [primeChainWidth]
  rw [← add_div]
  apply (div_le_div_iff_of_pos_right (by exact_mod_cast ht : (0 : ℝ) < t)).mpr
  exact_mod_cast (show u.1.val + 1 ≤ v.1.val by exact hlt)

theorem primeChain_geometry {p t : ℕ} (hp : 0 < p) (ht : 0 < t)
    (s : Fin t → Fin p) (hs : Function.Injective s) :
    ∀ x ∈ primeChainDigits s,
      0 ≤ primeChainStart s x ∧ 0 < primeChainWidth t x ∧
      primeChainStart s x + primeChainWidth t x ≤ 1 := by
  intro x hx
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
  rw [primeChainStart_eval hp s hs]
  dsimp [primeChainWidth]
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  refine ⟨div_nonneg (by positivity) (le_of_lt htR), one_div_pos.mpr htR, ?_⟩
  rw [← add_div, div_le_one htR]
  exact_mod_cast (show v.1.val + 1 ≤ t from v.1.isLt)

theorem primeChain_moment {p t : ℕ} (hp : 0 < p) (s : Fin t → Fin p)
    (hs : Function.Injective s) (f : ℝ) :
    ∑ x ∈ primeChainDigits s, (primeChainWidth t x)^f =
      (t * p : ℕ) * (1 / (t : ℝ))^f := by
  simp [primeChainWidth, primeChainDigits_card hp s hs]

/-- The six ordered chains used by the nine-component construction. -/
def primeChainPrimes : Fin 6 → ℕ := ![3, 7, 11, 31, 59, 103]
def primeChainLengths : Fin 6 → ℕ := ![2, 3, 4, 7, 9, 11]

def concretePrimeChain (i : Fin 6) :
    Fin (primeChainLengths i) → Fin (primeChainPrimes i) :=
  match i with
  | ⟨0, _⟩ => (![0, 1] : Fin 2 → Fin 3)
  | ⟨1, _⟩ => (![0, 1, 2] : Fin 3 → Fin 7)
  | ⟨2, _⟩ => (![0, 1, 4, 5] : Fin 4 → Fin 11)
  | ⟨3, _⟩ => (![0, 1, 8, 5, 2, 9, 10] : Fin 7 → Fin 31)
  | ⟨4, _⟩ => (![0, 1, 28, 17, 22, 4, 26, 20, 29] : Fin 9 → Fin 59)
  | ⟨5, _⟩ => (![0, 1, 29, 92, 2, 61, 17, 30, 93, 18, 19] : Fin 11 → Fin 103)
  | ⟨n + 6, h⟩ => False.elim (by omega)

theorem primeChainPrimes_prime (i : Fin 6) : (primeChainPrimes i).Prime := by
  fin_cases i <;> decide

theorem primeChainLengths_pos (i : Fin 6) : 0 < primeChainLengths i := by
  fin_cases i <;> decide

theorem concretePrimeChain_injective (i : Fin 6) :
    Function.Injective (concretePrimeChain i) := by
  fin_cases i <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem concretePrimeChain_ordered (i : Fin 6) :
    PrimeChainOrdered (concretePrimeChain i) := by
  haveI : NeZero (primeChainPrimes i) := ⟨ne_of_gt (primeChainPrimes_prime i).pos⟩
  fin_cases i <;> decide

/-- Explicit alphabets, with every upper digit allowed. -/
def concretePrimeDigits (i : Fin 6) : Finset ℤ := primeChainDigits (concretePrimeChain i)
noncomputable def concretePrimeStart (i : Fin 6) : ℤ → ℝ :=
  primeChainStart (concretePrimeChain i)
noncomputable def concretePrimeWidth (i : Fin 6) : ℤ → ℝ :=
  primeChainWidth (primeChainLengths i)

theorem concretePrimeDigits_card (i : Fin 6) :
    (concretePrimeDigits i).card = primeChainLengths i * primeChainPrimes i :=
  primeChainDigits_card (primeChainPrimes_prime i).pos _ (concretePrimeChain_injective i)

theorem concretePrimeDigits_bounds (i : Fin 6) :
    ∀ x ∈ concretePrimeDigits i, 0 ≤ x ∧ x < (primeChainPrimes i : ℤ)^2 :=
  primeChainDigits_bounds (primeChainPrimes_prime i).pos _

theorem concretePrime_interval_ordered (i : Fin 6) :
    IntervalOrderedModulo (concretePrimeDigits i) ((primeChainPrimes i : ℤ)^2)
      (concretePrimeStart i) (concretePrimeWidth i) :=
  primeChain_interval_ordered (primeChainPrimes_prime i) (primeChainLengths_pos i) _
    (concretePrimeChain_injective i) (concretePrimeChain_ordered i)

theorem concretePrime_geometry (i : Fin 6) :
    ∀ x ∈ concretePrimeDigits i,
      0 ≤ concretePrimeStart i x ∧ (1 / 11 : ℝ) ≤ concretePrimeWidth i x ∧
      concretePrimeWidth i x ≤ (1 / 2 : ℝ) ∧
      concretePrimeStart i x + concretePrimeWidth i x ≤ 1 := by
  intro x hx
  obtain ⟨hstart, _, hend⟩ := primeChain_geometry (primeChainPrimes_prime i).pos
    (primeChainLengths_pos i) _ (concretePrimeChain_injective i) x hx
  refine ⟨hstart, ?_, ?_, hend⟩ <;>
    fin_cases i <;> norm_num [concretePrimeWidth, primeChainWidth, primeChainLengths]

theorem concretePrime_moment (i : Fin 6) (f : ℝ) :
    ∑ x ∈ concretePrimeDigits i, (concretePrimeWidth i x)^f =
      (primeChainLengths i * primeChainPrimes i : ℕ) *
        (1 / (primeChainLengths i : ℝ))^f :=
  primeChain_moment (primeChainPrimes_prime i).pos _ (concretePrimeChain_injective i) f

end Sarkozy
