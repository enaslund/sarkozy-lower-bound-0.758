import Sarkozy.BinaryGrowth

/-!+# A finite parity-window policy constructs every binary depth

The policy conditions only quantify over states, their at most four branches,
and the eight numerical residue classes. The recursively expanded alphabets
are constructed here and are not certificate hypotheses.
-/

namespace Sarkozy

open scoped BigOperators

/-- Real data corresponding to a finite binary controller. Values outside
the branch or parity ranges are irrelevant. -/
structure BinaryPolicy (S : Type*) where
  branches : S → Finset ℤ
  child : S → ℤ → S
  reflect : S → ℤ → Bool
  swap : S → ℤ → ℤ
  scale : S → ℤ → ℝ
  translate : S → ℤ → ℝ
  present : S → ℤ → Prop
  lo : S → ℤ → ℝ
  hi : S → ℤ → ℝ
  seed : S → ℤ

namespace BinaryPolicy

variable {S : Type*} (P : BinaryPolicy S)

def originalParity (s : S) (k : ℤ) : ℤ :=
  (k/4-P.swap s (k%4))%2

def classPresent (s : S) (k : ℤ) : Prop :=
  k%4 ∈ P.branches s ∧ P.present (P.child s (k%4)) (P.originalParity s k)

noncomputable def classLo (s : S) (k : ℤ) : ℝ :=
  P.translate s (k%4) + P.scale s (k%4) *
    (if P.reflect s (k%4) then
      1-P.hi (P.child s (k%4)) (P.originalParity s k)
    else P.lo (P.child s (k%4)) (P.originalParity s k))

noncomputable def classHi (s : S) (k : ℤ) : ℝ :=
  P.translate s (k%4) + P.scale s (k%4) *
    (if P.reflect s (k%4) then
      1-P.lo (P.child s (k%4)) (P.originalParity s k)
    else P.hi (P.child s (k%4)) (P.originalParity s k))

/-- Every condition is local to a state, branch, or residue class. -/
structure Valid : Prop where
  branch : ∀ s r, r ∈ P.branches s → 0 ≤ r ∧ r < 4 ∧ 0 < P.scale s r
  window : ∀ s p, 0 ≤ p → p < 2 → P.present s p →
    0 ≤ P.lo s p ∧ P.lo s p < P.hi s p ∧ P.hi s p ≤ 1
  seed : ∀ s, 0 ≤ P.seed s ∧ P.seed s < 2 ∧ P.present s (P.seed s)
  containment : ∀ s k, 0 ≤ k → k < 8 → P.classPresent s k →
    P.present s (k%2) ∧ P.lo s (k%2) ≤ P.classLo s k ∧
      P.classHi s k ≤ P.hi s (k%2)
  cyclic : ∀ s k, 0 ≤ k → k < 8 → P.classPresent s k →
    P.classPresent s ((k+1)%8) → P.classHi s k ≤ P.classLo s ((k+1)%8)

end BinaryPolicy

/-- A finite digit set with an interval attached to each digit. -/
structure BinaryAlphabet where
  digits : Finset ℤ
  start : ℤ → ℝ
  width : ℤ → ℝ

namespace BinaryAlphabet

variable {S : Type*}

def Fits (A : BinaryAlphabet) (P : BinaryPolicy S) (s : S) (Q : ℤ) : Prop :=
  (∀ x ∈ A.digits, 0 ≤ x ∧ x < Q) ∧
  (∀ x ∈ A.digits, 0 < A.width x ∧ P.present s (x%2) ∧
    P.lo s (x%2) ≤ A.start x ∧ A.start x+A.width x ≤ P.hi s (x%2)) ∧
  IntervalOrderedModulo A.digits Q A.start A.width

noncomputable def seed (P : BinaryPolicy S) (s : S) : BinaryAlphabet where
  digits := {P.seed s}
  start := fun _ => P.lo s (P.seed s)
  width := fun _ => P.hi s (P.seed s)-P.lo s (P.seed s)

theorem seed_fits (P : BinaryPolicy S) (hP : P.Valid) (s : S) :
    (seed P s).Fits P s 4 := by
  obtain ⟨hs0,hs2,hsp⟩ := hP.seed s
  have hw := hP.window s (P.seed s) hs0 hs2 hsp
  refine ⟨?_,?_,?_⟩
  · intro x hx
    have hx' : x = P.seed s := by simpa [seed] using hx
    subst x
    omega
  · intro x hx
    have hx' : x = P.seed s := by simpa [seed] using hx
    subst x
    simp only [seed, Int.emod_eq_of_lt hs0 hs2]
    exact ⟨sub_pos.mpr hw.2.1, hsp, le_rfl, by linarith⟩
  · intro x hx y hy hxy _
    have hx' : x = P.seed s := by simpa [seed] using hx
    have hy' : y = P.seed s := by simpa [seed] using hy
    exact (hxy (hx'.trans hy'.symm)).elim

theorem fits_geometry (P : BinaryPolicy S) (hP : P.Valid) (A : BinaryAlphabet)
    (s : S) (Q : ℤ) (hA : A.Fits P s Q) :
    ∀ x ∈ A.digits, 0 ≤ A.start x ∧ 0 < A.width x ∧
      A.start x+A.width x ≤ 1 := by
  intro x hx
  obtain ⟨hw,hpr,hlo,hhi⟩ := hA.2.1 x hx
  have hwnd := hP.window s (x%2) (Int.emod_nonneg _ (by norm_num))
    (Int.emod_lt_of_pos _ (by norm_num)) hpr
  exact ⟨hwnd.1.trans hlo, hw, hhi.trans hwnd.2.2⟩

noncomputable def branch (P : BinaryPolicy S) (A : S → BinaryAlphabet)
    (Q : ℤ) (s : S) (r : ℤ) : BinaryAlphabet where
  digits := (A (P.child s r)).digits.image
    (binaryDigitTransform Q (P.reflect s r) (P.swap s r))
  start := fun x => P.translate s r + P.scale s r *
    binaryTransformStart Q (P.reflect s r) (P.swap s r)
      (A (P.child s r)).start (A (P.child s r)).width x
  width := fun x => P.scale s r *
    binaryTransformWidth Q (P.reflect s r) (P.swap s r) (A (P.child s r)).width x

noncomputable def step (P : BinaryPolicy S) (A : S → BinaryAlphabet)
    (Q : ℤ) (s : S) : BinaryAlphabet where
  digits := binaryJoin (P.branches s) (fun r => (branch P A Q s r).digits)
  start := binaryJoinStart fun r => (branch P A Q s r).start
  width := binaryJoinWidth fun r => (branch P A Q s r).width

/-- A placed child interval lies in exactly the numerical class window
specified by the policy. The parity calculation includes reflection. -/
theorem branch_window (P : BinaryPolicy S) (hP : P.Valid)
    (A : S → BinaryAlphabet) (Q : ℤ) (hQ : 2 ∣ Q)
    (hA : ∀ s, (A s).Fits P s Q) (s : S) (r : ℤ) (hr : r ∈ P.branches s) :
    ∀ y ∈ (branch P A Q s r).digits,
      0 < (branch P A Q s r).width y ∧
      P.classPresent s ((r+4*y)%8) ∧
      P.classLo s ((r+4*y)%8) ≤ (branch P A Q s r).start y ∧
      (branch P A Q s r).start y + (branch P A Q s r).width y ≤
        P.classHi s ((r+4*y)%8) := by
  intro y hy
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
  have hc := (hA (P.child s r)).1 x hx
  obtain ⟨hw,hpr,hlo,hhi⟩ := (hA (P.child s r)).2.1 x hx
  obtain ⟨hr0,hr4,hu⟩ := hP.branch s r hr
  let y := binaryDigitTransform Q (P.reflect s r) (P.swap s r) x
  have hpar : y%2 = (x+P.swap s r)%2 :=
    binaryDigitTransform_parity Q (P.reflect s r) (P.swap s r) x hQ
  have hclassr : ((r+4*y)%8)%4 = r := by omega
  have hclassp : P.originalParity s ((r+4*y)%8) = x%2 := by
    unfold BinaryPolicy.originalParity
    rw [hclassr]
    omega
  have hwnd := binaryTransform_window Q (P.reflect s r) (P.swap s r)
    (A (P.child s r)).start (A (P.child s r)).width x
    (P.lo (P.child s r) (x%2)) (P.hi (P.child s r) (x%2)) hc ⟨hlo,hhi⟩
  change 0 < P.scale s r * binaryTransformWidth Q (P.reflect s r) (P.swap s r)
      (A (P.child s r)).width y ∧
    P.classPresent s ((r+4*y)%8) ∧
    P.classLo s ((r+4*y)%8) ≤ (branch P A Q s r).start y ∧
    (branch P A Q s r).start y+(branch P A Q s r).width y ≤
      P.classHi s ((r+4*y)%8)
  refine ⟨?_,?_,?_,?_⟩
  · rw [binaryTransformWidth_eval Q (P.reflect s r) (P.swap s r) _ x hc]
    exact mul_pos hu hw
  · simp only [BinaryPolicy.classPresent, hclassr, hclassp]
    exact ⟨hr,hpr⟩
  · simp only [BinaryPolicy.classLo, hclassr, hclassp, branch]
    have hm := mul_le_mul_of_nonneg_left hwnd.1 hu.le
    dsimp only [y] at *
    linarith
  · simp only [BinaryPolicy.classHi, hclassr, hclassp, branch]
    have hm := mul_le_mul_of_nonneg_left hwnd.2 hu.le
    dsimp only [y] at *
    nlinarith

/-- All finite policy conditions together preserve valid alphabets in one
binary step. -/
theorem step_fits (P : BinaryPolicy S) (hP : P.Valid)
    (A : S → BinaryAlphabet) (Q : ℤ) (hQ0 : 0 < Q) (hQ2 : 2 ∣ Q)
    (hA : ∀ s, (A s).Fits P s Q) (s : S) :
    (step P A Q s).Fits P s (4*Q) := by
  dsimp only [Fits, step]
  have hR : ∀ r ∈ P.branches s, 0 ≤ r ∧ r < 4 :=
    fun r hr => ⟨(hP.branch s r hr).1, (hP.branch s r hr).2.1⟩
  have hcan : ∀ r ∈ P.branches s, ∀ y ∈ (branch P A Q s r).digits,
      0 ≤ y ∧ y < Q := by
    intro r hr y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact binaryDigitTransform_canonical Q _ _ _ hQ0
  refine ⟨binaryJoin_canonical _ _ Q hR hcan, ?_, ?_⟩
  · intro Y hY
    obtain ⟨r,hr,hY⟩ := Finset.mem_biUnion.mp hY
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hY
    simp only [binaryJoin_width_eval _ r y (hR r hr),
      binaryJoin_eval _ r y (hR r hr)]
    have hb := branch_window P hP A Q hQ2 hA s r hr y hy
    have hcontains := hP.containment s ((r+4*y)%8)
      (Int.emod_nonneg _ (by norm_num)) (Int.emod_lt_of_pos _ (by norm_num)) hb.2.1
    have hpar : ((r+4*y)%8)%2 = (r+4*y)%2 := by omega
    rw [hpar] at hcontains
    exact ⟨hb.1, hcontains.1, hcontains.2.1.trans hb.2.2.1,
      hb.2.2.2.trans hcontains.2.2⟩
  · apply binaryJoin_ordered _ _ Q _ _ (P.classLo s) (P.classHi s)
      (fun k => 0 ≤ k ∧ k < 8 ∧ P.classPresent s k) hQ2 hR
    · intro r hr
      apply binary_affine_ordered _ Q _ _ _ _ (hP.branch s r hr).2.2.le
      exact binaryTransform_ordered _ Q _ _ _ _ (hA (P.child s r)).1
        (hA (P.child s r)).2.2
    · intro r hr y hy
      have hb := branch_window P hP A Q hQ2 hA s r hr y hy
      exact ⟨⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num),
        hb.2.1⟩, hb.2.2⟩
    · intro k hk hk'
      exact hP.cyclic s k hk.1 hk.2.1 hk.2.2 hk'.2.2

/-- `family P n` is the actual alphabet at depth `n+1`. The initial
alphabet is a singleton in the chosen present parity window. -/
noncomputable def family (P : BinaryPolicy S) : ℕ → S → BinaryAlphabet
  | 0 => seed P
  | n+1 => step P (family P n) ((4 : ℤ)^(n+1))

/-- A finite valid policy constructs ordered alphabets at every depth.
No expanded alphabet or assertion about its square edges is assumed. -/
theorem family_fits (P : BinaryPolicy S) (hP : P.Valid) (n : ℕ) :
    ∀ s, (family P n s).Fits P s ((4 : ℤ)^(n+1)) := by
  induction n with
  | zero => simpa only [family, zero_add, pow_one] using seed_fits P hP
  | succ n ih =>
    intro s
    have heven : (2 : ℤ) ∣ 4^(n+1) := by
      refine ⟨2*4^n, ?_⟩
      rw [pow_succ]
      ring
    have hs := step_fits P hP (family P n) (4^(n+1)) (by positivity) heven ih s
    simpa only [family, pow_succ'] using hs

noncomputable def moment (A : BinaryAlphabet) (f : ℝ) : ℝ :=
  ∑ x ∈ A.digits, (A.width x)^f

/-- Reflection and translation preserve the moment; the branch scale gives
the exact matrix coefficient used by the finite positive-vector test. -/
theorem branch_moment (P : BinaryPolicy S) (hP : P.Valid)
    (A : S → BinaryAlphabet) (Q : ℤ) (hA : ∀ s, (A s).Fits P s Q)
    (s : S) (r : ℤ) (hr : r ∈ P.branches s) (f : ℝ) :
    (branch P A Q s r).moment f = (P.scale s r)^f * (A (P.child s r)).moment f := by
  have hu : 0 ≤ P.scale s r := (hP.branch s r hr).2.2.le
  have hw : ∀ y ∈ (branch P A Q s r).digits,
      0 ≤ binaryTransformWidth Q (P.reflect s r) (P.swap s r)
        (A (P.child s r)).width y := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    rw [binaryTransformWidth_eval Q (P.reflect s r) (P.swap s r) _ x
      ((hA (P.child s r)).1 x hx)]
    exact ((hA (P.child s r)).2.1 x hx).1.le
  dsimp only [moment, branch]
  dsimp only [branch] at hw
  rw [binary_scaled_moment _ _ _ _ hu hw,
    binaryTransform_moment _ Q _ _ _ f (hA (P.child s r)).1]

/-- Exact moment recurrence for the recursively constructed finite sets. -/
theorem family_moment_succ (P : BinaryPolicy S) (hP : P.Valid)
    (n : ℕ) (s : S) (f : ℝ) :
    (family P (n+1) s).moment f =
      ∑ r ∈ P.branches s, (P.scale s r)^f *
        (family P n (P.child s r)).moment f := by
  change (step P (family P n) ((4:ℤ)^(n+1)) s).moment f = _
  dsimp only [moment, step]
  rw [binaryJoin_moment _ _ _ f
    (fun r hr => ⟨(hP.branch s r hr).1, (hP.branch s r hr).2.1⟩)]
  apply Finset.sum_congr rfl
  intro r hr
  exact branch_moment P hP (family P n) (4^(n+1)) (family_fits P hP n) s r hr f

/-- The positive-vector row checks propagate through the actual alphabet
construction, starting from its singleton-window moments. -/
theorem family_moment_growth (P : BinaryPolicy S) (hP : P.Valid)
    (f c a : ℝ) (v : S → ℝ) (hf : f ≤ 1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    (hseed : ∀ s, c*v s ≤ P.hi s (P.seed s)-P.lo s (P.seed s))
    (hrow : ∀ s, a*v s ≤ ∑ r ∈ P.branches s, (P.scale s r)^f*v (P.child s r)) :
    ∀ n s, c*a^n*v s ≤ (family P n s).moment f := by
  intro n
  induction n with
  | zero =>
    intro s
    obtain ⟨hp0,hp2,hpresent⟩ := hP.seed s
    obtain ⟨hl,hlt,hh⟩ := hP.window s (P.seed s) hp0 hp2 hpresent
    simpa [family, seed, moment] using binary_seed_moment
      (P.hi s (P.seed s)-P.lo s (P.seed s)) f c (v s)
      (sub_nonneg.mpr hlt.le) (by linarith) hf (hseed s)
  | succ n ih =>
    intro s
    rw [family_moment_succ P hP n s f]
    calc
      c*a^(n+1)*v s = (c*a^n)*(a*v s) := by ring
      _ ≤ (c*a^n)*(∑ r ∈ P.branches s, (P.scale s r)^f*v (P.child s r)) :=
        mul_le_mul_of_nonneg_left (hrow s) (mul_nonneg hc (pow_nonneg ha _))
      _ = ∑ r ∈ P.branches s, (P.scale s r)^f*(c*a^n*v (P.child s r)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        ring
      _ ≤ ∑ r ∈ P.branches s, (P.scale s r)^f*(family P n (P.child s r)).moment f := by
        apply Finset.sum_le_sum
        intro r hr
        exact mul_le_mul_of_nonneg_left (ih (P.child s r))
          (Real.rpow_nonneg (hP.branch s r hr).2.2.le _)

/-- A finite collection of positive widths has a common positive lower bound,
including when the collection is empty. -/
theorem positive_width_lower_bound (C : Finset ℤ) (w : ℤ → ℝ)
    (hw : ∀ x ∈ C, 0 < w x) : ∃ σ : ℝ, 0 < σ ∧ ∀ x ∈ C, σ ≤ w x := by
  induction C using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert x C hx ih =>
    obtain ⟨σ,hσ,hbound⟩ := ih (fun y hy => hw y (Finset.mem_insert_of_mem hy))
    refine ⟨min (w x) σ, lt_min (hw x (Finset.mem_insert_self _ _)) hσ, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hbound y hy)

/-- Finite policy validity, finite positive-vector rows, and one finite depth
inequality construct the binary interval alphabet required by the moment
criterion. There are no expanded-alphabet assumptions in this theorem. -/
theorem root_interval_certificate (P : BinaryPolicy S) (hP : P.Valid)
    (f c a α : ℝ) (v : S → ℝ) (root : S) (m : ℕ)
    (hm : 0 < m) (hf : f ≤ 1) (hc : 0 < c) (ha : 0 < a)
    (hroot : v root = 1)
    (hseed : ∀ s, c*v s ≤ P.hi s (P.seed s)-P.lo s (P.seed s))
    (hrow : ∀ s, a*v s ≤ ∑ r ∈ P.branches s, (P.scale s r)^f*v (P.child s r))
    (hlog : α*(m : ℝ)*Real.log 4 ≤ Real.log c +
      ((m-1 : ℕ) : ℝ)*Real.log a - f*Real.log 2) :
    ∃ (C : Finset ℤ) (start width : ℤ → ℝ) (σ : ℝ),
      0 < σ ∧
      (∀ x ∈ C, 0 ≤ x ∧ x < (4 : ℤ)^m) ∧
      (∀ x ∈ C, 0 ≤ start x ∧ σ ≤ width x ∧ width x ≤ (1:ℝ)/2 ∧
        start x+width x ≤ 1) ∧
      IntervalOrderedModulo C ((4 : ℤ)^m) start width ∧
      ((4 : ℝ)^m)^α ≤ ∑ x ∈ C, (width x)^f := by
  let A := family P (m-1) root
  have hn : m-1+1 = m := by omega
  have hfit : A.Fits P root ((4 : ℤ)^m) := by
    simpa only [hn] using family_fits P hP (m-1) root
  have hgeom := fits_geometry P hP A root (4^m) hfit
  have hwidth : ∀ x ∈ A.digits, 0 < (1/2 : ℝ)*A.width x := by
    intro x hx
    exact mul_pos (by norm_num) (hgeom x hx).2.1
  obtain ⟨σ,hσ,hbound⟩ := positive_width_lower_bound A.digits _ hwidth
  refine ⟨A.digits,A.start,(fun x => (1/2 : ℝ)*A.width x),σ,hσ,hfit.1,?_,?_,?_⟩
  · intro x hx
    obtain ⟨hs,hw,he⟩ := hgeom x hx
    exact ⟨hs,hbound x hx,by linarith,by linarith⟩
  · exact binary_shrink_ordered A.digits (4^m) A.start A.width (1/2)
      (by norm_num) (fun x hx => (hgeom x hx).2.1.le) hfit.2.2
  · have hgrowth : c*a^(m-1) ≤ ∑ x ∈ A.digits, (A.width x)^f := by
      simpa only [hroot,mul_one,moment,A] using
        family_moment_growth P hP f c a v hf hc.le ha.le hseed hrow (m-1) root
    apply binary_root_moment_of_log A.digits A.width c a (1/2) α f m hc ha
      (by norm_num) (fun x hx => (hgeom x hx).2.1.le) hgrowth
    have hl : Real.log (1/2 : ℝ) = -Real.log 2 := by
      rw [Real.log_div (by norm_num : (1:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0),
        Real.log_one]
      ring
    rw [hl]
    linarith

end BinaryAlphabet

end Sarkozy
