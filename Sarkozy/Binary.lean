import Sarkozy.Intervals

/-!+# Binary square differences and parity-window assembly

The only cross-branch square fact needed by the recursion is that an odd
square is 1 modulo 8. A same-branch edge cancels a factor of 4. The resulting
assembly theorem uses exact interval bounds indexed by numerical classes
modulo 8, including the cyclic comparison from class 7 to class 0.
-/

namespace Sarkozy

/-- Cancel the base-four digit from a modular square in a single branch. -/
theorem binary_square_cancel (Q x y : ℤ)
    (hs : ∃ z : ℤ, 4 * Q ∣ 4 * (y - x) - z ^ 2) :
    ∃ z : ℤ, Q ∣ y - x - z ^ 2 := by
  obtain ⟨z,t,ht⟩ := hs
  have hroot : (2 : ℤ) ∣ z := by
    apply (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp
    refine ⟨y - x - Q * t, ?_⟩
    nlinarith [ht]
  obtain ⟨u, rfl⟩ := hroot
  refine ⟨u, t, ?_⟩
  nlinarith [ht]

/-- The complete list of square residues modulo eight. -/
theorem binary_square_mod_eight (z : ℤ) :
    z ^ 2 % 8 = 0 ∨ z ^ 2 % 8 = 1 ∨ z ^ 2 % 8 = 4 := by
  have hlo := Int.emod_nonneg z (by norm_num : (8 : ℤ) ≠ 0)
  have hhi := Int.emod_lt_of_pos z (by norm_num : (0 : ℤ) < 8)
  rw [pow_two, Int.mul_emod]
  interval_cases h : z % 8 <;> norm_num [h]

/-- A square joining different base-four branches advances one class modulo
eight. In particular, differences between branch residues two apart cannot
be squares. -/
theorem binary_cross_branch_class (Q r s x y : ℤ)
    (hQ : 2 ∣ Q) (hr : 0 ≤ r ∧ r < 4) (hs : 0 ≤ s ∧ s < 4)
    (hrs : r ≠ s)
    (hsquare : ∃ z : ℤ, 4 * Q ∣ (s + 4*y) - (r + 4*x) - z ^ 2) :
    (s + 4*y) % 8 = ((r + 4*x) % 8 + 1) % 8 := by
  obtain ⟨z,hz⟩ := hsquare
  have h8 : (8 : ℤ) ∣ 4 * Q := by
    obtain ⟨q,rfl⟩ := hQ
    exact ⟨q, by ring⟩
  have hm := Int.emod_eq_zero_of_dvd (dvd_trans h8 hz)
  have hz8 := binary_square_mod_eight z
  have hpower : z ^ 2 % 8 = 1 := by
    rcases hz8 with hz8 | hz8 | hz8
    · have hdiv : (4 : ℤ) ∣ z ^ 2 :=
        dvd_trans (by norm_num : (4 : ℤ) ∣ 8) (Int.dvd_of_emod_eq_zero hz8)
      obtain ⟨q,hq⟩ := hdiv
      obtain ⟨t,ht⟩ := dvd_trans h8 hz
      omega
    · exact hz8
    · have hdiv : (4 : ℤ) ∣ z ^ 2 := by
        apply Int.dvd_of_emod_eq_zero
        omega
      obtain ⟨q,hq⟩ := hdiv
      obtain ⟨t,ht⟩ := dvd_trans h8 hz
      omega
  omega

/-- A translated digit, with an optional reversal, reduced canonically. -/
def binaryDigitTransform (Q : ℤ) (reflect : Bool) (shift x : ℤ) : ℤ :=
  ((if reflect then -x else x) + shift) % Q

/-- The inverse residue map, before reading the original child's interval. -/
def binaryDigitInverse (Q : ℤ) (reflect : Bool) (shift x : ℤ) : ℤ :=
  (if reflect then shift-x else x-shift) % Q

theorem binaryDigitInverse_transform (Q : ℤ) (reflect : Bool) (shift x : ℤ)
    (hx : 0 ≤ x ∧ x < Q) :
    binaryDigitInverse Q reflect shift (binaryDigitTransform Q reflect shift x) = x := by
  cases reflect
  · have h := (Int.mod_modEq (x+shift) Q).sub_right shift
    change ((x+shift)%Q-shift)%Q = x
    have he : (x+shift)-shift = x := by ring
    rw [he] at h
    exact h.eq.trans (Int.emod_eq_of_lt hx.1 hx.2)
  · have h := (Int.mod_modEq (-x+shift) Q).sub_left shift
    have he : shift-(-x+shift) = x := by ring
    rw [he] at h
    exact h.eq.trans (Int.emod_eq_of_lt hx.1 hx.2)

theorem binaryDigitTransform_injective (C : Finset ℤ) (Q : ℤ)
    (reflect : Bool) (shift : ℤ) (hC : ∀ x ∈ C, 0 ≤ x ∧ x < Q) :
    Set.InjOn (binaryDigitTransform Q reflect shift) (↑C : Set ℤ) := by
  intro x hx y hy he
  have hi := congrArg (binaryDigitInverse Q reflect shift) he
  simpa [binaryDigitInverse_transform Q reflect shift x (hC x hx),
    binaryDigitInverse_transform Q reflect shift y (hC y hy)] using hi

/-- Reduction modulo an even child modulus preserves parity; sign reversal
does not change parity, so only the translation toggles it. -/
theorem binaryDigitTransform_parity (Q : ℤ) (reflect : Bool) (shift x : ℤ)
    (hQ : 2 ∣ Q) :
    binaryDigitTransform Q reflect shift x % 2 = (x+shift)%2 := by
  have hm := (Int.mod_modEq ((if reflect then -x else x)+shift) Q).of_dvd hQ
  cases reflect
  · exact hm.eq
  · have hp : (-x+shift)%2 = (x+shift)%2 := by omega
    exact hm.eq.trans hp

theorem binaryDigitTransform_canonical (Q : ℤ) (reflect : Bool) (shift x : ℤ)
    (hQ : 0 < Q) :
    0 ≤ binaryDigitTransform Q reflect shift x ∧
      binaryDigitTransform Q reflect shift x < Q := by
  exact ⟨Int.emod_nonneg _ (ne_of_gt hQ), Int.emod_lt_of_pos _ hQ⟩

/-- The inverse map reconstructs all reflected/translated child intervals. -/
noncomputable def binaryTransformStart (Q : ℤ) (reflect : Bool) (shift : ℤ)
    (a w : ℤ → ℝ) (x : ℤ) : ℝ :=
  let y := binaryDigitInverse Q reflect shift x
  if reflect then 1-a y-w y else a y

noncomputable def binaryTransformWidth (Q : ℤ) (reflect : Bool) (shift : ℤ)
    (w : ℤ → ℝ) (x : ℤ) : ℝ :=
  w (binaryDigitInverse Q reflect shift x)

theorem binaryTransformStart_eval (Q : ℤ) (reflect : Bool) (shift : ℤ)
    (a w : ℤ → ℝ) (x : ℤ) (hx : 0 ≤ x ∧ x < Q) :
    binaryTransformStart Q reflect shift a w (binaryDigitTransform Q reflect shift x) =
      if reflect then 1-a x-w x else a x := by
  simp only [binaryTransformStart, binaryDigitInverse_transform Q reflect shift x hx]

theorem binaryTransformWidth_eval (Q : ℤ) (reflect : Bool) (shift : ℤ)
    (w : ℤ → ℝ) (x : ℤ) (hx : 0 ≤ x ∧ x < Q) :
    binaryTransformWidth Q reflect shift w (binaryDigitTransform Q reflect shift x) = w x := by
  simp only [binaryTransformWidth, binaryDigitInverse_transform Q reflect shift x hx]

/-- Translation preserves square-edge orientation, while reflection reverses
both the residue orientation and the interval orientation. -/
theorem binaryTransform_ordered (C : Finset ℤ) (Q : ℤ) (reflect : Bool)
    (shift : ℤ) (a w : ℤ → ℝ)
    (hC : ∀ x ∈ C, 0 ≤ x ∧ x < Q)
    (horder : IntervalOrderedModulo C Q a w) :
    IntervalOrderedModulo (C.image (binaryDigitTransform Q reflect shift)) Q
      (binaryTransformStart Q reflect shift a w)
      (binaryTransformWidth Q reflect shift w) := by
  intro X hX Y hY hXY hsquare
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hX
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hY
  have hxy : x ≠ y := by intro he; exact hXY (by rw [he])
  rw [binaryTransformStart_eval Q reflect shift a w x (hC x hx),
    binaryTransformWidth_eval Q reflect shift w x (hC x hx),
    binaryTransformStart_eval Q reflect shift a w y (hC y hy)]
  obtain ⟨z,hz⟩ := hsquare
  have hm := ((Int.mod_modEq ((if reflect then -y else y)+shift) Q).sub
    (Int.mod_modEq ((if reflect then -x else x)+shift) Q)).sub_right (z^2)
  have hs : Q ∣ ((if reflect then -y else y)+shift) -
      ((if reflect then -x else x)+shift) - z^2 := by
    apply Int.dvd_of_emod_eq_zero
    rw [← hm.eq]
    exact Int.emod_eq_zero_of_dvd hz
  cases reflect
  · simp only [Bool.false_eq_true, ↓reduceIte] at hs ⊢
    have hs' : Q ∣ y-x-z^2 := by convert hs using 1; ring
    exact horder x hx y hy hxy ⟨z,hs'⟩
  · simp only [↓reduceIte] at hs ⊢
    have hs' : Q ∣ x-y-z^2 := by convert hs using 1; ring
    have h := horder y hy x hx (Ne.symm hxy) ⟨z,hs'⟩
    linarith

/-- Reflection takes an interval inside `[lo,hi]` to one inside
`[1-hi,1-lo]`, retaining its positive width. -/
theorem binaryTransform_window (Q : ℤ) (reflect : Bool) (shift : ℤ)
    (a w : ℤ → ℝ) (x : ℤ) (lo hi : ℝ) (hx : 0 ≤ x ∧ x < Q)
    (hwindow : lo ≤ a x ∧ a x+w x ≤ hi) :
    (if reflect then 1-hi else lo) ≤
      binaryTransformStart Q reflect shift a w (binaryDigitTransform Q reflect shift x) ∧
    binaryTransformStart Q reflect shift a w (binaryDigitTransform Q reflect shift x) +
      binaryTransformWidth Q reflect shift w (binaryDigitTransform Q reflect shift x) ≤
      (if reflect then 1-lo else hi) := by
  rw [binaryTransformStart_eval Q reflect shift a w x hx,
    binaryTransformWidth_eval Q reflect shift w x hx]
  cases reflect <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> constructor <;> linarith

/-- An increasing affine placement preserves modular interval order. -/
theorem binary_affine_ordered (C : Finset ℤ) (Q : ℤ) (a w : ℤ → ℝ)
    (u t : ℝ) (hu : 0 ≤ u) (horder : IntervalOrderedModulo C Q a w) :
    IntervalOrderedModulo C Q (fun x => t+u*a x) (fun x => u*w x) := by
  intro x hx y hy hxy hsquare
  have h := mul_le_mul_of_nonneg_left (horder x hx y hy hxy hsquare) hu
  nlinarith

/-- Shrinking widths at fixed left endpoints preserves interval order. -/
theorem binary_shrink_ordered (C : Finset ℤ) (Q : ℤ) (a w : ℤ → ℝ)
    (θ : ℝ) (hθ : θ ≤ 1) (hw : ∀ x ∈ C, 0 ≤ w x)
    (horder : IntervalOrderedModulo C Q a w) :
    IntervalOrderedModulo C Q a (fun x => θ*w x) := by
  intro x hx y hy hxy hsquare
  have h := horder x hx y hy hxy hsquare
  have hs := mul_le_mul_of_nonneg_right hθ (hw x hx)
  nlinarith

/-- Assemble distinct base-four branches from their transformed children. -/
def binaryJoin (R : Finset ℤ) (C : ℤ → Finset ℤ) : Finset ℤ :=
  R.biUnion fun r => (C r).image fun x => r + 4*x

noncomputable def binaryJoinStart (a : ℤ → ℤ → ℝ) (x : ℤ) : ℝ :=
  a (x % 4) (x / 4)

noncomputable def binaryJoinWidth (w : ℤ → ℤ → ℝ) (x : ℤ) : ℝ :=
  w (x % 4) (x / 4)

theorem binaryJoin_eval (a : ℤ → ℤ → ℝ) (r x : ℤ)
    (hr : 0 ≤ r ∧ r < 4) : binaryJoinStart a (r + 4*x) = a r x := by
  simp [binaryJoinStart, Int.add_mul_ediv_left _ _ (by norm_num : (4:ℤ) ≠ 0),
    Int.emod_eq_of_lt hr.1 hr.2, Int.ediv_eq_zero_of_lt hr.1 hr.2]

theorem binaryJoin_width_eval (w : ℤ → ℤ → ℝ) (r x : ℤ)
    (hr : 0 ≤ r ∧ r < 4) : binaryJoinWidth w (r + 4*x) = w r x :=
  binaryJoin_eval w r x hr

/-- Same-branch interval order and eight cyclic window comparisons imply
the full binary parent order. Only present numerical classes are compared. -/
theorem binaryJoin_ordered (R : Finset ℤ) (C : ℤ → Finset ℤ) (Q : ℤ)
    (a w : ℤ → ℤ → ℝ) (lo hi : ℤ → ℝ) (present : ℤ → Prop)
    (hQ : 2 ∣ Q) (hR : ∀ r ∈ R, 0 ≤ r ∧ r < 4)
    (hchild : ∀ r ∈ R, IntervalOrderedModulo (C r) Q (a r) (w r))
    (hwindow : ∀ r ∈ R, ∀ x ∈ C r,
      present ((r+4*x)%8) ∧ lo ((r+4*x)%8) ≤ a r x ∧
        a r x + w r x ≤ hi ((r+4*x)%8))
    (hcyclic : ∀ k : ℤ, present k → present ((k+1)%8) →
      hi k ≤ lo ((k+1)%8)) :
    IntervalOrderedModulo (binaryJoin R C) (4*Q)
      (binaryJoinStart a) (binaryJoinWidth w) := by
  intro X hX Y hY hXY hsquare
  obtain ⟨r,hr,hX⟩ := Finset.mem_biUnion.mp hX
  obtain ⟨X,hx,rfl⟩ := Finset.mem_image.mp hX
  obtain ⟨s,hs,hY⟩ := Finset.mem_biUnion.mp hY
  obtain ⟨Y,hy,rfl⟩ := Finset.mem_image.mp hY
  rw [binaryJoin_eval a r X (hR r hr), binaryJoin_width_eval w r X (hR r hr),
    binaryJoin_eval a s Y (hR s hs)]
  by_cases hrs : r = s
  · subst s
    have hxy : X ≠ Y := by intro he; exact hXY (by rw [he])
    have hcancel : ∃ z : ℤ, 4*Q ∣ 4*(Y-X)-z^2 := by
      obtain ⟨z,hz⟩ := hsquare
      refine ⟨z, ?_⟩
      convert hz using 1; ring
    exact hchild r hr X hx Y hy hxy (binary_square_cancel Q X Y hcancel)
  · have hclass := binary_cross_branch_class Q r s X Y hQ (hR r hr) (hR s hs)
      hrs hsquare
    obtain ⟨hpX,hloX,hhiX⟩ := hwindow r hr X hx
    obtain ⟨hpY,hloY,hhiY⟩ := hwindow s hs Y hy
    rw [hclass] at hpY hloY
    exact hhiX.trans ((hcyclic _ hpX hpY).trans hloY)

/-- Canonical children remain canonical after distinct base-four digits are
prepended. -/
theorem binaryJoin_canonical (R : Finset ℤ) (C : ℤ → Finset ℤ) (Q : ℤ)
    (hR : ∀ r ∈ R, 0 ≤ r ∧ r < 4)
    (hC : ∀ r ∈ R, ∀ x ∈ C r, 0 ≤ x ∧ x < Q) :
    ∀ x ∈ binaryJoin R C, 0 ≤ x ∧ x < 4*Q := by
  intro X hX
  obtain ⟨r,hr,hX⟩ := Finset.mem_biUnion.mp hX
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hX
  have hb := hR r hr
  have hc := hC r hr x hx
  omega

/-- The assembled interval is precisely the selected branch interval, so
any uniform geometric bounds pass to the union. -/
theorem binaryJoin_geometry (R : Finset ℤ) (C : ℤ → Finset ℤ)
    (a w : ℤ → ℤ → ℝ) (hR : ∀ r ∈ R, 0 ≤ r ∧ r < 4)
    (hgeom : ∀ r ∈ R, ∀ x ∈ C r,
      0 ≤ a r x ∧ 0 < w r x ∧ a r x + w r x ≤ 1) :
    ∀ x ∈ binaryJoin R C, 0 ≤ binaryJoinStart a x ∧
      0 < binaryJoinWidth w x ∧ binaryJoinStart a x + binaryJoinWidth w x ≤ 1 := by
  intro X hX
  obtain ⟨r,hr,hX⟩ := Finset.mem_biUnion.mp hX
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hX
  rw [binaryJoin_eval a r x (hR r hr), binaryJoin_width_eval w r x (hR r hr)]
  exact hgeom r hr x hx

end Sarkozy
