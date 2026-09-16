import Sarkozy.Moment

/-!
# Automatic uniform bounds for finite interval alphabets

For a fixed finite family, positivity and widths strictly below one imply
the common bounds needed by the stopping-word argument. The theorem below
therefore removes these uniform bounds from the external certificate interface.
-/

namespace Sarkozy

open scoped BigOperators

/-- Transfer an injectively indexed interval construction to the integer-digit
interface used by the asymptotic theorem, preserving its moment exactly. -/
theorem realize_indexed_interval_alphabet {κ : Type*} [Fintype κ]
    (digit : κ → ℤ) (left width : κ → ℝ) (B : ℕ)
    (hinj : Function.Injective digit)
    (hcanonical : ∀ i, 0 ≤ digit i ∧ digit i < B)
    (hgeometry : ∀ i, 0 ≤ left i ∧ 0 < width i ∧ width i < 1 ∧
      left i + width i ≤ 1)
    (hordered : ∀ i j, i ≠ j →
      (∃ z : ℤ, (B : ℤ) ∣ (digit j - digit i - z ^ 2)) →
      left i + width i ≤ left j) :
    ∃ (C : Finset ℤ) (a w : ℤ → ℝ),
      C.card = Fintype.card κ ∧
      (∀ x ∈ C, 0 ≤ x ∧ x < B) ∧
      (∀ x ∈ C, 0 ≤ a x ∧ 0 < w x ∧ w x < 1 ∧ a x + w x ≤ 1) ∧
      IntervalOrderedModulo C B a w ∧
      ∀ f : ℝ, (∑ x ∈ C, (w x) ^ f) = ∑ i, (width i) ^ f := by
  classical
  let C := Finset.univ.image digit
  let a := Function.extend digit left (fun _ => 0)
  let w := Function.extend digit width (fun _ => 0)
  have ha (i : κ) : a (digit i) = left i := hinj.extend_apply _ _ _
  have hw (i : κ) : w (digit i) = width i := hinj.extend_apply _ _ _
  refine ⟨C, a, w, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Finset.card_image_iff.mpr hinj.injOn).trans (Finset.card_univ)
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hcanonical i
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    rw [ha, hw]
    exact hgeometry i
  · intro x hx y hy hxy hsquare
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    rw [ha, ha, hw]
    exact hordered i j (fun hij => hxy (congrArg digit hij)) hsquare
  · intro f
    dsimp [C]
    rw [Finset.sum_image hinj.injOn]
    exact Finset.sum_congr rfl (fun i _ => by rw [hw])

theorem exists_uniform_width_bounds {ι : Type*} [Fintype ι]
    (C : ι → Finset ℤ) (w : ι → ℤ → ℝ)
    (hw : ∀ i, ∀ x ∈ C i, 0 < w i x ∧ w i x < 1) :
    ∃ σ ρ : ℝ, 0 < σ ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ i, ∀ x ∈ C i, σ ≤ w i x ∧ w i x ≤ ρ := by
  classical
  let T : Finset ℝ := insert (1 / 2) (Finset.univ.biUnion fun i => (C i).image (w i))
  have hT : T.Nonempty := ⟨1 / 2, Finset.mem_insert_self _ _⟩
  have hmem (i : ι) (x : ℤ) (hx : x ∈ C i) : w i x ∈ T := by
    apply Finset.mem_insert_of_mem
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  have hvalid : ∀ z ∈ T, 0 < z ∧ z < 1 := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · norm_num
    · obtain ⟨i, _, hz⟩ := Finset.mem_biUnion.mp hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      exact hw i x hx
  refine ⟨T.min' hT, T.max' hT, (hvalid _ (T.min'_mem hT)).1,
    (hvalid _ (T.max'_mem hT)).1, (hvalid _ (T.max'_mem hT)).2, ?_⟩
  intro i x hx
  exact ⟨T.min'_le _ (hmem i x hx), T.le_max' _ (hmem i x hx)⟩

/-- The interval-moment criterion with only pointwise finite geometry assumptions.
No common lower or upper width bound is an input hypothesis. -/
theorem interval_moment_exponent_of_pointwise_widths
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (C : ι → Finset ℤ) (B : ι → ℕ) (a w : ι → ℤ → ℝ)
    (f : ι → ℝ) (α : ℝ)
    (hB : ∀ i, 1 < B i)
    (hcop : Pairwise (fun i j => (B i).Coprime (B j)))
    (hsquare : ∀ i, ∃ s : ℕ, B i = s ^ 2)
    (hC : ∀ i, ∀ x ∈ C i, 0 ≤ x ∧ x < B i)
    (hgeom : ∀ i, ∀ x ∈ C i,
      0 ≤ a i x ∧ 0 < w i x ∧ w i x < 1 ∧ a i x + w i x ≤ 1)
    (horder : ∀ i, IntervalOrderedModulo (C i) (B i) (a i) (w i))
    (hα : 0 ≤ α) (hf : ∀ i, 0 ≤ f i)
    (hmoment : ∀ i, (B i : ℝ) ^ α ≤ ∑ x ∈ C i, (w i x) ^ (f i))
    (hgap : α < ∑ i, f i) : LowerBoundExponent α := by
  obtain ⟨σ, ρ, hσ, hρ, hρ1, hwidth⟩ := exists_uniform_width_bounds C w
    (fun i x hx => ⟨(hgeom i x hx).2.1, (hgeom i x hx).2.2.1⟩)
  apply interval_moment_exponent C B a w f α σ ρ hB hcop hsquare hC hσ hρ hρ1
  · intro i x hx
    exact ⟨(hgeom i x hx).1, (hwidth i x hx).1,
      (hwidth i x hx).2, (hgeom i x hx).2.2.2⟩
  · exact horder
  · exact hα
  · exact hf
  · exact hmoment
  · exact hgap

end Sarkozy
