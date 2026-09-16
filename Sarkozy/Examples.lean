import Sarkozy.CRT

/-! A small application with every modular hypothesis proved inside Lean. -/

namespace Sarkozy

/-- The two residues `0,1` modulo three are ranked in increasing order. -/
theorem two_residues_ranked : RankedModulo {0, 1} 3 id := by
  intro x hx y hy hxy hsquare
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl
  · rcases hy with rfl | rfl
    · exact (hxy rfl).elim
    · norm_num
  · rcases hy with rfl | rfl
    · obtain ⟨z, hz⟩ := hsquare
      have hcast : ((0 - 1 - z ^ 2 : ℤ) : ZMod 3) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hz
      have hnot : ∀ t : ZMod 3, (0 : ZMod 3) - 1 - t ^ 2 ≠ 0 := by decide
      exact (hnot (z : ZMod 3) (by push_cast at hcast; exact hcast)).elim
    · exact (hxy rfl).elim

/-- The reverse-rank construction sends the residues `0,1` to the integers `4,2`. -/
theorem two_residues_image : reverseRankSet {0, 1} 3 1 id = {2, 4} := by
  norm_num [reverseRankSet, reverseRank, Finset.pair_comm]

/-- An explicit application of the general theorem, with no certificate assumptions. -/
theorem two_four_squareDifferenceFree : SquareDifferenceFree {2, 4} := by
  rw [← two_residues_image]
  apply reverseRankSet_squareDifferenceFree _ _ _ _ (by norm_num) _ two_residues_ranked
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;> norm_num

/-- Three consecutive residues form an increasing square chain modulo seven. -/
theorem three_residues_ranked : RankedModulo {0, 1, 2} 7 id := by
  intro x hx y hy hxy hsquare
  obtain ⟨z, hz⟩ := hsquare
  have hcast : ((y - x - z ^ 2 : ℤ) : ZMod 7) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr hz
  have hnot : ∀ t : ZMod 7,
      (-1 : ZMod 7) - t ^ 2 ≠ 0 ∧ (-2 : ZMod 7) - t ^ 2 ≠ 0 := by decide
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  all_goals try exact (hxy rfl).elim
  all_goals try norm_num
  all_goals push_cast at hcast
  all_goals first
    | exact ((hnot (z : ZMod 7)).1 hcast).elim
    | exact ((hnot (z : ZMod 7)).2 hcast).elim

/-- A two-component application: six integers in `[1,84]` with no square differences.
The local moduli are three and seven; both local certificates are proved above. -/
theorem six_elements_in_eighty_four :
    ∃ A : Finset ℤ, A.card = 6 ∧
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ 84) ∧ SquareDifferenceFree A := by
  let C : Bool → Finset ℤ := fun b => if b then {0, 1, 2} else {0, 1}
  let M : Bool → ℕ := fun b => if b then 7 else 3
  let K : Bool → ℤ := fun b => if b then 2 else 1
  have hM : ∀ i, 0 < M i := by decide
  have hcop : Pairwise (fun i j => (M i).Coprime (M j)) := by
    intro i j hij
    cases i <;> cases j <;> norm_num [M] at *
  have hcan : ∀ i, ∀ x ∈ C i, 0 ≤ x ∧ x < M i := by
    intro i
    cases i <;> norm_num [C, M]
  have hrange : ∀ i, ∀ x ∈ C i, 0 ≤ id x ∧ id x ≤ K i := by
    intro i
    cases i <;> norm_num [C, K]
  have hranked : ∀ i, RankedModulo (C i) (M i) id := by
    intro i
    cases i
    · exact two_residues_ranked
    · exact three_residues_ranked
  obtain ⟨A, hcard, hbound, hfree⟩ :=
    crt_reverseRank_realization C M (fun _ => id) K hM hcop hcan hrange hranked
  refine ⟨A, ?_, ?_, hfree⟩
  · simpa [C] using hcard
  · simpa [M, K] using hbound

end Sarkozy
