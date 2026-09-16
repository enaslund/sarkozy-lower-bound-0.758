import Sarkozy.BinaryPolicy
import Sarkozy.BinaryData

/-!
# The rational record certificate supplies a valid real binary policy

The finite conditions are checked on rationals and transported to the real
interval semantics. The policy uses all 25 states of the full record witness.
-/

namespace Sarkozy

structure RationalBinaryPolicy (S : Type*) where
  branches : S → Finset ℤ
  child : S → ℤ → S
  reflect : S → ℤ → Bool
  swap : S → ℤ → ℤ
  scale : S → ℤ → ℚ
  translate : S → ℤ → ℚ
  present : S → ℤ → Prop
  lo : S → ℤ → ℚ
  hi : S → ℤ → ℚ
  seed : S → ℤ

namespace RationalBinaryPolicy

variable {S : Type*} (P : RationalBinaryPolicy S)

noncomputable def toReal : BinaryPolicy S where
  branches := P.branches
  child := P.child
  reflect := P.reflect
  swap := P.swap
  scale := fun s r => P.scale s r
  translate := fun s r => P.translate s r
  present := P.present
  lo := fun s p => P.lo s p
  hi := fun s p => P.hi s p
  seed := P.seed

def classLo (s : S) (k : ℤ) : ℚ :=
  P.translate s (k%4) + P.scale s (k%4) *
    (if P.reflect s (k%4) then
      1-P.hi (P.child s (k%4)) ((k/4-P.swap s (k%4))%2)
    else P.lo (P.child s (k%4)) ((k/4-P.swap s (k%4))%2))

def classHi (s : S) (k : ℤ) : ℚ :=
  P.translate s (k%4) + P.scale s (k%4) *
    (if P.reflect s (k%4) then
      1-P.lo (P.child s (k%4)) ((k/4-P.swap s (k%4))%2)
    else P.hi (P.child s (k%4)) ((k/4-P.swap s (k%4))%2))

theorem classLo_cast (s : S) (k : ℤ) :
    (P.classLo s k : ℝ) = P.toReal.classLo s k := by
  cases h : P.reflect s (k%4) <;>
    simp [classLo, BinaryPolicy.classLo, BinaryPolicy.originalParity, toReal, h]

theorem classHi_cast (s : S) (k : ℤ) :
    (P.classHi s k : ℝ) = P.toReal.classHi s k := by
  cases h : P.reflect s (k%4) <;>
    simp [classHi, BinaryPolicy.classHi, BinaryPolicy.originalParity, toReal, h]

structure Valid : Prop where
  branch : ∀ s r, r ∈ P.branches s → 0 ≤ r ∧ r < 4 ∧ 0 < P.scale s r
  window : ∀ s (p : Fin 2), P.present s p →
    0 ≤ P.lo s p ∧ P.lo s p < P.hi s p ∧ P.hi s p ≤ 1
  seed : ∀ s, 0 ≤ P.seed s ∧ P.seed s < 2 ∧ P.present s (P.seed s)
  containment : ∀ s (k : Fin 8), P.toReal.classPresent s k →
    P.present s ((k : ℤ)%2) ∧ P.lo s ((k : ℤ)%2) ≤ P.classLo s k ∧
      P.classHi s k ≤ P.hi s ((k : ℤ)%2)
  cyclic : ∀ s (k : Fin 8), P.toReal.classPresent s k →
    P.toReal.classPresent s (((k : ℤ)+1)%8) →
      P.classHi s k ≤ P.classLo s (((k : ℤ)+1)%8)

/-- Finite rational validity entails the real policy hypotheses used by the
recursive construction. In particular every cast and cyclic class is proved. -/
theorem valid_toReal (hP : P.Valid) : P.toReal.Valid := by
  constructor
  · intro s r hr
    obtain ⟨h0,h4,hu⟩ := hP.branch s r hr
    exact ⟨h0,h4,by change (0:ℝ) < (P.scale s r : ℝ); exact_mod_cast hu⟩
  · intro s p hp0 hp2 hpr
    let j : Fin 2 := ⟨p.toNat, by omega⟩
    have hj : (j : ℤ) = p := by dsimp [j]; omega
    change P.present s p at hpr
    have h := hP.window s j (by simpa [hj] using hpr)
    rw [hj] at h
    change 0 ≤ (P.lo s p : ℝ) ∧ (P.lo s p : ℝ) < (P.hi s p : ℝ) ∧ (P.hi s p : ℝ) ≤ 1
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2.1, by exact_mod_cast h.2.2⟩
  · exact hP.seed
  · intro s k hk0 hk8 hpr
    let j : Fin 8 := ⟨k.toNat, by omega⟩
    have hj : (j : ℤ) = k := by dsimp [j]; omega
    have h := hP.containment s j (by simpa [hj] using hpr)
    rw [hj] at h
    refine ⟨h.1, ?_, ?_⟩
    · rw [← classLo_cast]
      change (P.lo s (k%2) : ℝ) ≤ (P.classLo s k : ℝ)
      exact_mod_cast h.2.1
    · rw [← classHi_cast]
      change (P.classHi s k : ℝ) ≤ (P.hi s (k%2) : ℝ)
      exact_mod_cast h.2.2
  · intro s k hk0 hk8 hpr hnext
    let j : Fin 8 := ⟨k.toNat, by omega⟩
    have hj : (j : ℤ) = k := by dsimp [j]; omega
    have h := hP.cyclic s j (by simpa [hj] using hpr) (by simpa [hj] using hnext)
    rw [hj] at h
    rw [← classLo_cast, ← classHi_cast]
    exact_mod_cast h

end RationalBinaryPolicy

namespace RecordBinary

def rawState (s : Fin 25) : BinaryData.State :=
  BinaryData.states.getD s.val ⟨⟨0,1⟩, none, []⟩

def rawBranch (s : Fin 25) (r : ℤ) : BinaryData.Branch :=
  ((rawState s).branches.find? (fun b => (b.residue : ℤ) == r)).getD
    ⟨0,0,1,0,false,false⟩

def rawWindow (s : Fin 25) (p : ℤ) : BinaryData.Window :=
  if p = 0 then (rawState s).even else (rawState s).odd.getD ⟨0,0⟩

def rationalPolicy : RationalBinaryPolicy (Fin 25) where
  branches := fun s => ((rawState s).branches.map fun b => (b.residue : ℤ)).toFinset
  child := fun s r => ⟨(rawBranch s r).child % 25, Nat.mod_lt _ (by decide)⟩
  reflect := fun s r => (rawBranch s r).reflect
  swap := fun s r => if (rawBranch s r).swap then 1 else 0
  scale := fun s r => (rawBranch s r).scale
  translate := fun s r => (rawBranch s r).shift
  present := fun s p => p = 0 ∨ p = 1 ∧ (rawState s).odd.isSome = true
  lo := fun s p => (rawWindow s p).lo
  hi := fun s p => (rawWindow s p).hi
  seed := fun s => if (rawWindow s 0).hi - (rawWindow s 0).lo <
    (rawWindow s 1).hi - (rawWindow s 1).lo then 1 else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rationalPolicy_valid : rationalPolicy.Valid := by
  constructor <;>
    dsimp [rationalPolicy, BinaryPolicy.classPresent, BinaryPolicy.originalParity,
      RationalBinaryPolicy.toReal, RationalBinaryPolicy.classLo, RationalBinaryPolicy.classHi] <;>
    decide +kernel

noncomputable def policy : BinaryPolicy (Fin 25) := rationalPolicy.toReal

theorem policy_valid : policy.Valid :=
  RationalBinaryPolicy.valid_toReal rationalPolicy rationalPolicy_valid

end RecordBinary
end Sarkozy
