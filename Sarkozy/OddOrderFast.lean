import Sarkozy.OddOrderCertificate

/-!
# Definitionally transparent evaluation for repeated prefix queries

The continuations below force small numeric keys and digits before invoking
larger expressions. Equal numeric prefixes then share identical closed kernel
expressions. All optimized checks are proved equal to the original checks.
-/

namespace Sarkozy.OddOrder

/-- Force the numerical value before passing it to a continuation. -/
def withNat (n : ℕ) (f : ℕ → ℕ) : ℕ :=
  match n with
  | 0 => f 0
  | n+1 => f (n+1)

theorem withNat_eq (n : ℕ) (f : ℕ → ℕ) : withNat n f = f n := by
  cases n <;> rfl

def withInt (n : ℤ) (f : ℤ → ℕ) : ℕ :=
  match n with
  | .ofNat n => withNat n (fun k => f (.ofNat k))
  | .negSucc n => withNat n (fun k => f (.negSucc k))

theorem withInt_eq (n : ℤ) (f : ℤ → ℕ) : withInt n f = f n := by
  cases n <;> simp only [withInt, withNat_eq]

def canonicalLookup (table : MaskTree) (key : ℕ) : ℕ :=
  withNat key table.lookup

theorem canonicalLookup_eq (table : MaskTree) (key : ℕ) :
    canonicalLookup table key = table.lookup key := withNat_eq _ _

def fastPrefixLookup (p : ℕ) (table : MaskTree) (digits : List ℤ) : ℕ :=
  canonicalLookup table (prefixCode p digits)

def fastPredecessors (G : List ℤ → ℕ) (p : ℕ) : ℕ → ℤ → List ℤ → ℕ
  | 0, _, pre => G pre
  | e+1, b, pre =>
      withInt (b % (p : ℤ)) fun digit =>
        maskUnion ((List.range p).map fun z =>
          if candidate p digit z = digit then 0
          else G (pre ++ [candidate p digit z])) |||
        fastPredecessors G p e (b / (p : ℤ)) (pre ++ [digit])

/-- Materializing keys and current digits does not change the mask. -/
theorem fastPredecessors_eq (G : List ℤ → ℕ) (p e : ℕ) (b : ℤ) (pre : List ℤ) :
    fastPredecessors G p e b pre = predecessors G p e b pre := by
  induction e generalizing b pre with
  | zero => rfl
  | succ e ih =>
      simp only [fastPredecessors, withInt_eq, predecessors, ih, candidate, Int.emod_emod]

def fastTargetCheck (n p0 p1 e : ℕ) (G0 G1 : List ℤ → ℕ) (E : MaskTree)
    (i : ℕ) (r : Entry) : Bool :=
  decide (r.2 ≤ n) &&
    ((decide (r.2 = 0) || decide (E.lookup (r.2-1) ≤ entryStart r)) &&
      belowOrSelf (fastPredecessors G0 p0 e (entryPoint r 0) [] &&&
        fastPredecessors G1 p1 e (entryPoint r 1) []) r.2 i)

theorem fastTargetCheck_eq (n p0 p1 e : ℕ) (G0 G1 : List ℤ → ℕ) (E : MaskTree) :
    fastTargetCheck n p0 p1 e G0 G1 E = targetCheck n p0 p1 e G0 G1 E := by
  funext i r
  simp only [fastTargetCheck, targetCheck, fastPredecessors_eq]

end Sarkozy.OddOrder
