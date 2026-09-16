#!/usr/bin/env python3
"""Translate a rational JSON binary witness into kernel-checkable Lean data.

Usage: python3 scripts/generate-binary-data.py PATH_TO_CERTIFICATE_JSON
The generated Lean proof, not this translator, decides geometric validity.
"""
from pathlib import Path
from fractions import Fraction
import hashlib
import json
import sys

source = Path(sys.argv[1])
data = json.loads(source.read_text())

def rational(value):
    value = Fraction(*value) if isinstance(value, list) else Fraction(value)
    if value.denominator == 1:
        return str(value.numerator)
    return f'({value.numerator} / {value.denominator})'

states = []
for state in data['states']:
    a, b, c, d, denominator = state['windows']
    even = f'⟨{rational([a,denominator])}, {rational([b,denominator])}⟩'
    odd = 'none' if c < 0 else f'some ⟨{rational([c,denominator])}, {rational([d,denominator])}⟩'
    branches = []
    for branch in state['branches']:
        branches.append('⟨'+', '.join([
            str(branch['r']), str(branch['child']), rational(branch['scale']),
            rational(branch['shift']), str(bool(branch['swap'])).lower(),
            str(bool(branch['reflect'])).lower()])+'⟩')
    states.append(f'  ⟨{even}, {odd}, [\n    '+',\n    '.join(branches)+']⟩')

header = '''import Mathlib

/-!
# Exact geometry of the 25-state certificate for exponent 0.75806746

All endpoints and affine maps are rational. `geometry_verified` is proved
by `decide +kernel`, so the finite checks are reduced by Lean's kernel.
The definitions implement the interval containments and cyclic mod-eight
orders used by the binary transition lemma. They do not assert the real
moment inequalities or positivity of a spectral gap.
-/

namespace Sarkozy.BinaryData

structure Window where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq

structure Branch where
  residue : ℕ
  child : ℕ
  scale : ℚ
  shift : ℚ
  swap : Bool
  reflect : Bool
  deriving DecidableEq

structure State where
  even : Window
  odd : Option Window
  branches : List Branch
  deriving DecidableEq

def windowValid (w : Window) : Prop := 0 ≤ w.lo ∧ w.lo < w.hi ∧ w.hi ≤ 1

def placed (data : List State) (s : State) (k : Fin 8) : Option Window := do
  let branch ← s.branches.find? (fun b => b.residue == k.val % 4)
  let child ← data[branch.child]?
  let parity := (k.val / 4 + if branch.swap then 1 else 0) % 2
  let w ← if parity = 0 then some child.even else child.odd
  let v := if branch.reflect then ⟨1 - w.hi, 1 - w.lo⟩ else w
  return ⟨branch.shift + branch.scale * v.lo, branch.shift + branch.scale * v.hi⟩

def contained (parent child : Option Window) : Prop :=
  match child, parent with
  | none, _ => True
  | some _, none => False
  | some c, some p => p.lo ≤ c.lo ∧ c.lo < c.hi ∧ c.hi ≤ p.hi

def ordered (left right : Option Window) : Prop :=
  match left, right with
  | some a, some b => a.hi ≤ b.lo
  | _, _ => True

instance (w : Window) : Decidable (windowValid w) := by unfold windowValid; infer_instance
instance (a b : Option Window) : Decidable (contained a b) := by
  unfold contained; split <;> infer_instance
instance (a b : Option Window) : Decidable (ordered a b) := by
  unfold ordered; split <;> infer_instance

def stateValid (data : List State) (s : State) : Prop :=
  windowValid s.even ∧
  (match s.odd with | none => True | some w => windowValid w) ∧
  s.branches.Pairwise (fun a b => a.residue ≠ b.residue) ∧
  (∀ b ∈ s.branches, b.residue < 4 ∧ b.child < data.length ∧ 0 < b.scale) ∧
  (∀ k : Fin 8,
    contained (if k.val % 2 = 0 then some s.even else s.odd) (placed data s k) ∧
    ordered (placed data s k) (placed data s (k + 1)))

instance (data : List State) (s : State) : Decidable (stateValid data s) := by
  unfold stateValid
  cases s.odd <;> infer_instance

'''
footer = '''
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem geometry_verified : ∀ s ∈ states, stateValid states s := by decide +kernel

theorem state_count : states.length = 25 := by decide
theorem branch_count : (states.map fun s => s.branches.length).sum = 94 := by decide

end Sarkozy.BinaryData
'''
digest = hashlib.sha256(source.read_bytes()).hexdigest()
result = header+f'-- Source certificate SHA-256: {digest}\n'
result += 'def states : List State := [\n'+',\n'.join(states)+']\n'+footer
output = Path(__file__).resolve().parents[1] / 'Sarkozy/BinaryData.lean'
output.write_text(result)
print(f'Wrote {output}: {len(states)} states, source SHA-256 {digest}')
