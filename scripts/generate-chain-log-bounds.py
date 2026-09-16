#!/usr/bin/env python3
"""Propose exact integer square-root ladders; Lean checks every square relation.

No floating-point arithmetic, external theorem prover, or native_decide is used.
Run from any directory; replace only the marked data block in ChainMoments.lean.
"""
from fractions import Fraction
from math import isqrt
from pathlib import Path

STEPS = 52
DENOMINATOR = 10**35
OUTPUT_DENOMINATOR = 10**15
START = '-- BEGIN GENERATED INTEGER LOG CERTIFICATES'
END = '-- END GENERATED INTEGER LOG CERTIFICATES'


def ladder(x: int, upper: bool) -> list[int]:
    values = [x * DENOMINATOR]
    for _ in range(STEPS):
        radicand = values[-1] * DENOMINATOR
        root = isqrt(radicand)
        if upper and root * root < radicand:
            root += 1
        values.append(root)
    return values


def certificate(x: int, upper: bool) -> tuple[str, int]:
    direction = 'upper' if upper else 'lower'
    name = f'chainLog{direction.title()}{x}'
    values = ladder(x, upper)
    endpoint = (Fraction(values[-1], DENOMINATOR) - 1 if upper else
                1 - Fraction(DENOMINATOR, values[-1])) * 2**STEPS
    scaled = endpoint * OUTPUT_DENOMINATOR
    rounded = (-(-scaled.numerator // scaled.denominator) if upper else
               scaled.numerator // scaled.denominator)
    rows = ',\n    '.join(', '.join(map(str, values[j:j+3])) for j in range(0, len(values), 3))
    left, right = (f'Real.log ({x} : ℝ)', f'{rounded} / {OUTPUT_DENOMINATOR}') if upper else (
        f'{rounded} / {OUTPUT_DENOMINATOR}', f'Real.log ({x} : ℝ)')
    proof = ('  exact h.trans (by norm_num)' if upper else
             '  exact (show (' + left + ' : ℝ) ≤ _ by norm_num).trans h')
    block = f'''private def {name} : Fin {STEPS+1} → ℕ :=
  ![{rows}]

theorem chain_log_{direction}_{x} : {left} ≤ {right} := by
  have h := log_{direction}_of_integer_ladder {x} {DENOMINATOR} {name}
    (by decide) (by decide) (by decide) (by decide)
  have hend : {name} (Fin.last {STEPS}) = {values[-1]} := by decide
  rw [hend] at h
{proof}
'''
    return block, rounded


def main() -> None:
    sections = [START, 'set_option maxRecDepth 100000\nset_option maxHeartbeats 4000000\n']
    for upper, numbers in [(False, [2,3,4,7,9,11]), (True, [3,7,11,31,59,103])]:
        for x in numbers:
            block, rounded = certificate(x, upper)
            sections.append(block)
            print(('upper' if upper else 'lower'), x, rounded, '/', OUTPUT_DENOMINATOR)
    sections.append(END)
    path = Path(__file__).resolve().parents[1] / 'Sarkozy' / 'ChainMoments.lean'
    text = path.read_text()
    generated = '\n\n'.join(sections)
    if START in text:
        begin = text.index(START)
        end = text.index(END, begin) + len(END)
        text = text[:begin] + generated + text[end:]
    else:
        text = text.replace('\nend Sarkozy\n', '\n' + generated + '\n\nend Sarkozy\n')
    path.write_text(text)


if __name__ == '__main__':
    main()
