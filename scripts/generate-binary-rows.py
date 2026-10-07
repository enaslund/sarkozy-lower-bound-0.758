#!/usr/bin/env python3
"""Generate the kernel-checked binary row power certificates.

Every distinct branch scale `u` is rounded down to the denominator `D`, and a
lower bound for `u^f` is certified by the shared endpoint checker of
`FastPowerCertificate`: exact 4096th-power comparisons of two integer root
endpoints and an eighth-order logarithm enclosure. Decimal arithmetic only
proposes the lower endpoints. Exact Fraction arithmetic checks every row here,
and Lean's kernel checks everything again.
"""
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal, localcontext, ROUND_FLOOR
from math import isqrt
import hashlib
import json

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT/'research-notes/next-push/binary-cert-0.7580758318008816.json'
OUTPUT = ROOT/'lean-formalization/Sarkozy/BinaryRows.lean'
TEMPLATE = Path(__file__).with_name('binary-rows-proof.txt')
D = 10**30
STEPS = 12
ROOT_POWER = 2**STEPS
DENOMINATOR_POWER = D**(ROOT_POWER-1)
POWER_NUMERATOR = 1549247890379023302829202
POWER_DENOMINATOR = 10**25
POWER = F(POWER_NUMERATOR, POWER_DENOMINATOR)


def log_bounds(x):
    z = 1-x
    s = sum((z**k/F(k) for k in range(1, 9)), F())
    error = z**9/x
    return -s-error, -s+error


def root_endpoints(a0, b0):
    a, b = a0, b0
    for _ in range(STEPS):
        a = isqrt(a*D)
        z = b*D
        b = isqrt(z)
        b += b*b < z
    return a, b


def certificate(a0):
    a, _ = root_endpoints(a0, a0)
    certified = POWER*ROOT_POWER*log_bounds(F(a, D))[0]
    with localcontext() as ctx:
        ctx.prec = 100
        exponent = Decimal(certified.numerator)/Decimal(certified.denominator)-Decimal(10)**-27
        y = int((exponent.exp()*D).to_integral_value(rounding=ROUND_FLOOR))-1
    while True:
        _, b = root_endpoints(a0, y)
        if log_bounds(F(b, D))[1] <= POWER*log_bounds(F(a, D))[0]:
            break
        y -= 1
    assert 0 < a <= D and 0 < b <= D and y > 0
    assert a**ROOT_POWER <= a0*DENOMINATOR_POWER
    assert y*DENOMINATOR_POWER <= b**ROOT_POWER
    return y, a, b


def vec(items, indent='  ', group=3):
    return '!['+(',\n'+indent).join(', '.join(map(str, items[j:j+group]))
                                    for j in range(0, len(items), group))+']'


def matrix(rows):
    return '!['+',\n    '.join(vec(row, '      ') for row in rows)+']'


def main():
    raw = SOURCE.read_bytes()
    data = json.loads(raw)
    assert F(data['f']) == POWER
    growth = F(data['a'])
    vector = [F(x) for x in data['vector']]
    scales = sorted({(F(*b['scale'])*D).numerator//(F(*b['scale'])*D).denominator
                     for s in data['states'] for b in s['branches']})
    count = len(scales)
    certs = [certificate(n) for n in scales]
    indices = []
    margins = []
    for s, state in enumerate(data['states']):
        row = [0]*4
        lhs = F(0)
        for branch in state['branches']:
            q = F(*branch['scale'])
            j = scales.index((q*D).numerator//(q*D).denominator)
            assert F(scales[j], D) <= q
            row[branch['r']] = j
            lhs += F(certs[j][0], D)*vector[branch['child']]
        margins.append(lhs-growth*vector[s])
        indices.append(row)
    assert min(margins) > 0, min(margins)
    header = f"""
namespace RecordBinary

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

-- Source JSON SHA-256: {hashlib.sha256(raw).hexdigest()}
-- {count} distinct scales, rounded down to denominator 10^30, with
-- {ROOT_POWER}th-root endpoint certificates for their powers.
private def rowScaleNumerator : Fin {count} → ℕ :=
  {vec(scales, '    ')}

private def rowLowerNumerator : Fin {count} → ℕ :=
  {vec([c[0] for c in certs], '    ')}

private def rowRootLow : Fin {count} → ℕ :=
  {vec([hex(c[1]) for c in certs], '    ')}

private def rowRootHigh : Fin {count} → ℕ :=
  {vec([hex(c[2]) for c in certs], '    ')}

private def rowScale (i : Fin {count}) : ℚ := (rowScaleNumerator i : ℚ)/{D}
private def rowLower (i : Fin {count}) : ℚ := (rowLowerNumerator i : ℚ)/{D}

private def rowBranchIndex : Fin 25 → Fin 4 → Fin {count} :=
  {matrix(indices)}

private def rowIndex (s : Fin 25) (r : ℤ) : Fin {count} :=
  rowBranchIndex s ⟨r.toNat%4, Nat.mod_lt _ (by decide)⟩
"""
    proof = TEMPLATE.read_text()
    for key, value in [('@COUNT@', count), ('@D@', D), ('@N@', ROOT_POWER-1),
                       ('@PN@', POWER_NUMERATOR), ('@PD@', POWER_DENOMINATOR),
                       ('@GN@', growth.numerator), ('@GD@', growth.denominator)]:
        proof = proof.replace(key, str(value))
    original = OUTPUT.read_text()
    before = original.split('-- BEGIN GENERATED BINARY POWER CERTIFICATES')[0]
    after = original.split('-- END GENERATED BINARY POWER CERTIFICATES')[1]
    OUTPUT.write_text(before+'-- BEGIN GENERATED BINARY POWER CERTIFICATES'+header+proof
                      + '\n-- END GENERATED BINARY POWER CERTIFICATES'+after)
    print(json.dumps({'distinct_scales': count, 'root_power': ROOT_POWER,
                      'minimum_exact_row_surplus': str(min(margins)),
                      'minimum_row_surplus_decimal': float(min(margins)),
                      'output_bytes': OUTPUT.stat().st_size}, indent=2))


if __name__ == '__main__':
    main()
