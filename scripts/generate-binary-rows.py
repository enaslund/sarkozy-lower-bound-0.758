#!/usr/bin/env python3
"""Generate the kernel-checked binary row power certificates.

Decimal arithmetic only proposes lower endpoints. Integer square comparisons,
exact Fraction arithmetic and ultimately Lean's kernel verify the output.
"""
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal, localcontext
from math import isqrt
import hashlib,json
ROOT=Path(__file__).resolve().parents[2]
SOURCE=ROOT/'research-notes/binary-push/certificate-alpha-0758067460.json'
OUTPUT=ROOT/'lean-formalization/Sarkozy/BinaryRows.lean'
raw=SOURCE.read_bytes();data=json.loads(raw)
f=F(data['f']); fn=154942497274; fd=10**12
GRID=10**12; POWERS=10**10; DEN=10**26; STEPS=36
scales=sorted({int(F(*b['scale'])*GRID) for s in data['states'] for b in s['branches']})
count=len(scales); powers=[]; lowers=[]; uppers=[]
for number in scales:
 q=F(number,GRID)
 with localcontext() as context:
  context.prec=100
  value=(Decimal(q.numerator)/q.denominator)**(Decimal(f.numerator)/f.denominator)
  proposal=int(value*POWERS)-1
 lower=[number*(DEN//GRID)]; upper=[proposal*(DEN//POWERS)]
 for _ in range(STEPS):
  lower.append(isqrt(lower[-1]*DEN))
  z=isqrt(upper[-1]*DEN)
  upper.append(z+(z*z < upper[-1]*DEN))
 assert all(x>0 for x in lower+upper)
 assert all(lower[j+1]**2<=lower[j]*DEN for j in range(STEPS))
 assert all(upper[j]*DEN<=upper[j+1]**2 for j in range(STEPS))
 assert (upper[-1]-DEN)*lower[-1]*fd <= fn*DEN*(lower[-1]-DEN)
 powers.append(proposal);lowers.append(lower);uppers.append(upper)
indices=[]; vector=list(map(F,data['vector'])); growth=F(data['a']);margins=[]
for s,state in enumerate(data['states']):
 row=[0]*4; lhs=F(0)
 for branch in state['branches']:
  j=scales.index(int(F(*branch['scale'])*GRID));row[branch['r']]=j
  lhs+=F(powers[j],POWERS)*vector[branch['child']]
 assert lhs>growth*vector[s]
 margins.append(lhs-growth*vector[s]);indices.append(row)
def vec(items,indent='  ',group=3):
 return '!['+(',\n'+indent).join(', '.join(map(str,items[j:j+group])) for j in range(0,len(items),group))+']'
def matrix(rows):return '!['+',\n    '.join(vec(row,'      ') for row in rows)+']'
header=f"""
namespace RecordBinary

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

-- Source JSON SHA-256: {hashlib.sha256(raw).hexdigest()}
-- {count} distinct downward-rounded scales; {STEPS} square-root steps.
private def rowScaleNumerator : Fin {count} → ℕ :=
  {vec(scales,'    ')}

private def rowLowerNumerator : Fin {count} → ℕ :=
  {vec(powers,'    ')}

private def rowLowerLadder : Fin {count} → Fin {STEPS+1} → ℕ :=
  {matrix(lowers)}

private def rowUpperLadder : Fin {count} → Fin {STEPS+1} → ℕ :=
  {matrix(uppers)}

private def rowScale (i : Fin {count}) : ℚ := (rowScaleNumerator i : ℚ)/{GRID}
private def rowLower (i : Fin {count}) : ℚ := (rowLowerNumerator i : ℚ)/{POWERS}

private def rowBranchIndex : Fin 25 → Fin 4 → Fin {count} :=
  {matrix(indices)}

private def rowIndex (s : Fin 25) (r : ℤ) : Fin {count} :=
  rowBranchIndex s ⟨r.toNat%4, Nat.mod_lt _ (by decide)⟩
"""
proof=Path(__file__).with_name('binary-rows-proof.txt').read_text()
proof=proof.replace('@COUNT@',str(count)).replace('@STEPS@',str(STEPS)).replace('@DEN@',str(DEN)).replace('@GRID@',str(GRID)).replace('@POWERS@',str(POWERS)).replace('@LFACTOR@',str(DEN//GRID)).replace('@UFACTOR@',str(DEN//POWERS))
original=OUTPUT.read_text();before=original.split('-- BEGIN GENERATED BINARY POWER CERTIFICATES')[0];after=original.split('-- END GENERATED BINARY POWER CERTIFICATES')[1]
OUTPUT.write_text(before+'-- BEGIN GENERATED BINARY POWER CERTIFICATES'+header+proof+'\n-- END GENERATED BINARY POWER CERTIFICATES'+after)
print(json.dumps({'distinct_scales':count,'levels':STEPS+1,'integer_entries':2*count*(STEPS+1),'minimum_exact_row_surplus':str(min(margins)),'minimum_row_surplus_decimal':float(min(margins)),'output_bytes':OUTPUT.stat().st_size},indent=2))
