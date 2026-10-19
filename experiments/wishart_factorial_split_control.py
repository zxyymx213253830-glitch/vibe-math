"""Deterministic exact Gamma-factorial product controls; no probability proof."""
from pathlib import Path
from fractions import Fraction as F
import math,json,hashlib
fac=math.factorial
def moment(d,n,p):return math.prod(F(fac(d+j+p),fac(d+j)) for j in range(n))
records=[]
for d in range(13):
 for n in range(13):
  for p in range(5):
   for q in range(5):assert moment(d,n,p+q)==moment(d,n,p)*moment(d+p,n,q)
  closed=F(fac(d+n)*fac(d+n+1),fac(d)*fac(d+1))
  assert moment(d,n,2)==closed
  assert moment(d,n,1)==F(fac(d+n),fac(d))
  records.append(dict(d=d,n=n,second_moment=str(closed)))
result=dict(seed=None,status='PASS exact factorial cocycle and p1/p2 closed product controls d,n0..12 p,q0..4; not proof',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),records=records)
p=Path(__file__).resolve().parents[1]/'verification/central_mixed_moments/factorial-split-control.json';p.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8');print(result['status'])
