"""Exact grouped-cardinality hard-edge coefficient audit, not general proof."""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,math
fac=math.factorial;choose=math.comb
def mass(d,n,q):return math.prod(F(fac(d+j+q),fac(d+j)) for j in range(n))
records=[]
for N in range(1,13):
 for d in range(3):
  k=d+1;Q=[F(0) for _ in range(k+1)]
  if d==0:Q[0]=F(1)
  elif d==1:
   Q=[F(choose(N,j),fac(j)) if j<=N else F(0) for j in range(k+1)]
  else:
   for a in range(N+1):
    for c in range(a+1):
     for b in range(N-a+1):
      j=N-a+N-c-b
      if j<=k:
       moment=mass(N-c,c,2)*mass(N-a,a-c,1)*mass(N-c-b,b,1)
       Q[j]+=F(choose(N,a)*choose(a,c)*choose(N-a,b),fac(N)*fac(N+1))*moment
  coeff=[]
  for j in range(k+1):coeff.append(-sum(F((-N)**i,fac(i))*Q[j-i] for i in range(j+1))+(1 if j==0 else 0))
  assert all(coeff[j]==0 for j in range(k))
  target=F(fac(N+d),fac(N-1)*fac(d+1)**2)
  assert coeff[k]==target
  records.append(dict(N=N,d=d,Qlow=list(map(str,Q)),sharp=str(coeff[k]),candidate=str(target)))
result=dict(seed=None,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),status='PASS exact grouped-cardinality coefficients N1..12 d0..2 against simplified candidate; not proof',records=records)
p=Path(__file__).resolve().parents[1]/'verification/central_mixed_moments/simplified-coefficient-control.json';p.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8');print(result['status'])
