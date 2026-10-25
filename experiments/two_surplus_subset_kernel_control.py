"""Exact overlap moments and uniform-cardinality superset kernel; not proof."""
from pathlib import Path
from fractions import Fraction as Q
from math import factorial as f,comb
import random,json,hashlib
SEED=2026102504;rng=random.Random(SEED);checks=[]
def ck(l,v):
 assert v,l
 checks.append(l)
def power(d,n,p):
 v=Q(1)
 for j in range(n):v*=Q(f(d+j+p),f(d+j))
 return v
for n in range(11):
 for a in range(n+1):
  for b in range(n+1):
   for c in range(max(0,a+b-n),min(a,b)+1):
    M=power(n-c,c,2)*power(n-a,a-c,1)*power(n-b,b-c,1)
    closed=Q(f(n)*f(n+1),(n-c+1)*f(n-a)*f(n-b))
    ck('overlap '+str((n,a,b,c)),M==closed)
 for u in range(n+1):
  ck('superset kernel '+str((n,u)),sum((Q(comb(n-u,k-u),(n+1)*comb(n,k)) for k in range(u,n+1)),Q(0))==Q(1,u+1))
for n in range(9):
 for x in [Q(0),Q(rng.randint(1,6),3),Q(2)]:
  total=Q(0)
  for a in range(n+1):
   for c in range(a+1):
    for b in range(n-a+1):
     total+=Q(comb(n,a)*comb(a,c)*comb(n-a,b),(n-c+1)*f(n-a)*f(n-c-b))*x**(2*n-a-c-b)
  A=lambda j:sum((Q(comb(j,k),f(k))*x**k for k in range(j+1)),Q(0))
  average=sum((A(j)**2 for j in range(n+1)),Q(0))/(n+1)
  ck('Laguerre square average '+str((n,x)),total==average)
  if n>0 and x>0:ck('omitted average divisor rejected '+str((n,x)),total!=sum(A(j)**2 for j in range(n+1)))
result=dict(seed=SEED,checks=len(checks),status='PASS',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),controls=checks,scope='Exact overlap-factorial reduction and finite superset kernel, known n0/n1 calibration; not general proof or new actual law')
Path('verification/sheaf_wishart/quota-20261022-0949/two-surplus-subset-kernel-control.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('PASS',len(checks),'exact controls')
