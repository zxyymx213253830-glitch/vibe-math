"""Positive determinant ensemble normalization controls; before source, not proof."""
from pathlib import Path
import hashlib,itertools,json,math,random
import sympy as s
seed=2026102412;rng=random.Random(seed);checks=0;t=s.symbols('t')
for n in range(5):
 for r in range(5):
  a=list(range(5));w=[rng.randrange(1,4) for _ in a]
  f=lambda i,k:(a[k]+r)**i
  E=[k<=r for k in a]
  H=s.Matrix(n,n,lambda i,j:sum(w[k]*f(i,k)*f(j,k) for k in a))
  A=s.Matrix(n,n,lambda i,j:sum(w[k]*f(i,k)*f(j,k) for k in a if E[k]))
  B=H-A;z=H.det();assert z>0;checks+=1
  masses=[0]*(n+1)
  for p in itertools.product(a,repeat=n):
   v=math.prod(w[k] for k in p)*s.Matrix(n,n,lambda i,j:f(i,p[j])).det()**2
   masses[sum(E[k] for k in p)]+=v
  assert sum(masses)==math.factorial(n)*z;checks+=1
  P=s.Poly((B+t*A).det(),t)
  for k in range(n+1):
   prob=s.Rational(masses[k],math.factorial(n)*z)
   assert prob==P.nth(k)/z and 0<=prob<=1;checks+=1
# Rank-deficient basis gives zero mass; unconditional probability claim is invalid.
assert s.Matrix([[2,2],[2,2]]).det()==0;checks+=1
out=dict(seed=seed,checks=checks,status='PASS exact controls; not proof',reference='Positive discrete squared-determinant ensemble total mass n!detH, normalized count coefficient/detH, empty dimension, rank deficient zero-mass negative calibration',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('verification/sheaf_wishart/quota-20261022-0949/determinant-ensemble-count-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out))
