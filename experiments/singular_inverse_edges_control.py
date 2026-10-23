"""Exact fixed-floor/constant-model controls for two inverse-moment edges."""
from pathlib import Path
import hashlib,itertools,json,random
import sympy as s
seed=2026102237;rng=random.Random(seed);checks=cases=0
for m in [1,2,3]:
 for b in [0,1,2]:
  n=m+b;D=s.diag(*range(1,m+1))
  B=s.eye(b).row_join(s.zeros(b,m))
  A=s.Matrix(m,b,lambda i,j:s.Rational(rng.randrange(-2,3),2)+s.I*s.Rational(rng.randrange(-2,3),3))
  M=A.row_join(D);C=s.zeros(b,m).col_join(D.inv())
  assert B*C==s.zeros(b,m) and M*C==s.eye(m);checks+=2
  assert B.col_join(M).rank()-B.rank()==m;checks+=1
  for t in range(3):
   Z=s.Matrix(m,b,lambda i,j:s.Rational(rng.randrange(-3,4),2)+s.I*s.Rational(rng.randrange(-3,4),3))
   X=Z*B+M
   assert X*C==s.eye(m) and X.rank()==m;checks+=2
   G=(X*X.H-s.eye(m)).applyfunc(s.simplify)
   for size in range(1,m+1):
    for ix in itertools.combinations(range(m),size):
     assert s.simplify(G.extract(ix,ix).det())>=0;checks+=1
   if b==0:
    assert X==M and (X.H*X)==M.H*M;checks+=2
   cases+=1
out=dict(status='PASS exact edge controls, not probability proof',seed=seed,
 checks=checks,cases=cases,reference='scalar |z|^2+1>=1; fixed right inverse XC=I; zero-noise constant sample',
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('verification/sheaf_wishart/quota-20261022-0949/singular-inverse-edges-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
