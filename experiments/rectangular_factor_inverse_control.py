"""Exact fixed rectangular factor normalization and physical sample controls."""
from pathlib import Path
import hashlib,json,random
import sympy as s
seed=2026102238;rng=random.Random(seed);cases=checks=0
for m in [1,2,3]:
 for n in [1,2,3]:
  for extra in [1,2]:
   p=n+extra;perm=list(range(p));rng.shuffle(perm)
   U=s.eye(p)[:,perm[:n]]
   R=s.eye(n)
   for i in range(n):
    R[i,i]=i+2
    for j in range(i+1,n):R[i,j]=rng.randrange(-2,3)+s.I*rng.randrange(-1,2)
   B=U*R;S=R.inv()
   assert U.H*U==s.eye(n) and (B*S-U).applyfunc(s.simplify)==s.zeros(p,n);checks+=2
   assert B.rank()==n and S.det()!=0;checks+=2
   M=s.Matrix(m,n,lambda i,j:s.Rational(rng.randrange(-3,4),2)+s.I*s.Rational(rng.randrange(-2,3),3))
   for t in range(2):
    Z=s.Matrix(m,p,lambda i,j:s.Rational(rng.randrange(-3,4),2)+s.I*s.Rational(rng.randrange(-2,3),3))
    assert ((Z*B+M)*S-Z*U-M*S).applyfunc(s.simplify)==s.zeros(m,n);checks+=1
   cases+=1
assert s.Matrix([[2]]).H*s.Matrix([[2]])==s.Matrix([[4]]);checks+=1
out=dict(status='PASS exact factor controls, not Gaussian/inverse proof',seed=seed,
 checks=checks,cases=cases,reference='coordinate isometry U; nonunitary invertible R; scalar B=2 gives Gram scale4',
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('verification/sheaf_wishart/quota-20261022-0949/rectangular-factor-inverse-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
