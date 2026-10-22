"""Fixed-seed exact subset/fiber controls. Evidence, not a general proof."""
from pathlib import Path
from itertools import combinations, permutations, product
import sys, json, hashlib, time, math
import numpy as np
import sympy as s
seed=2026102204; rng=np.random.default_rng(seed); checks=[]; start=time.monotonic()
def mat(m,n):
 return s.Matrix(m,n,lambda i,j:s.Rational(int(rng.integers(-2,3)),2)+s.I*s.Rational(int(rng.integers(-2,3)),2))
def same(name,a,b):
 assert s.expand(a-b)==0,name
 checks.append(name)
for q in range(4):
 for m in range(5):
  A=mat(q,m); B=mat(m,q); canonical=s.S.Zero; fibers={}
  for f in product(range(m),repeat=q):
   term=s.expand(A.extract(range(q),f).det()*B.extract(f,range(q)).det())
   image=tuple(sorted(set(f)))
   fibers[image]=s.expand(fibers.get(image,0)+term)
   if len(image)!=q: same(f'repeated-row-{q}-{m}-{f}',term,0)
  for S in combinations(range(m),q):
   t=s.expand(A.extract(range(q),S).det()*B.extract(S,range(q)).det())
   same(f'fiber-{q}-{m}-{S}',fibers.get(S,0),math.factorial(q)*t)
   canonical+=t
   for f in permutations(S):
    same(f'reordering-{q}-{m}-{f}',A.extract(range(q),f).det()*B.extract(f,range(q)).det(),t)
  same(f'subset-CB-{q}-{m}',(A*B).det(),canonical)
  gram_sum=sum((s.expand(s.conjugate(B.extract(S,range(q)).det())*B.extract(S,range(q)).det()) for S in combinations(range(m),q)),s.S.Zero)
  same(f'gram-{q}-{m}',(B.conjugate().T*B).det(),gram_sum)
X=s.Matrix([[1,s.I],[2,3],[s.I,1]])
for q in range(3):
 t=s.Symbol('t'); poly=s.Poly((s.eye(2)+t*(X.conjugate().T*X)).det(),t)
 value=sum((s.expand(s.conjugate(X.extract(S,T).det())*X.extract(S,T).det()) for S in combinations(range(3),q) for T in combinations(range(2),q)),s.S.Zero)
 same(f'all-minors-coefficient-{q}',poly.nth(q),value)
assert s.eye(2).det()!=2*s.eye(2).det();checks.append('spurious-factorial-negative-control')
assert s.I*s.I!=s.conjugate(s.I)*s.I;checks.append('missing-conjugate-negative-control')
out=dict(status='PASS exact controls; NOT general proof',seed=seed,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),checks=len(checks),details=checks,seconds=time.monotonic()-start,scope='q0..3,m0..4 rational-complex factors; fibers, ordering invariance, empty/q>m, Gram and all-minors coefficients')
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:out[k] for k in ['status','checks','seconds']}))
