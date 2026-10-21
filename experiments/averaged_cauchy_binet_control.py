"""Exact controls for the permutation-averaged rectangular identity, not a proof."""
from pathlib import Path
from itertools import product
import sys,json,hashlib,time
import sympy as s
import numpy as np
seed=2026102201;rng=np.random.default_rng(seed);checks=[];start=time.monotonic()
def mat(m,n):return s.Matrix(m,n,lambda i,j:s.Rational(int(rng.integers(-2,3)),2)+s.I*s.Rational(int(rng.integers(-2,3)),2))
def test(name,lhs,rhs):
 assert s.expand(lhs-rhs)==0,name
 checks.append(name)
for q in range(4):
 for m in range(5):
  A=mat(q,m);B=mat(m,q)
  terms=[s.expand(A.extract(range(q),f).det()*B.extract(f,range(q)).det()) for f in product(range(m),repeat=q)]
  test(f'factorial-averaged-rectangular-{q}-{m}',s.factorial(q)*(A*B).det(),sum(terms,s.S.Zero))
  G=B.conjugate().T*B
  squared=[]
  for f in product(range(m),repeat=q):
   d=s.expand(B.extract(f,range(q)).det());squared.append(s.expand(s.conjugate(d)*d))
  test(f'factorial-gram-squares-{q}-{m}',s.factorial(q)*G.det(),sum(squared,s.S.Zero))
  if q<=m and q:
   f=tuple(range(q));d=s.expand(B.extract(f,range(q)).det());v=s.expand(s.conjugate(d)*d)
   assert s.expand(s.factorial(q)*G.det()-v)>=0
   checks.append(f'single-minor-domination-{q}-{m}')
test('empty-index-convention',s.factorial(0),1)
assert s.factorial(2)*s.eye(2).det()!=s.eye(2).det();checks.append('missing-factorial-negative-control')
assert (s.I*s.I)!=(s.conjugate(s.I)*s.I);checks.append('missing-conjugation-negative-control')
out=dict(status='PASS exact controls; NOT general proof',seed=seed,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),checks=len(checks),details=checks,seconds=time.monotonic()-start,scope='q0..3,m0..4 arbitrary rational-complex rectangular factors and Gram squares; includes q>m,empty and negative controls.')
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps({k:out[k] for k in ['status','checks','seconds']}))
