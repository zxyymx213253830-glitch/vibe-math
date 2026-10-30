"""Exact finite reindex/column scaling of determinant polynomials, not proof."""
from pathlib import Path
import hashlib,json,random
import sympy as sp
from sympy.combinatorics import Permutation

rng=random.Random(2026103105)
t=sp.Symbol('t');checks=negatives=0
for n in range(0,5):
 for trial in range(5):
  A=sp.Matrix(n,n,lambda i,j:rng.randrange(-5,6))
  B=sp.Matrix(n,n,lambda i,j:rng.randrange(-5,6))
  row=list(range(n));col=list(range(n));rng.shuffle(row);rng.shuffle(col)
  d=[rng.randrange(1,6) for _ in range(n)]
  P=B+t*A
  Q=sp.Matrix(n,n,lambda i,j:d[j]*P[row[i],col[j]])
  sign=Permutation(row).signature()*Permutation(col).signature() if n else 1
  assert sp.expand(Q.det()-sign*sp.prod(d)*P.det())==0
  checks+=1
  if n>=2 and sign==-1 and P.det()!=0:
   assert sp.expand(Q.det()-sp.prod(d)*P.det())!=0
   negatives+=1
assert negatives>0
result=dict(seed=2026103105,status='PASS',checks=checks,negative_controls=negatives,
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),not_a_proof=True,
 scope='exact finite polynomial determinant reindex and column-scale transport')
out=Path(__file__).resolve().parents[1]/'verification/sheaf_wishart/quota-20261022-0949/row-affine-transport-control.json'
out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('PASS',checks,'negative',negatives)
