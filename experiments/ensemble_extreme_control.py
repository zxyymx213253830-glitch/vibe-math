"""Exact finite-measure determinant-ensemble all-in/all-out controls."""
from itertools import product
from pathlib import Path
import hashlib,json,random
import sympy as sp

rng=random.Random(2026103005)
checks=0
points=[sp.Rational(i,2) for i in range(1,7)]
weights=[sp.Rational(rng.randint(1,8),rng.randint(2,9)) for _ in points]
for n in range(5):
 def detmat(z):
  if n==0:return sp.Integer(1)
  return sp.Matrix([[z[j]**i for j in range(n)] for i in range(n)]).det()
 for selected in [[],points[:2],points[1::2],points]:
  M=sp.Matrix(n,n,lambda i,j:sum(weights[t]*points[t]**(i+j) for t in range(len(points))))
  A=sp.Matrix(n,n,lambda i,j:sum(weights[t]*points[t]**(i+j) for t in range(len(points)) if points[t] in selected))
  B=sp.Matrix(n,n,lambda i,j:sum(weights[t]*points[t]**(i+j) for t in range(len(points)) if points[t] not in selected))
  denom=sp.factorial(n)*M.det()
  allin=allout=sp.Integer(0)
  for idx in product(range(len(points)),repeat=n):
   z=[points[t] for t in idx]
   mass=sp.prod(weights[t] for t in idx)*detmat(z)**2
   if all(v in selected for v in z):allin+=mass
   if all(v not in selected for v in z):allout+=mass
  assert denom>0 and allin/denom==A.det()/M.det() and allout/denom==B.det()/M.det()
  checks+=2
out={'seed':2026103005,'status':'PASS','checks':checks,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'not_a_proof':True,'scope':'finite exact generic all-in/all-out determinant ratios; no physical Wishart law'}
p=Path(__file__).resolve().parents[1]/'verification/sheaf_wishart/quota-20261022-0949/ensemble-extreme-control.json'
p.write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print('PASS',checks,'seed',2026103005)
