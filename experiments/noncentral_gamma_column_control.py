"""Exact coefficient/Gamma-column reduction controls; no general proof."""
from pathlib import Path
import sympy as S
import numpy as np
import math,json,hashlib
SEED=2026102606;rng=np.random.default_rng(SEED);x=S.Symbol('x');checks=[]
def ck(name,b):
 assert b,name
 checks.append(name)
def P(q,k):
 return S.Poly(S.factorial(k)*sum(S.binomial(q+k,k-j)*x**j/S.factorial(j) for j in range(k+1)),x)
for q in range(5):
 for k in range(7):
  p=P(q,k)
  for j in range(9):
   c=p.nth(j)
   ck(f'global coefficient including above-degree {q,k,j}',c==S.factorial(k)*S.binomial(q+k,q+j)/S.factorial(j))
   ck(f'weighted coefficient binomial {q,k,j}',S.factorial(q+j)*c==S.factorial(q+k)*S.binomial(k,j))
  for h in range(7):
   rhs=sum(S.factorial(h)*S.binomial(q+h,h-j)*S.factorial(q+j)*p.nth(j) for j in range(h+1))
   ck(f'Gamma column coefficient expansion {q,k,h}',rhs==S.factorial(q+k+h))
for p in range(7):
 for q in range(4):
  T=S.Matrix(p,p,lambda j,h:S.factorial(h)*S.binomial(q+h,h-j)*S.factorial(q+j) if j<=h else 0)
  ck(f'upper triangular Gamma column transform determinant {p,q}',T.det()==S.prod(S.factorial(h)*S.factorial(q+h) for h in range(p)))
  ck(f'Gamma column transform invertible including empty {p,q}',T.det()!=0)
for _ in range(15):
 q,k,j=map(int,rng.integers(0,9,size=3))
 ck(f'random weighted coefficient {q,k,j}',S.factorial(q+j)*P(q,k).nth(j)==S.factorial(q+k)*S.binomial(k,j))
ck('truncated-subtraction coefficient negative control',P(2,1).nth(3)!=S.factorial(1)*S.binomial(3,max(0,1-3))/S.factorial(3))
ck('missing factorial diagonal negative control',S.Matrix([[2,6],[0,6]]).det()!=6)
R=Path(__file__).resolve().parents[1]
d=dict(seed=SEED,status='PASS',checks=len(checks),controls=checks,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Calibration only, including finite gamma column transform; no actual law or general proof.')
(R/'verification/sheaf_wishart/quota-20261022-0949/noncentral-gamma-column-control.json').write_text(json.dumps(d,indent=2)+'\n',encoding='utf-8')
print('PASS',len(checks),'exact controls; not proof')
