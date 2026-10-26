"""Exact C * coefficient-confluent V * Gamma-column block controls."""
from pathlib import Path
import sympy as S
import numpy as np
import json,hashlib
SEED=2026102608;rng=np.random.default_rng(SEED);x=S.Symbol('x');checks=[]
def ck(n,b):
 assert b,n
 checks.append(n)
def P(q,k):
 return S.Poly(S.factorial(k)*sum(S.binomial(q+k,k-j)*x**j/S.factorial(j) for j in range(k+1)),x)
for p in range(5):
 for L in range(5):
  n=p+L
  for q in range(4):
   pol=[P(q,k) for k in range(n)]
   lam=[S.Integer(int(v)) for v in rng.choice(np.arange(1,14),size=L,replace=False)]
   C=S.Matrix(n,n,lambda i,j:pol[i].nth(j))
   V=S.Matrix(n,n,lambda i,j:S.Integer(i==j) if j<p else lam[j-p]**i)
   T=S.Matrix(p,p,lambda j,h:S.factorial(h)*S.binomial(q+h,h-j)*S.factorial(q+j) if j<=h else 0)
   G=S.diag(T,S.eye(L))
   M=S.Matrix(n,n,lambda i,j:S.factorial(q+i+j) if j<p else pol[i].eval(lam[j-p]))
   ck(f'monic coefficient basis unit determinant {p,L,q}',C.det()==1)
   ck(f'exact mixed moment factorization {p,L,q}',C*V*G==M)
   d=S.prod(y**p for y in lam)*S.prod(lam[j]-lam[i] for i in range(L) for j in range(i+1,L))*S.prod(S.factorial(h)*S.factorial(q+h) for h in range(p))
   ck(f'mixed moment determinant {p,L,q}',M.det()==d)
   ck(f'mixed moment invertible including empty {p,L,q}',M.det()!=0)
   if n>=2 and p>0 and L>0:
    ck(f'wrong coefficient transpose negative {p,L,q}',C.T*V*G!=M)
R=Path(__file__).resolve().parents[1]
d=dict(seed=SEED,status='PASS',checks=len(checks),controls=checks,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Finite exact calibration only, not general matrix factorization or a Wishart law.')
(R/'verification/sheaf_wishart/quota-20261022-0949/mixed-noncentral-moment-matrix-control.json').write_text(json.dumps(d,indent=2)+'\n',encoding='utf-8');print('PASS',len(checks),'exact controls; not proof')
