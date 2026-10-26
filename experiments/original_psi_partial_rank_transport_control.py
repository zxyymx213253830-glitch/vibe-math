"""Exact original Psi(0) row/column reindexing and column-power controls."""
from pathlib import Path
import sympy as S
import numpy as np
import json,hashlib
SEED=2026102609;rng=np.random.default_rng(SEED);checks=[]
def ck(n,b):
 assert b,n
 checks.append(n)
def P(q,k,x):
 return S.factorial(k)*sum(S.binomial(q+k,k-j)*x**j/S.factorial(j) for j in range(k+1))
for s in range(8):
 for L in range(s+1):
  p=s-L
  lam=[S.Integer(int(v))**2 for v in rng.choice(np.arange(1,16),size=L,replace=False)]
  rows=list(range(s))[::-1];cols=[s-1-h for h in range(p)]+list(range(L))
  ck(f'row/column bijections {s,L}',sorted(rows)==list(range(s)) and sorted(cols)==list(range(s)))
  for q in range(4):
   A=S.Matrix(s,s,lambda i,j:lam[j]**S.Rational(q,2)*P(q,s-i-1,lam[j]) if j<L else S.factorial(q+s-i-1+s-j-1))
   M=S.Matrix(s,s,lambda k,j:S.factorial(q+k+j) if j<p else P(q,k,lam[j-p]))
   w=[S.Integer(1)]*p+[x**S.Rational(q,2) for x in lam]
   B=S.Matrix(s,s,lambda i,j:A[rows[i],cols[j]])
   ck(f'original Psi reindex and powers {s,L,q}',B==M*S.diag(*w))
   ck(f'original Psi normalizer nonzero including empty {s,L,q}',A.det()!=0)
   if L>=2:
    rep=lam.copy();rep[-1]=rep[0]
    E=S.Matrix(s,s,lambda i,j:rep[j]**S.Rational(q,2)*P(q,s-i-1,rep[j]) if j<L else S.factorial(q+s-i-1+s-j-1))
    ck(f'repeated noncentrality negative {s,L,q}',E.det()==0)
ck('omitting central-column reversal negative',S.Matrix([[6,2],[2,1]]).det()!=S.Matrix([[2,6],[1,2]]).det())
R=Path(__file__).resolve().parents[1]
d=dict(seed=SEED,status='PASS',checks=len(checks),controls=checks,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Exact finite calibration only; not the general transport proof or actual Wishart density.')
(R/'verification/sheaf_wishart/quota-20261022-0949/original-psi-partial-rank-transport-control.json').write_text(json.dumps(d,indent=2)+'\n',encoding='utf-8');print('PASS',len(checks),'exact controls; not proof')
