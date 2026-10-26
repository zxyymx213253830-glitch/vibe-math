"""Original Psi(0) norm product including zero/repeated noncentral parameters."""
from pathlib import Path
import sympy as S
import numpy as np
import json,hashlib
SEED=2026102611;rng=np.random.default_rng(SEED);checks=[]
def ck(n,b):
 assert b,n
 checks.append(n)
def P(q,k,x):
 return S.factorial(k)*sum(S.binomial(q+k,k-j)*x**j/S.factorial(j) for j in range(k+1))
for s in range(7):
 for L in range(s+1):
  p=s-L
  for q in range(4):
   for case in range(3):
    if case==0:lam=[S.Rational(int(v),3)**2 for v in rng.choice(np.arange(1,18),size=L,replace=False)]
    elif case==1:lam=[S.Integer(j%2)**2 for j in range(L)]
    else:lam=[S.Rational(4,9)]*L
    A=S.Matrix(s,s,lambda i,j:lam[j]**S.Rational(q,2)*P(q,s-i-1,lam[j]) if j<L else S.factorial(q+s-i-1+s-j-1))
    power=S.prod(x**S.Rational(q,2) for x in lam)*S.prod(x**p for x in lam)
    v=S.prod(abs(lam[j]-lam[i]) for i in range(L) for j in range(i+1,L))
    gamma=S.prod(S.factorial(h)*S.factorial(q+h) for h in range(p))
    rhs=power*v*gamma
    ck(f'original norm explicit product {s,L,q,case}',S.simplify(abs(A.det())-rhs)==0)
    ck(f'nonnegative norm product {s,L,q,case}',rhs>=0)
ck('zero-to-zero exponent convention',S.Integer(0)**0==1)
ck('squared Vandermonde negative control',abs(S.Matrix([[5,2],[1,1]]).det())!=abs(S.Integer(1)-4)**2)
R=Path(__file__).resolve().parents[1]
d=dict(seed=SEED,status='PASS',checks=len(checks),controls=checks,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Exact finite calibration only; not general norm-product proof or a probability law.')
(R/'verification/sheaf_wishart/quota-20261022-0949/original-psi-norm-product-control.json').write_text(json.dumps(d,indent=2)+'\n',encoding='utf-8');print('PASS',len(checks),'exact controls; not proof')
