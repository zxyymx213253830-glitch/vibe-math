"""Seeded exact monic/evaluation/full-rank Psi(0) controls, not a proof."""
from pathlib import Path
import math,json,hashlib
import numpy as np
import sympy as S
SEED=2026102605
rng=np.random.default_rng(SEED)
x=S.Symbol('x');checks=[]
def ck(name,condition):
    assert condition,name
    checks.append(name)
def P(q,k,z):
    return S.factorial(k)*sum(S.binomial(q+k,k-j)*z**j/S.factorial(j) for j in range(k+1))
for q in range(6):
    for k in range(8):
        p=S.Poly(P(q,k,x),x)
        ck(f'monic and degree {q,k}',p.degree()==k and p.LC()==1)
        ck(f'central Gamma calibration {q,k}',P(q,k,0)==S.factorial(q+k)/S.factorial(q))
        ck(f'top derivative calibration {q,k}',S.diff(p.as_expr(),x,k)==S.factorial(k))
for n in range(7):
    for q in range(5):
        points=[S.Rational(int(v),7) for v in rng.choice(np.arange(-40,41),size=n,replace=False)]
        A=S.Matrix(n,n,lambda i,j:P(q,j,points[i]))
        v=S.prod(points[j]-points[i] for i in range(n) for j in range(i+1,n))
        ck(f'signed real ascending evaluation determinant {n,q}',S.simplify(A.det()-v)==0)
        lam=[S.Integer(j+1)**2 for j in range(n)][::-1]
        B=S.Matrix(n,n,lambda i,j:lam[j]**S.Rational(q,2)*P(q,n-i-1,lam[j]))
        det=S.prod(y**S.Rational(q,2) for y in lam)*S.prod(lam[i]-lam[j] for i in range(n) for j in range(i+1,n))
        ck(f'full-rank original Psi zero determinant {n,q}',S.simplify(B.det()-det)==0)
        ck(f'positive distinct nonzero including empty {n,q}',B.det()!=0)
        if n>=2:
            repeated=lam.copy();repeated[-1]=repeated[0]
            C=S.Matrix(n,n,lambda i,j:repeated[j]**S.Rational(q,2)*P(q,n-i-1,repeated[j]))
            ck(f'repeated parameter negative control {n,q}',C.det()==0)
        if n>=1 and q>0:
            zero=lam.copy();zero[-1]=S.Integer(0)
            C=S.Matrix(n,n,lambda i,j:zero[j]**S.Rational(q,2)*P(q,n-i-1,zero[j]))
            ck(f'zero parameter positive-surplus negative control {n,q}',C.det()==0)
ck('row reversal sign negative',S.Matrix([[P(2,i,z) for z in [1,4]] for i in range(2)]).det()==3)
ck('empty determinant is one',S.zeros(0).det()==1)
R=Path(__file__).resolve().parents[1]
result=dict(seed=SEED,status='PASS',checks=len(checks),controls=checks,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Exact calibration only. No general determinant or probability proof.')
(R/'verification/sheaf_wishart/quota-20261022-0949/noncentral-full-rank-determinant-control.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('PASS',len(checks),'exact controls; not proof')
