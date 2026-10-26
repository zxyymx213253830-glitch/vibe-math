"""Exact zero-threshold noncentral moment blocks and determinant calibration."""
from pathlib import Path
import math,json,hashlib
import sympy as S
import numpy as np
SEED=2026102604;rng=np.random.default_rng(SEED);checks=[]
def ck(name,p):
    assert p,name
    checks.append(name)
def P(q,k,x):
    return math.factorial(k)*sum(S.binomial(q+k,k-j)*x**j/S.factorial(j) for j in range(k+1))
for s in range(6):
    for q in range(4):
        t=s+q
        for L in range(s+1):
            p=s-L;lam=[S.Integer(L+1-j)**2 for j in range(L)]
            A=S.Matrix(s,s,lambda i,j:lam[j]**S.Rational(q,2)*P(q,s-i-1,lam[j]) if j<L else S.factorial(q+s-i-1+s-j-1))
            B=S.Matrix(s,s,lambda i,j:S.Integer(2)**S.Rational(2*(i+1)-s-t,2)*(S.sqrt(2*lam[j]))**q*2**(s-i-1)*P(q,s-i-1,lam[j]) if j<L else S.factorial(t+s-(i+1)-(j+1)))
            ck(f'original prefactor and row-order {s,q,L}',(A-B).applyfunc(S.simplify)==S.zeros(s))
            D=S.prod(x**(S.Rational(q,2)+p) for x in lam)*S.prod(lam[i]-lam[j] for i in range(L) for j in range(i+1,L))*S.prod(S.factorial(h)*S.factorial(q+h) for h in range(p))
            ck(f'candidate mixed confluent determinant {s,q,L}',S.simplify(A.det()-D)==0)
            for h in range(p):
                for k in range(s):
                    x=S.Symbol('x')
                    rhs=sum(S.factorial(h)*S.binomial(q+h,h-j)*S.factorial(q+j)/S.factorial(j)*S.diff(P(q,k,x),x,j).subs(x,0) for j in range(h+1))
                    ck(f'Gamma derivative column {s,q,L,h,k}',S.simplify(rhs-S.factorial(q+k+h))==0)
            if L>=2:
                rep=lam.copy();rep[-1]=rep[0]
                R=S.Matrix(s,s,lambda i,j:rep[j]**S.Rational(q,2)*P(q,s-i-1,rep[j]) if j<L else S.factorial(q+s-i-1+s-j-1))
                ck(f'repeated noncentrality determinant vanishes {s,q,L}',R.det()==0)
for _ in range(12):
    q,k,h=map(int,rng.integers(0,7,size=3));x=S.Symbol('x')
    rhs=sum(S.factorial(h)*S.binomial(q+h,h-j)*S.factorial(q+j)/S.factorial(j)*S.diff(P(q,k,x),x,j).subs(x,0) for j in range(h+1))
    ck(f'independent derivative column {q,k,h}',S.simplify(rhs-S.factorial(q+k+h))==0)
ck('wrong Vandermonde direction negative',(S.Matrix([[5,2],[1,1]]).det())!=1-4)
result=dict(seed=SEED,status='PASS',checks=len(checks),controls=checks,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Exact original Psi(0) prefactor/degree and Gamma derivative columns; proposed mixed confluent determinant and repeated-parameter negative. Determinant formula remains calibration only until proved.')
Path('verification/sheaf_wishart/quota-20261022-0949/noncentral-psi-zero-moment-control.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('PASS',len(checks),'controls')
