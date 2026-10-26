"""Finite Cauchy-Binet noncentral kernel positivity controls, NOT a proof/law."""
from pathlib import Path
from itertools import combinations
import sympy as S
import numpy as np
import mpmath as mp
import json,hashlib
SEED=2026102610;rng=np.random.default_rng(SEED);checks=[]
def ck(n,b):
 assert b,n
 checks.append(n)
def core(p,lam,xx,J,q):
 n=len(xx)
 X=S.Matrix(n,J+1,lambda i,m:xx[i]**m)
 C=S.Matrix(J+1,n,lambda m,j:S.Integer(m==j) if j<p else lam[j-p]**m/(S.factorial(m)*S.factorial(q+m)))
 return X,C
for s in range(5):
 for L in range(s+1):
  p=s-L
  xx=[S.Integer(int(v)) for v in sorted(rng.choice(np.arange(1,14),size=s,replace=False))]
  lam=[S.Integer(int(v))**2 for v in sorted(rng.choice(np.arange(1,9),size=L,replace=False))]
  for q in range(3):
   for J in range(max(s-1,0),max(s-1,0)+3):
    X,C=core(p,lam,xx,J,q);A=X*C
    terms=[X[:,list(E)].det()*C[list(E),:].det() for E in combinations(range(J+1),s)]
    ck(f'independent Cauchy-Binet identity {s,L,q,J}',sum(terms)==A.det())
    ck(f'each finite coefficient minor product nonnegative {s,L,q,J}',all(v>=0 for v in terms))
    ck(f'finite kernel strictly positive including empty {s,L,q,J}',A.det()>0)
   if s>=2:
    X,C=core(p,lam,xx,s-2,q)
    ck(f'insufficient truncation rank negative {s,L,q}',(X*C).det()==0)
    rep=xx.copy();rep[-1]=rep[0]
    X,C=core(p,lam,rep,s+1,q)
    ck(f'repeated physical eigenvalue negative {s,L,q}',(X*C).det()==0)
   if L>=2:
    rep=lam.copy();rep[-1]=rep[0]
    X,C=core(p,rep,xx,s+1,q)
    ck(f'repeated noncentrality negative {s,L,q}',(X*C).det()==0)
   if p>0 and L>0:
    zero=lam.copy();zero[0]=S.Integer(0)
    X,C=core(p,zero,xx,s+1,q)
    ck(f'zero noncentrality conflicts with central coefficient negative {s,L,q}',(X*C).det()==0)
mp.mp.dps=70
for q in range(4):
 for z in [mp.mpf('0.01'),mp.mpf('0.7'),mp.mpf('3'),mp.mpf('8')]:
  exact=mp.besseli(q,2*mp.sqrt(z))/z**(mp.mpf(q)/2)
  direct=mp.fsum(z**m/(mp.factorial(m)*mp.factorial(q+m)) for m in range(100))
  ck(f'Bessel-series closed-form calibration {q,str(z)}',abs(direct-exact)<mp.mpf('1e-60'))
ck('two-column reversal sign negative',S.Matrix([[1,1],[1,2]]).det()==-S.Matrix([[1,1],[2,1]]).det())
R=Path(__file__).resolve().parents[1]
d=dict(seed=SEED,status='PASS',checks=len(checks),controls=checks,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Finite exact minor controls and Bessel-series calibration only. No general total positivity, infinite limiting exchange, probability normalization or actual G2 law.')
(R/'verification/sheaf_wishart/quota-20261022-0949/noncentral-candidate-total-positivity-control.json').write_text(json.dumps(d,indent=2)+'\n',encoding='utf-8');print('PASS',len(checks),'controls; not a proof or law')
