"""Exact coefficient recurrence and confluent CD calibration, not proof."""
from pathlib import Path
import sympy as s
import random,json,hashlib
SEED=2026102506;rng=random.Random(SEED);X=s.Symbol('X');checks=[]
def A(n):return sum(s.binomial(n,k)*X**k/s.factorial(k) for k in range(n+1))
def ck(l,v):
 assert v,l
 checks.append(l)
ck('base0',A(0)==1);ck('base1',A(1)==1+X)
for n in range(11):
 p=A(n);q=A(n+1);r=A(n+2)
 ck('three term '+str(n),s.expand((n+2)*r-(2*n+3+X)*q+(n+1)*p)==0)
 W=s.expand(p*s.diff(q,X)-q*s.diff(p,X))
 Wnext=s.expand(q*s.diff(r,X)-r*s.diff(q,X))
 ck('Wronskian recurrence '+str(n),s.expand((n+2)*Wnext-q*q-(n+1)*W)==0)
 ck('CD average '+str(n),s.expand((n+1)*W-sum(A(j)**2 for j in range(n+1)))==0)
 z=s.Rational(rng.randint(-4,5),3)+s.I/2
 pn=(-1)**n*s.factorial(n)*s.laguerre(n,X)
 qn=(-1)**(n+1)*s.factorial(n+1)*s.laguerre(n+1,X)
 monicW=(pn*s.diff(qn,X)-qn*s.diff(pn,X)).subs(X,-z)
 ck('monic W normalization '+str(n),s.simplify(monicW-s.factorial(n)*s.factorial(n+1)*W.subs(X,z))==0)
 if n>0:ck('wrong CD divisor rejected '+str(n),s.expand(W-sum(A(j)**2 for j in range(n+1)))!=0)
r=dict(seed=SEED,checks=len(checks),status='PASS',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),controls=checks,scope='Exact polynomial coefficients, n0/1 calibration, formal derivative recurrences and complex normalization; not proof')
Path('verification/sheaf_wishart/quota-20261022-0949/positive-laguerre-recurrence-control.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8')
print('PASS',len(checks),'exact controls')
