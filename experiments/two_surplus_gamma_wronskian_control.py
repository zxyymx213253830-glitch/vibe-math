"""Exact factorial/Gamma/actual mixed-minor polynomial calibration, not proof."""
from pathlib import Path
import sympy as s
import random,json,hashlib,math
SEED=2026102503;rng=random.Random(SEED);X=s.Symbol('X');checks=[]
def ck(label,v):
 assert v,label
 checks.append(label)
def power(d,n,p):return s.prod(s.Rational(math.factorial(d+j+p),math.factorial(d+j)) for j in range(n))
def actual_poly(n,x):
 total=0
 for a in range(n+1):
  for c in range(a+1):
   for b in range(n-a+1):
    moment=power(n-c,c,2)*power(n-a,a-c,1)*power(n-c-b,b,1)
    total+=math.comb(n,a)*math.comb(a,c)*math.comb(n-a,b)*x**(2*n-a-c-b)*moment
 return s.cancel(total/(math.factorial(n)*math.factorial(n+1)))
for n in range(7):
 p=(-1)**n*s.factorial(n)*s.laguerre(n,X)
 q=(-1)**(n+1)*s.factorial(n+1)*s.laguerre(n+1,X)
 W=s.expand(p*s.diff(q,X)-q*s.diff(p,X))
 H=s.prod(s.factorial(j)**2 for j in range(n));C=s.factorial(n)*s.factorial(n+1)
 ck('normalizer n'+str(n),W.subs(X,0)==C)
 for x in [s.Integer(0),s.Rational(rng.randint(1,5),3),s.Integer(2)]:
  tail=lambda k:s.factorial(k)*sum(x**j/s.factorial(j) for j in range(k+1))
  D=s.Matrix(n,n,lambda i,j:tail(i+j+2)).det()
  ck('Gamma Wronskian '+str((n,x)),s.simplify(D-H*W.subs(X,-x))==0)
  ck('mixed minor actual polynomial '+str((n,x)),s.simplify(actual_poly(n,x)-W.subs(X,-x)/C)==0)
  ck('positive normalized polynomial '+str((n,x)),actual_poly(n,x)>0)
  if n==1:ck('scalar Gamma3 '+str(x),s.expand(D-(x*x+2*x+2))==0)
  if n>=2 and x>0:ck('missing normalizer rejected '+str((n,x)),s.simplify(actual_poly(n,x)-W.subs(X,-x))!=0)
out=dict(seed=SEED,checks=len(checks),status='PASS',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),controls=checks,scope='Exact upper-integer-Gamma finite sums, Wronskian, and already-defined actual mixed-minor polynomial; controls not proof of general equality')
Path('verification/sheaf_wishart/quota-20261022-0949/two-surplus-gamma-wronskian-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('PASS',len(checks),'exact controls')
