"""Pre-source actual2x2 maximum/T2 and ordered-half controls; not proofs."""
from pathlib import Path
import hashlib,json
import numpy as np
import sympy as s
seed=2026102409;rng=np.random.default_rng(seed);checks=0
x=s.symbols('x',positive=True);u,v=s.symbols('u v',real=True)
joint=s.exp(-u-v)*(u-v)**2
inner=s.integrate(joint,(v,0,u))
closed=1-(x*x+2)*s.exp(-x)+s.exp(-2*x)
assert s.simplify(inner-((u*u-2*u+2)*s.exp(-u)-2*s.exp(-2*u)))==0;checks+=1
assert s.simplify(s.integrate(inner,(u,0,x))-closed)==0;checks+=1
m0=1-s.exp(-x);m1=1-(x+1)*s.exp(-x);m2=2-(x*x+2*x+2)*s.exp(-x)
assert s.simplify(s.Matrix([[m2,m1],[m1,m0]]).det()-closed)==0;checks+=1
assert s.simplify(1-s.exp(-2*x)-closed-((x*x+2)*s.exp(-x)-2*s.exp(-2*x)))==0;checks+=1
assert s.limit(closed,x,0,dir='+')==0 and s.limit(closed,x,s.oo)==1;checks+=1
for _ in range(20):
 n=int(rng.integers(1,7));a=list(map(int,rng.integers(-3,5,size=n)));w=list(map(int,rng.integers(0,4,size=n)))
 H=lambda i,j:(a[i]-a[j])**2*(a[i]**2+1)*(a[j]**2+1)
 full=sum(w[i]*w[j]*H(i,j) for i in range(n) for j in range(n))
 ordered=sum(w[i]*w[j]*H(i,j) for i in range(n) for j in range(n) if a[j]<a[i])
 assert 2*ordered==full;checks+=1
 weights=[w[i]*(a[i]**2+1) for i in range(n)]
 determinant=sum(weights)*sum(weights[i]*a[i]**2 for i in range(n))-sum(weights[i]*a[i] for i in range(n))**2
 assert ordered==determinant;checks+=1
a=[0,1,3]
asym=lambda i,j:(a[i]-a[j])**2*(a[i]+1)
assert 2*sum(asym(i,j) for i in range(3) for j in range(3) if a[j]<a[i])!=sum(asym(i,j) for i in range(3) for j in range(3));checks+=1
assert 2*sum(1 for i in range(3) for j in range(3) if a[j]<a[i])!=9;checks+=1 # diagonal atoms matter
out=dict(seed=seed,checks=checks,status='PASS exact controls; not proof',reference='Ordered joint triangular integral, lower-Gamma 2x2 moment determinant, min/max T3 difference; discrete symmetric ordered-half and moment determinant; asymmetric/nonzero-diagonal negative controls',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('verification/sheaf_wishart/quota-20261022-0949/two-by-two-maximum-cdf-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
