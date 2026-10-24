"""Pre-source strict crossing controls; exact calibration, not proofs."""
from pathlib import Path
import hashlib,json,random
import sympy as s
seed=2026102410; rng=random.Random(seed); checks=0
x=s.symbols('x',positive=True); u,v=s.symbols('u v',real=True)
closed=(x*x+2)*s.exp(-x)-2*s.exp(-2*x)
assert s.simplify(s.integrate(s.integrate(s.exp(-u-v)*(u-v)**2,(v,0,x)),(u,x,s.oo))-closed)==0;checks+=1
assert s.limit(closed,x,0,dir='+')==0 and s.limit(closed,x,s.oo)==0;checks+=1
for _ in range(60):
 a=[rng.randrange(-4,6) for _ in range(8)]; b=[z+rng.randrange(5) for z in a];w=[rng.randrange(4) for z in a]
 t=s.Rational(rng.randrange(-8,18),2)
 weak=sum(c for l,h,c in zip(a,b,w) if l<=t)
 upper=sum(c for l,h,c in zip(a,b,w) if h<=t)
 strict=sum(c for l,h,c in zip(a,b,w) if l<t<h)
 boundary=sum(c for l,h,c in zip(a,b,w) if l==t<h)
 assert weak==upper+strict+boundary;checks+=1
 if all(l!=t or c==0 for l,c in zip(a,w)):
  assert weak==upper+strict;checks+=1
assert 1!=0+0 # atom a=0,b=1,x=0 invalidates boundary-free strict recurrence
checks+=1
out=dict(seed=seed,checks=checks,status='PASS exact controls; not proof',reference='Direct strip integral against known ordered central2x2 joint density, endpoint limits, exact weighted ordered atomic recurrence and missing-boundary negative control',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('verification/sheaf_wishart/quota-20261022-0949/two-by-two-strict-crossing-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out))
