"""Pre-source trace/radius -> ordered eigenvalue linear density controls."""
from pathlib import Path
import hashlib,json
import numpy as np
import sympy as s
seed=2026102408;rng=np.random.default_rng(seed);checks=0
J=s.Matrix([[1,1],[1,-1]])
assert J.det()==-2 and abs(J.inv().det())==s.Rational(1,2);checks+=1
for _ in range(80):
 t,r=map(s.Integer,rng.integers(-8,9,size=2));u,v=J*s.Matrix([t,r])
 assert J.inv()*s.Matrix([u,v])==s.Matrix([t,r]);checks+=1
 assert bool(0<r<t)==bool(0<v<u);checks+=1
u,v=s.symbols('u v',real=True);t=(u+v)/2;r=(u-v)/2
assert s.simplify(s.Rational(1,2)*8*r*r*s.exp(-2*t)-s.exp(-u-v)*(u-v)**2)==0;checks+=1
q,g=s.symbols('q g',positive=True)
law=s.exp(-(2*q+g))*g*g
assert s.integrate(law,(q,0,s.oo),(g,0,s.oo))==1;checks+=1
assert s.integrate(2*law,(q,0,s.oo),(g,0,s.oo))==2;checks+=1
out=dict(seed=seed,checks=checks,status='PASS exact controls; not general proof',reference='Signed Jacobian -2; inverse 1/2; cone equivalence; exact transformed density and normalization; omitted-half negative control',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('verification/sheaf_wishart/quota-20261022-0949/two-by-two-spectral-linear-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
