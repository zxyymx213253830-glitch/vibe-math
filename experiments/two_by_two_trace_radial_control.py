"""Pre-source trace/traceless coordinates for the actual central 2x2 G2 gap."""
from pathlib import Path
import hashlib,json,math
import numpy as np
import sympy as sp
from scipy.stats import expon,gamma
seed=2026102405;rng=np.random.default_rng(seed);checks=0
B=sp.Matrix([[sp.Rational(1,2),0,0,sp.Rational(1,2)],[sp.Rational(1,2),0,0,-sp.Rational(1,2)],[0,1,0,0],[0,0,1,0]])
assert abs(B.det())==sp.Rational(1,2) and abs(B.inv().det())==2;checks+=1
for _ in range(100):
 q=[sp.Integer(int(v)) for v in rng.integers(-5,6,size=4)];t,v0,v1,v2=B*sp.Matrix(q)
 r2=v0*v0+v1*v1+v2*v2
 assert sp.expand(q[0]*q[3]-q[1]**2-q[2]**2-(t*t-r2))==0;checks+=1
 assert bool(q[0]>0 and q[1]**2+q[2]**2<q[0]*q[3])==bool(t>0 and t*t>r2);checks+=1
 A=np.array([[float(q[0]),complex(float(q[1]),float(q[2]))],[complex(float(q[1]),-float(q[2])),float(q[3])]])
 assert np.allclose(np.linalg.eigvalsh(A),[float(t)-math.sqrt(float(r2)),float(t)+math.sqrt(float(r2))]);checks+=1
u,v=sp.symbols('u v',positive=True)
joint=sp.exp(-(2*u+v))*v*v
assert sp.integrate(joint,(u,0,sp.oo),(v,0,sp.oo))==1;checks+=1
assert sp.simplify(joint/(2*sp.exp(-2*u)*(v*v*sp.exp(-v)/2)))==1;checks+=1
N=200000
Z=(rng.normal(size=(N,2,2))+1j*rng.normal(size=(N,2,2)))/math.sqrt(2)
W=np.swapaxes(Z.conj(),1,2)@Z
e=np.linalg.eigvalsh(W);U=e[:,0];V=e[:,1]-e[:,0]
for p in [.05,.25,.5,.75,.95]:
 for values,threshold in [(U,expon.ppf(p,scale=.5)),(V,gamma.ppf(p,3))]:
  assert abs(float(np.mean(values<=threshold))-p)<6*math.sqrt(p*(1-p)/N);checks+=1
for p in [.25,.5,.75]:
 a=U<=expon.ppf(p,scale=.5);b=V<=gamma.ppf(p,3)
 assert abs(float(np.mean(a&b))-p*p)<6*math.sqrt(p*p*(1-p*p)/N);checks+=1
for x in [.2,1.,2.,4.,8.]:
 closed=1-(x*x+2)*math.exp(-x)+math.exp(-2*x)
 assert abs(float(np.mean(e[:,1]<=x))-closed)<6*math.sqrt(closed*(1-closed)/N)+1e-5;checks+=1
assert sp.integrate(joint/2,(u,0,sp.oo),(v,0,sp.oo))==sp.Rational(1,2);checks+=1
out=dict(seed=seed,checks=checks,status='PASS calibrated finite controls; not joint-law proof',
 reference='Exact 4D trace determinant/Jacobian; positive-cone algebra; eigenpair formula; Exp(2) x Gamma(3,1); closed maximum CDF; omitted-Jacobian control',
 scope='200000 actual properCN1 central 2x2 matrices; ordered joint spectral density remains unproved',
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('verification/sheaf_wishart/quota-20261022-0949/two-by-two-trace-radial-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
