"""Discrete probability controls for variance continuity and inverse-scale rate."""
from pathlib import Path
import hashlib,json,math,random
import numpy as np
seed=2026102240;rng=random.Random(seed);checks=cases=0
def variance(x,w):
 mean=float(w@x)
 return float(w@((x-mean)**2))
for n in [2,5,11]:
 for t in range(24):
  w=np.array([rng.randrange(1,10) for _ in range(n)],dtype=float);w/=w.sum()
  v=np.array([rng.uniform(-5,5) for _ in range(n)])
  e=np.array([rng.uniform(-2,2) for _ in range(n)])
  u=v+e;I=float(w@(e*e));V=variance(v,w)
  left=abs(variance(u,w)-V);right=I+2*math.sqrt(I)*math.sqrt(V)
  assert left<=right+1e-11;checks+=1
  assert math.isclose(variance(u+13,w),variance(u,w),rel_tol=1e-11,abs_tol=1e-11);checks+=1
  A=math.sqrt(I)
  for scale in [1,3,100]:
   us=v+e/scale
   bound=A*A/(scale*scale)+2*A/scale*math.sqrt(V)
   assert abs(variance(us,w)-V)<=bound+1e-11;checks+=1
  cases+=1
# Tight positive proportional centered error, and constant-shift zero variance change.
v=np.array([-1.,1.]);w=np.array([.5,.5])
for eps in [.01,.2,1.,3.]:
 I=eps*eps
 assert math.isclose(abs(variance((1+eps)*v,w)-1),I+2*math.sqrt(I),rel_tol=1e-12);checks+=1
assert variance(v+7,w)==variance(v,w);checks+=1
out=dict(status='PASS finite controls, not general measure/probability proof',seed=seed,
 checks=checks,cases=cases,reference='two-point +/-1 with u=(1+epsilon)v attains the bound; variance shift invariance',
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('verification/sheaf_wishart/quota-20261022-0949/variance-offset-rate-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
