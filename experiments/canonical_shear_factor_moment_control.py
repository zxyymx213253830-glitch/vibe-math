"""Gaussian shear-factor moment calibration (not an all-orders integrability proof)."""
from pathlib import Path
import hashlib,json,sys,math
import numpy as np
from scipy.integrate import quad
SEED=2026102231;rng=np.random.default_rng(SEED);checks=0;cases=0
# Exact radial density for proper CN1 scalar: 2*r*exp(-r*r).
for q in [0,1,2,4,7]:
 for t in [0,0.5,2]:
  cases+=1
  ref=sum(math.comb(q,k)*t**k*math.gamma(1+k/2) for k in range(q+1))
  value=quad(lambda r: (1+t*r)**q*2*r*math.exp(-r*r),0,np.inf,epsabs=1e-9)[0]
  assert abs(value-ref)<=1e-7*max(1,ref);checks+=1
# Nonzero complex means/rectangular/zero factors; finite fixed samples are only sanity controls.
for c,b in [(0,0),(0,3),(3,0),(1,1),(2,3),(3,2)]:
 cases+=1
 Q=(rng.normal(size=(c,c))+1j*rng.normal(size=(c,c)))/math.sqrt(2)
 M=rng.normal(size=(c,b))+1j*rng.normal(size=(c,b))
 Z=(rng.normal(size=(64,c,b))+1j*rng.normal(size=(64,c,b)))/math.sqrt(2)
 for z in Z:
  K=Q@(z+M);v=float(np.linalg.norm(K,2)) if min(K.shape) else 0.
  assert np.isfinite((1+v)**7.25);checks+=1
  if not c or not b:assert v==0;checks+=1
out=dict(seed=SEED,cases=cases,checks=checks,status='PASS',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Closed scalar moment calibration plus finite sample sanity only; not a proof of general integrability',known_controls=['properCN1 radial Gamma moments','zero/empty shear factor1'])
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out))
