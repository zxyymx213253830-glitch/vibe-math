"""Pre-source R3 radial reduction controls, not a measure-theoretic proof."""
from pathlib import Path
import hashlib,json,math
import numpy as np
from scipy.integrate import quad
seed=2026102406
rng=np.random.default_rng(seed)
checks=0
for k in range(6):
 for a in [0.5,1.,2.,float(rng.uniform(.6,2.5))]:
  integral=4*math.pi*quad(lambda r:r**(k+2)*math.exp(-a*r),0,math.inf,epsabs=1e-9)[0]
  closed=4*math.pi*math.factorial(k+2)/a**(k+3)
  assert math.isclose(integral,closed,rel_tol=2e-10)
  checks+=1
for a in [.25,.5,1.,2.]:
 radial=4*math.pi*quad(lambda r:r*r*math.exp(-a*r*r),0,math.inf)[0]
 cartesian=(math.pi/a)**1.5
 assert math.isclose(radial,cartesian,rel_tol=2e-10)
 checks+=1
for R in [.1,.5,1.,3.]:
 radial=4*math.pi*quad(lambda r:r*r,0,R)[0]
 assert math.isclose(radial,4*math.pi*R**3/3,rel_tol=1e-12)
 assert not math.isclose(radial/2,4*math.pi*R**3/3,rel_tol=1e-12)
 checks+=2
out=dict(seed=seed,checks=checks,status='PASS calibrated controls; not a proof',reference='Gamma factorial integrals, Cartesian Gaussian integral cubed, Euclidean ball volume; factor-two negative controls',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('verification/sheaf_wishart/quota-20261022-0949/three-dimensional-radial-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
