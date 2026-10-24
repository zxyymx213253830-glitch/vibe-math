"""Pre-source trace-times-R3 volume reduction, calibrated controls only."""
from pathlib import Path
import hashlib,json,math
import numpy as np
from scipy.integrate import quad
seed=2026102407;rng=np.random.default_rng(seed);checks=0
for _ in range(40):
 p=rng.integers(-9,10,size=4)
 radius=math.sqrt(sum(int(x)**2 for x in p[1:]))
 assert math.isclose(radius,np.linalg.norm(p[1:]))
 assert np.array_equal(np.r_[p[0],p[1:]],p)
 checks+=2
for a in [.5,1.,2.,3.]:
 for b in [.25,.5,1.,2.]:
  radial=4*math.pi*math.sqrt(math.pi/a)*quad(lambda r:r*r*math.exp(-b*r*r),0,math.inf)[0]
  cartesian=math.sqrt(math.pi/a)*(math.pi/b)**1.5
  assert math.isclose(radial,cartesian,rel_tol=3e-10)
  checks+=1
assert math.sqrt(3)>1 # Pi sup norm would incorrectly give 1 for this radius.
checks+=1
out=dict(seed=seed,checks=checks,status='PASS calibrated controls; not general proof',reference='Exact coordinate split/recovery; Euclidean norm; product of four Gaussian integrals versus R3 radial reduction; sup-norm negative control',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('verification/sheaf_wishart/quota-20261022-0949/four-dimensional-radial-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
