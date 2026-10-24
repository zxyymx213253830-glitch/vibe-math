"""Pre-source controls for actual arbitrary even-dimensional Gaussian law."""
from pathlib import Path
import hashlib,json,math
import numpy as np
from scipy.special import gammainc
from scipy.stats import ncx2,poisson
seed=2026102402;rng=np.random.default_rng(seed);checks=0
for q in range(9):
 for a in [0.,.3,1.7]:
  for x in [.01,.3,1.,4.,12.]:
   ref=ncx2.cdf(2*x,2*(q+1),a*a)
   # Independently summed central Gamma mixture, including central boundary.
   mixture=sum(poisson.pmf(n,a*a/2)*gammainc(q+n+1,x) for n in range(80))
   assert abs(mixture-ref)<3e-13
   checks+=1
for q in [0,1,4,8]:
 for a in [0.,1.7]:
  direction=rng.normal(size=2*(q+1));direction/=np.linalg.norm(direction)
  mean=a*direction
  energy=np.sum((rng.normal(size=(200000,len(mean)))+mean)**2,axis=1)/2
  for p in [.05,.25,.5,.75,.95]:
   threshold=ncx2.ppf(p,2*(q+1),a*a)/2
   observed=float(np.mean(energy<=threshold))
   assert abs(observed-p)<6*math.sqrt(p*(1-p)/len(energy))+2e-5
   checks+=1
assert abs(ncx2.cdf(4,4,2)-ncx2.cdf(4,4,1))>.05 # encoded squared norm is twice complex energy
checks+=1
out=dict(seed=seed,checks=checks,status='PASS calibrated finite controls; not a law proof',
 reference='Noncentral chi-square CDF versus explicit Poisson/Gamma mixture; central Gamma; fixed-direction shifted Gaussian samples; factor-two negative control',
 scope='Arbitrary positive complex row count target, real dimension 2*(q+1), source/law bridge still required',
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('verification/sheaf_wishart/quota-20261022-0949/general-one-column-law-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
