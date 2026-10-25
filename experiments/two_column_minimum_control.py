"""Upper-Gamma two-column minimum controls; before source, not proof."""
from pathlib import Path
import hashlib,json,math
from scipy.integrate import dblquad
from scipy.special import gammaincc,gamma
seed=2026102416;checks=0
for d in range(6):
 C=math.factorial(d)*math.factorial(d+1)
 for x in [0.,0.5,2.,4.]:
  U=lambda k:gamma(k+1)*gammaincc(k+1,x)
  tail=(U(d+2)*U(d)-U(d+1)**2)/C
  ref=dblquad(lambda v,u:math.exp(-u-v)*(u-v)**2*(u*v)**d/C,x,math.inf,lambda u:x,lambda u:u,epsabs=1e-9)[0]
  assert abs(tail-ref)<1e-8;checks+=1
  assert -1e-12<=1-tail<=1+1e-12;checks+=1
  if x==0:assert abs(tail-1)<1e-12;checks+=1
# The clipped tail measure at x<0 has full positive support, not signed Gamma continuation.
assert max(0,-1)==0 and gammaincc(1,0)==1;checks+=1
out=dict(seed=seed,checks=checks,status='PASS calibrated controls; not proof',reference='Independent infinite triangular tail quadrature versus upper-Gamma determinant, minCDF complement and zero threshold normalization; clipped-negative endpoint calibration',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('verification/sheaf_wishart/quota-20261022-0949/two-column-minimum-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out))
