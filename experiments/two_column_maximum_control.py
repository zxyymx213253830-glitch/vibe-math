"""All-row central two-column maximum Gamma determinant calibration, not proof."""
from pathlib import Path
import hashlib,json,math
from scipy.special import gammainc,gammaincc,gamma
from scipy.integrate import dblquad
seed=2026102415;checks=0
for d in range(8):
 den=math.factorial(d)*math.factorial(d+1)
 for x in [0.,0.5,1.,2.,4.]:
  lo=lambda k:gamma(k+1)*gammainc(k+1,x)
  det=lo(d+2)*lo(d)-lo(d+1)**2
  ref=dblquad(lambda v,u:math.exp(-u-v)*(u-v)**2*(u*v)**d/den,0,x,lambda u:0,lambda u:u,epsabs=1e-11)[0]
  assert abs(det/den-ref)<1e-9;checks+=1
  up=lambda k:gamma(k+1)*gammaincc(k+1,x)
  tail=(up(d+2)*up(d)-up(d+1)**2)/den
  assert -1e-12<=det/den<=1+1e-12 and -1e-12<=tail<=1+1e-12;checks+=1
  # original Xi/Psi use reversed moment order, determinant unchanged.
  assert abs((lo(d)*lo(d+2)-lo(d+1)**2)-det)<1e-12;checks+=1
assert math.factorial(2)*math.factorial(3)!=1;checks+=1
out=dict(seed=seed,checks=checks,status='PASS calibrated controls; not proof',reference='Independent triangular joint-density quadrature versus lower-Gamma moment determinant, upper-Gamma tail range, row/column reversal, denominator negative calibration',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('verification/sheaf_wishart/quota-20261022-0949/two-column-maximum-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out))
