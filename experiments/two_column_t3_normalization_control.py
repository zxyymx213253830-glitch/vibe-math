"""Central two-column T3 normalization controls, before source; not proof."""
from pathlib import Path
import hashlib,json,math
from scipy.integrate import dblquad
from scipy.special import gammainc,gammaincc,gamma
seed=2026102501;checks=0
for d in range(8):
 C=math.factorial(d)*math.factorial(d+1)
 for x in [0.5,2.,4.]:
  up=lambda k:gamma(k+1)*gammaincc(k+1,x)
  lo=lambda k:gamma(k+1)*gammainc(k+1,x)
  P=[[up(d+2),up(d+1)],[up(d+1),up(d)]]
  Q=[[lo(d+2),lo(d+1)],[lo(d+1),lo(d)]]
  raw=P[0][0]*Q[1][1]-P[0][1]*Q[1][0]+Q[0][0]*P[1][1]-Q[0][1]*P[1][0]
  ref=dblquad(lambda v,u:math.exp(-u-v)*(u-v)**2*(u*v)**d/C,x,math.inf,lambda u:0,lambda u:x,epsabs=1e-10)[0]
  assert abs(raw/C-ref)<3e-9;checks+=1
  assert abs(1-(P[0][0]*P[1][1]-P[0][1]**2)/C-(Q[0][0]*Q[1][1]-Q[0][1]**2)/C-ref)<3e-9;checks+=1
  if d==0:
   assert abs(ref-((x*x+2)*math.exp(-x)-2*math.exp(-2*x)))<1e-10;checks+=1
# Known explicit source-transcription witness; normalize by2, do not silently alter original.
raw=16*math.exp(-2)-28*math.exp(-4)
assert raw>1 and 0<raw/2<1;checks+=1
out=dict(seed=seed,checks=checks,status='PASS calibrated controls; not proof',reference='Independent strict crossing strip integral against actual ordered density, unchanged mixed-row candidate/C, exact min/max event decomposition and square2 closed calibration; retained2x3 transcription witness',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('verification/sheaf_wishart/quota-20261022-0949/two-column-t3-normalization-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out))
