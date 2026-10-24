"""Central arbitrary-row two-column determinant-bias controls, before source."""
from pathlib import Path
import hashlib,json,math
import numpy as np
from scipy.integrate import dblquad
seed=2026102414;rng=np.random.default_rng(seed);checks=0;N=200000;rows=[]
for d in range(8):
 den=math.factorial(d)*math.factorial(d+1)
 assert math.factorial(d+2)*math.factorial(d)-math.factorial(d+1)**2==den;checks+=1
 for p in range(4):
  ratio=math.factorial(d+p)*math.factorial(d+p+1)/den
  assert ratio==math.prod(math.prod(range(d+j+1,d+j+p+1)) for j in [0,1]);checks+=1
for m in [3,4,6]:
 z=(rng.normal(size=(N,m,2))+1j*rng.normal(size=(N,m,2)))/np.sqrt(2)
 W=z.conj().transpose(0,2,1)@z;ev=np.linalg.eigvalsh(W);tr=ev.sum(axis=1);det=ev.prod(axis=1)
 assert abs(tr.mean()-2*m)<=7*np.sqrt(2*m/N);checks+=1
 assert abs(det.mean()-m*(m-1))<=7*np.sqrt(2*m*m*(m-1)/N);checks+=1
 d=m-2;den=math.factorial(d)*math.factorial(d+1)
 for a,b in [(0.25,4.),(1.,8.),(2.,12.)]:
  ref=dblquad(lambda v,u:math.exp(-u-v)*(u-v)**2*(u*v)**d/den,a,b,lambda u:a,lambda u:u,epsabs=1e-10)[0]
  est=float(np.mean((ev[:,0]>a)&(ev[:,1]<b)))
  assert abs(est-ref)<=7*np.sqrt(max(ref*(1-ref),1e-8)/N)+1e-7;checks+=1
  rows.append(dict(m=m,a=a,b=b,estimate=est,reference=ref))
# Omitting determinant-bias normalization changes total mass for d=1.
assert math.factorial(1)*math.factorial(2)!=1;checks+=1
out=dict(seed=seed,samples_per_shape=N,checks=checks,status='PASS calibrated controls; not proof',reference='Gamma moment determinant normalization d!(d+1)!, exact determinant-bias ratios, independent actual properCN1 trace/determinant moments and ordered joint rectangle quadrature',joint_checks=rows,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('verification/sheaf_wishart/quota-20261022-0949/two-column-bias-density-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out))
