"""Fixed seed finite atomic/exponential calibration. Controls, never uniqueness proof."""
import hashlib,json,math
from pathlib import Path
import numpy as np
SEED=2026102508
rng=np.random.default_rng(SEED);checks=[]
def ck(name,p):
 assert p,name
 checks.append(name)
for d in range(7):
 X=rng.integers(0,8,size=(9,d))/3
 w=rng.integers(0,6,size=9)/7
 f=X.sum(axis=1);tilt=w*np.exp(-f)
 ck('positive cone norm domination '+str(d),np.all((np.max(X,axis=1) if d else np.zeros(9))<=f))
 ck('positive tilt finite '+str(d),np.all(tilt<=w))
 ck('untilt recovery '+str(d),np.allclose(tilt*np.exp(f),w,rtol=1e-13,atol=1e-13))
 for k in range(4):
  L=rng.normal(size=d);dual=np.abs(L).sum();t=.7/(dual+1)*(-1 if k%2 else 1)
  v=X@L;lhs=np.dot(tilt,np.exp(t*v));rhs=np.dot(w,np.exp(-f+t*v))
  ck('tilted MGF identity '+str((d,k)),abs(lhs-rhs)<1e-12)
  ck('local domination '+str((d,k)),np.all(-f+t*v<=1e-12))
# Matrix PSD trace dominates Frobenius norm; includes zero/rank deficient support.
for n in range(5):
 for rank in range(n+1):
  B=rng.normal(size=(rank,n))+1j*rng.normal(size=(rank,n));W=B.conj().T@B
  tr=np.trace(W).real
  ck('PSD trace domination '+str((n,rank)),np.linalg.norm(W)<=tr+1e-12)
  if n:
   H=rng.normal(size=(n,n))+1j*rng.normal(size=(n,n));H=(H+H.conj().T)/2
   s=.6/(np.linalg.norm(H)+1);T=np.eye(n)-s*H
   ck('local PSD test '+str((n,rank)),np.min(np.linalg.eigvalsh(T))>0)
   ck('matrix tilt identity '+str((n,rank)),abs(math.exp(-tr)*math.exp(s*np.trace(H@W).real)-math.exp(-np.trace(T@W).real))<1e-11)
# Trace-only testing cannot identify a matrix law, even for PSD support.
W=np.diag([1.,0.]);V=np.diag([0.,1.])
ck('trace-only negative equal tests',all(abs(math.exp(-t*np.trace(W))-math.exp(-t*np.trace(V)))<1e-14 for t in [0,.1,1,3]))
ck('trace-only negative distinguishing PSD direction',abs(math.exp(-np.trace(W@W))-math.exp(-np.trace(W@V)))>.5)
# First two scalar moments do not determine a nonnegative law.
x=np.array([0.,1.,2.,3.]);p=np.array([1,3,3,1])/8;q=np.array([0,6,0,2])/8
ck('two moments negative calibration',all(abs(np.dot(p,x**k)-np.dot(q,x**k))<1e-14 for k in range(3)))
ck('two moments negative distinguished transform',abs(np.dot(p,np.exp(-x))-np.dot(q,np.exp(-x)))>.02)
# Zero-dimensional finite measures are determined by mass, not dimension assumptions.
ck('zero dimension mass test',math.exp(0)*2==2 and math.exp(0)*3==3)
r=dict(seed=SEED,status='PASS',checks=len(checks),controls=checks,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Finite atomic tilt identity/domination and PSD trace norm controls; inadequate trace-only and first-two-moment negatives. No uniqueness proof.')
Path('verification/sheaf_wishart/quota-20261022-0949/tilted-laplace-uniqueness-control.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8')
print('PASS',len(checks),'controls')
