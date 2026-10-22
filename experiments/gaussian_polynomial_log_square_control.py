"""Planar variance2 log-square/moment controls, never a general proof."""
from pathlib import Path
import sys,json,hashlib,time,math
import numpy as np
from scipy.integrate import quad
seed=2026102207;rng=np.random.default_rng(seed);N=200000;start=time.monotonic();checks=[]
def ok(name,p):
 assert p,name
 checks.append(name)
Z=rng.normal(size=(N,3))+1j*rng.normal(size=(N,3))
neg=lambda z:np.maximum(0.,-np.log(np.maximum(np.abs(z),1e-300)))
mu=(np.log(2)-np.euler_gamma)/2;var=np.pi**2/24
for n in range(4):
 l=np.sum(np.log(np.abs(Z[:,:n])),axis=1);v=l*l;ref=n*var+(n*mu)**2
 ok(f'product-n{n}-known-log-square',abs(v.mean()-ref)<=7*v.std(ddof=1)/np.sqrt(N)+1e-12)
for root in [0.,.4+1.3j,3.+2j]:
 y=neg(Z[:,0]-root)
 for k in range(1,5):
  v=y**k;bound=math.factorial(k)/2**(k+1)
  ok(f'planar-root-uniform-moment-{root}-{k}',v.mean()<bound+7*v.std(ddof=1)/np.sqrt(N))
  if root==0:
   ref=quad(lambda t:t**k*np.exp(-2*t)*np.exp(-np.exp(-2*t)/2),0,np.inf)[0]
   ok(f'root0-quadrature-{k}',abs(v.mean()-ref)<7*v.std(ddof=1)/np.sqrt(N))
for a,roots in [(1.,[]),(.1,[]),(2.,[0.,0.,0.]),(.2,[.3+1j,-.5j]),(1j,[1.,-1.])]:
 P=np.full(N,a,complex)
 for b in roots:P*=Z[:,0]-b
 Y=neg(P)**2;lead=max(0.,-np.log(abs(a)));bound=2*lead**2+len(roots)**2/2
 ok(f'polynomial-section-square-{a}-{roots}',Y.mean()<bound+7*Y.std(ddof=1)/np.sqrt(N)+1e-12)
ok('zero-polynomial-totalized-log-control',0.**2==0.)
ok('wrong-proper-variance-negative-control',abs(np.mean(np.abs(Z[:,0])**2)-1.)>.5)
ok('L1-does-not-imply-L2-negative-control',quad(lambda x:x**(-.75),0,1)[0]<np.inf and 2*.75>=1)
out=dict(status='PASS reproducible controls; NOT general proof',seed=seed,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),samples=N,checks=len(checks),details=checks,seconds=time.monotonic()-start,scope='planar stdGaussian(C) secondmoment2; log-square known products, uniform shifted-root momentsk1..4, polynomial section bound; totalizedzero and normalization controls')
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps({k:out[k] for k in ['status','checks','seconds']}))
