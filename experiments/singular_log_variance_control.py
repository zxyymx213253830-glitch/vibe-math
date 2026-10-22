"""Finite log variance and high-scale L2 controls for fixed singular models."""
from pathlib import Path
import sys,json,hashlib,time
import numpy as np
from scipy.special import digamma,polygamma
from scipy.integrate import quad
seed=2026102209;rng=np.random.default_rng(seed);N=200000;start=time.monotonic();checks=[]
def checkmean(name,v,ref):
 assert abs(v.mean()-ref)<7*v.std(ddof=1)/np.sqrt(N)+1e-12,name
 checks.append(name)
for m in [1,2,3]:
 Z=(rng.normal(size=(N,m))+1j*rng.normal(size=(N,m)))/np.sqrt(2)
 lam=np.sum(np.abs(Z)**2,axis=1);S=np.log(lam);mu=digamma(m);V=polygamma(1,m)
 checkmean(f'Gamma{m}-log-square',S*S,V+mu**2)
 checkmean(f'Gamma{m}-centered-square',(S-mu)**2,V)
 errors=[]
 for r in [1.,10.,100.,1e4]:
  E=np.log1p(r*lam)-np.log(r)-S
  errors.append(np.mean(E*E))
  assert np.all(E>-1e-10);checks.append(f'Gamma{m}-offset-error-positive-{r}')
  if m==1:
   ref=quad(lambda x:np.exp(-x)*np.log1p(1/(r*x))**2,0,np.inf,epsabs=1e-8)[0]
   checkmean(f'Exp1-offset-square-quadrature-{r}',E*E,ref)
 assert all(a>b for a,b in zip(errors,errors[1:]));checks.append(f'Gamma{m}-L2-decreasing-control')
 assert errors[-1]<.02;checks.append(f'Gamma{m}-L2-small-control')
c=1.5;Z=(rng.normal(size=(N,2))+1j*rng.normal(size=(N,2)))/np.sqrt(2)
X=np.zeros((N,2,2),complex);X[:,:,0]=Z;X[:,1,1]=c
ev=np.linalg.eigvalsh(np.swapaxes(X.conj(),1,2)@X);S=np.sum(np.log(ev),axis=1)
mu=2*np.log(c)-np.euler_gamma;V=np.pi**2/6
checkmean('singularB-fixedMean-rank2-centered-square',(S-mu)**2,V)
errors=[]
for r in [1.,10.,100.,1e4]:
 E=np.sum(np.log1p(r*ev),axis=1)-2*np.log(r)-S;errors.append(np.mean(E*E))
assert all(a>b for a,b in zip(errors,errors[1:]));checks.append('rank2-L2-decreasing-control')
assert errors[-1]<.02;checks.append('rank2-L2-small-control')
for ev in [np.array([]),np.array([0.,0.]),np.array([0.,4.])]:
 S=np.sum(np.log(ev[ev>0]));R=np.count_nonzero(ev>0)
 E=np.sum(np.log1p(1e4*ev))-R*np.log(1e4)-S
 assert E*E<1e-6;checks.append(f'empty-zero-deterministic-offset-{ev.tolist()}')
assert np.log(.25)<0;checks.append('positive-spectrum-log-is-not-positive-part-negative-control')
out=dict(status='PASS reproducible controls; NOT general proof',seed=seed,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),samples=N,checks=len(checks),details=checks,seconds=time.monotonic()-start,scope='fixed rank1 Gamma, singular-factor rank2 and zero/deterministic models; known log moments and independent Exp1 L2-error quadrature. L2 asymptotic is a control until separately formalized.')
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps({k:out[k] for k in ['status','checks','seconds']}))
