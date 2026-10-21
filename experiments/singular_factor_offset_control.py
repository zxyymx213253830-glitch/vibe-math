"""Proper-CN1 singular-factor offset controls with exact known references."""
from pathlib import Path
import sys,json,hashlib
import numpy as np
from scipy.special import digamma
seed=2026102202;N=200000;rng=np.random.default_rng(seed);rows=[]
def check(name,ok,**detail):
 assert bool(ok),name
 rows.append(dict(name=name,**detail))
def mean_control(name,a,ref):
 mean=float(np.mean(a));se=float(np.std(a,ddof=1)/np.sqrt(a.size))
 check(name,abs(mean-ref)<=8*se+1e-10,mean=mean,reference=float(ref),standard_error=se)
for m in [1,2,3]:
 z=(rng.normal(size=(N,m))+1j*rng.normal(size=(N,m)))/np.sqrt(2)
 lam=np.sum(np.abs(z)**2,axis=1)
 S=np.log(lam)
 mean_control(f'rank1-singular-B-log-gamma-m{m}',S,digamma(m))
 mean_control(f'proper-cn1-energy-m{m}',lam,m)
 errs=[]
 for rho in [1e2,1e4,1e6]:
  delta=np.log1p(rho*lam)-np.log(rho)-S
  check(f'rank1-offset-error-nonnegative-m{m}-rho{rho}',np.min(delta)>=-1e-12)
  errs.append(float(np.mean(delta)))
 check(f'rank1-offset-error-decreases-m{m}',errs[0]>=errs[1]>=errs[2]>=0,errors=errs)
c=1.5
z=(rng.normal(size=(N,2))+1j*rng.normal(size=(N,2)))/np.sqrt(2)
X=np.zeros((N,2,2),complex);X[:,:,0]=z;X[:,1,1]=c
G=np.conjugate(X).transpose(0,2,1)@X
ev=np.linalg.eigvalsh(G)
S=np.sum(np.log(ev),axis=1)
reference=2*np.log(c)+digamma(1)
mean_control('rank2-B-singular-M-noiseless-complement-logdet',S,reference)
check('rank2-logdet-direct-identity',np.max(np.abs(S-(2*np.log(c)+np.log(np.abs(z[:,0])**2))))<1e-7)
mean_control('rank2-correlated-trace',np.trace(G,axis1=1,axis2=2).real,2+c*c)
errs=[]
for rho in [1e2,1e4,1e6]:
 delta=np.sum(np.log1p(rho*ev),axis=1)-2*np.log(rho)-S
 check(f'rank2-offset-error-nonnegative-rho{rho}',np.min(delta)>=-1e-10)
 errs.append(float(np.mean(delta)))
check('rank2-offset-error-decreases',errs[0]>=errs[1]>=errs[2]>=0,errors=errs)
check('zero-B-fixed-rank1-offset-reference',np.log(4)==2*np.log(2),rank=1,offset=float(np.log(4)))
check('empty-rank0-offset',sum([])==0,rank=0,offset=0)
out=dict(status='PASS known-reference controls; NOT a proof',seed=seed,samples=N,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),checks=len(rows),details=rows,scope='Fixed properCN1 singular B; rank1 gamma references, rank2 singular B plus fixed noiseless mean complement, zero B and rank0. No parameter-uniform assertion.')
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps({k:out[k] for k in ['status','samples','checks']}))
