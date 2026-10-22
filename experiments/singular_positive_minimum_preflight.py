"""Explore an OPEN smallest-positive-eigenvalue inverse threshold; only known controls assert."""
from pathlib import Path
import sys,json,hashlib,time
import numpy as np
from scipy.special import gammainc
seed=2026102211;rng=np.random.default_rng(seed);N=400000;start=time.monotonic();checks=[];cases=[]
for m,b,c,shift in [(2,1,0,0.),(1,2,0,0.),(2,1,1,0.),(2,2,1,0.),(3,1,1,0.),(3,2,1,0.),(2,1,1,.4),(2,1,2,.4),(3,0,1,0.)]:
 R=min(m,b+c);assert R>0
 X=np.zeros((N,m,b+c),complex)
 if b:X[:,:,:b]=(rng.normal(size=(N,m,b))+1j*rng.normal(size=(N,m,b)))/np.sqrt(2)+shift*(1+.3j)
 for j in range(c):X[:,m-c+j,b+j]=1.5+.2*j
 val=np.linalg.svd(X,compute_uv=False)[:,-1]**2
 thresholds=[.01,.02,.04,.08];cdf=[float(np.mean(val<=x)) for x in thresholds]
 slopes=[float(np.log(v/u)/np.log(y/x)) if min(u,v)>0 else None for x,y,u,v in zip(thresholds,thresholds[1:],cdf,cdf[1:])]
 candidate=None if b==0 or c==m else abs(m-b-c)+1
 case=dict(m=m,b=b,c=c,shift=shift,generic_rank=R,candidate_exponent_NOT_PROVED=candidate,thresholds=thresholds,sampled_cdf=cdf,local_log_slopes_HEURISTIC=slopes,min_observed=float(val.min()),interpretation='Exploratory sampled slopes only; no general inverse-moment or tail theorem')
 if c==0 and shift==0 and min(m,b)==1:
  k=max(m,b)
  for x,v in zip(thresholds,cdf):
   ref=float(gammainc(k,x));sd=np.sqrt(ref*(1-ref)/N)
   assert abs(v-ref)<7*sd+7/N;checks.append(f'known-Gamma{k}-CDF-{x}')
 if b==0 or c==m:
  assert val.min()>=2.25-1e-10;checks.append(f'known-noiseless-floor-{m}-{b}-{c}')
 cases.append(case)
T=np.array([[1.,0.],[0.,2.]],complex)
assert np.linalg.matrix_rank(T)==2 and np.linalg.matrix_rank(T[:,:1])==1;checks.append('noisy-source-rank-is-not-total-rank-control')
Q=np.array([[1.,1j]],complex);e=np.linalg.eigvalsh(Q.conj().T@Q)
assert abs(e[0])<1e-12 and e[1]>0;checks.append('structural-zero-column-minimum-warning-control')
out=dict(status='PASS known controls; CANDIDATE OPEN, NOT general proof',seed=seed,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),samples_per_case=N,checks=len(checks),known_controls=checks,cases=cases,seconds=time.monotonic()-start)
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(dict(status=out['status'],known_checks=len(checks),cases=len(cases),seconds=out['seconds'])))
