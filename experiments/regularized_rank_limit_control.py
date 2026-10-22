"""Bounded regularized spectral counts: controls, not a general proof."""
from pathlib import Path
import sys,json,hashlib,time
import numpy as np
from scipy.special import exp1
seed=2026102206;rng=np.random.default_rng(seed);start=time.monotonic();checks=[];N=200000
def ok(name,p):
 assert p,name
 checks.append(name)
z=(rng.normal(size=N)+1j*rng.normal(size=N))/np.sqrt(2);u=np.abs(z)**2
for r in [.2,1.,4.]:
 J=np.exp(1/r)*exp1(1/r)/r
 a=r*u/(1+r*u)
 for k,ref in [(1,1-J),(2,1-2*J+(1-J)/r)]:
  v=a**k;ok(f'Exp1-normalized-{k}-{r}',abs(v.mean()-ref)<7*v.std(ddof=1)/np.sqrt(N))
for ev in [np.array([]),np.array([0.,0.]),np.array([0.,.25,2.]),np.array([1.,3.])]:
 R=np.count_nonzero(ev>0)
 for k in [1,2,3,7]:
  vals=[np.sum((r*ev/(1+r*ev))**k) for r in [0.,.1,1.,10.,1e8]]
  ok(f'bounds-monotone-{ev.tolist()}-{k}',all(-1e-12<=v<=R+1e-12 for v in vals) and all(a<=b for a,b in zip(vals,vals[1:])))
  ok(f'fixed-spectrum-limit-{ev.tolist()}-{k}',abs(vals[-1]-R)<1e-6)
for k in [1,2,3]:
 v=[np.mean((r*u/(1+r*u))**k) for r in [1.,10.,100.,1e4]]
 ok(f'CN1-positive-mode-limit-{k}',all(a<b for a,b in zip(v,v[1:])) and v[-1]>.995)
ok('k0-zero-mode-negative-control',0.0**0!=0.0)
ok('unscaled-derivative-is-not-rank-negative-control',np.mean(u/(1+1e5*u))<1e-4)
out=dict(status='PASS reproducible controls; NOT general proof',seed=seed,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),samples=N,checks=len(checks),details=checks,seconds=time.monotonic()-start,scope='positive integer powers only; finite spectra incl empty/zeros; properCN1 Exp1 closed forms and rank1 high-scale controls')
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps({k:out[k] for k in ['status','checks','seconds']}))
