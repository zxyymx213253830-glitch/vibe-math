"""Known-reference controls for expected logdet derivative at positive scale."""
from pathlib import Path
import sys,json,hashlib
import numpy as np
from scipy.special import exp1
seed=2026102203;N=200000;rng=np.random.default_rng(seed);l=rng.exponential(size=N);rows=[]
for r in [.1,1.,10.,100.]:
 d=l/(1+r*l);ref=1/r-np.exp(1/r)*exp1(1/r)/(r*r)
 mean=float(d.mean());se=float(d.std(ddof=1)/np.sqrt(N))
 assert abs(mean-ref)<8*se+1e-10
 h=r*1e-4
 fd=(np.log1p((r+h)*l)-np.log1p((r-h)*l))/(2*h)
 assert np.max(np.abs(fd-d))<1e-6
 assert np.all(d>=0) and np.all(d<=l)
 rows.append(dict(rho=r,mean=mean,reference=float(ref),standard_error=se,finite_difference_max_error=float(np.max(np.abs(fd-d)))))
for l0 in [0.,.25,1.,4.]:
 r=2.;h=1e-4;d=l0/(1+r*l0);fd=(np.log1p((r+h)*l0)-np.log1p((r-h)*l0))/(2*h)
 assert abs(fd-d)<1e-8
 rows.append(dict(deterministic_eigenvalue=l0,derivative=d))
out=dict(status='PASS closed-reference derivative controls; NOT a proof',seed=seed,samples=N,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),checks=len(rows),details=rows,scope='Exponential(1) scalar properCN1 and fixed spectrum including zero mode. E lambda/(1+rho lambda) uses exact E1 reference; shared samples in finite differences.')
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps({k:out[k] for k in ['status','checks']}))
