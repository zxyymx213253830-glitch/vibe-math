"""Fixed-seed mixed noisy/noiseless block controls; no general probability proof."""
import json,hashlib
from pathlib import Path
import numpy as np
from scipy.special import digamma,exp1
from scipy.integrate import quad
root=Path(__file__).resolve().parents[1];seed=202610201013;rng=np.random.default_rng(seed);N=200000
checks=[]
def check(name,ok,**data):checks.append(dict(name=name,passed=bool(ok),**data))
K=float(np.e*exp1(1))
for a,r,s in [(1,1,1),(2,2,1),(1,2,1)]:
 A=(rng.normal(size=(N,a,r))+1j*rng.normal(size=(N,a,r)))/np.sqrt(2)
 D=(rng.normal(size=(N,s,r))+1j*rng.normal(size=(N,s,r)))/np.sqrt(2)
 X=np.zeros((N,a+s,r+s),complex);X[:,:a,:r]=A;X[:,a:,:r]=D;X[:,a:,r:]=np.eye(s)
 W=X@X.conj().transpose(0,2,1);S=A@A.conj().transpose(0,2,1)
 sign,logW=np.linalg.slogdet(W);_,logA=np.linalg.slogdet(S)
 base=float(sum(digamma(r-j) for j in range(a)));ref=base+(K if r>a else 0)
 se=float(logW.std(ddof=1)/np.sqrt(N));err=abs(float(logW.mean())-ref)
 check(f'closed-logdet-{a}-{r}-{s}',err<8*se+1e-3,estimate=float(logW.mean()),reference=ref,se=se)
 check(f'CN1-energy-{a}-{r}',abs(float(np.mean(abs(A)**2))-1)<0.01)
 # Same-sample Schur complement, separate from eigen/logdet computation.
 Q=A[:3000].conj().transpose(0,2,1)@np.linalg.solve(S[:3000],A[:3000])
 P=np.eye(r)-Q
 T=np.eye(s)+D[:3000]@P@D[:3000].conj().transpose(0,2,1)
 _,logT=np.linalg.slogdet(T)
 check(f'Schur-{a}-{r}-{s}',np.max(abs(logW[:3000]-logA[:3000]-logT))<2e-8,
       max_error=float(np.max(abs(logW[:3000]-logA[:3000]-logT))))
 if r==a:check(f'square-A-cancels-D-{a}',np.quantile(abs(logW-logA),.999)<1e-8,
             max_error=float(np.max(abs(logW-logA))))
 for rho in [10.,1000.]:
  _,C=np.linalg.slogdet(np.eye(a+s)+rho*W)
  rem=C-(a+s)*np.log(rho)-logW
  check(f'offset-positive-{a}-{r}-{rho}',np.min(rem)>-1e-8,mean_remainder=float(rem.mean()))
# Zero-mode scalar mixture: atom at0 and independent Exp1 positive part with probability1/2.
# E C=0.5 exp(1/rho) E1(1/rho), expected positive-log=-gamma/2.
gamma=-float(digamma(1))
for rho in [1.,10.,1000.]:
 v=float(.5*np.exp(1/rho)*exp1(1/rho));q=quad(lambda t:.5*np.exp(-t)*np.log1p(rho*t),0,np.inf)[0]
 check('zero-mode-known-'+str(rho),abs(v-q)<1e-9,value=v,quadrature=q,
       offset=v-.5*np.log(rho),limit=-gamma/2)
# AE-positive bounded L1 does not imply log L1: on Uniform(0,1), f=exp(-1/t).
for eps in [.1,.01,.001]:
 val=quad(lambda t:1/t,eps,1)[0]
 check('log-nonintegrability-warning-'+str(eps),abs(val+np.log(eps))<1e-10,
       truncated_negative_log_integral=val,exact=-float(np.log(eps)))
report=dict(source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seed=seed,samples=N,
 scope='Fixed block controls and closed reference checks only. No proof of generic offset or inverse moments.',checks=checks,
 status='PASS' if all(c['passed'] for c in checks) else 'FAIL')
(root/'verification/central_mixed_moments/mixed-noiseless-offset-preflight.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(report['status'],len(checks));raise SystemExit(0 if report['status']=='PASS' else 1)
