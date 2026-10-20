"""Scalar CN1 shifted disk maximum-density controls; no proof by sampling."""
import json,hashlib
from pathlib import Path
import numpy as np
from scipy.stats import ncx2
from scipy.integrate import quad
from scipy.special import gamma,digamma,exp1
checks=[]
def check(n,b,**d):checks.append(dict(name=n,passed=bool(b),**d))
for a in [0.,.2,1.,5.,10.]:
 for x in [0.,1e-8,.001,.1,1.,10.]:
  v=float(ncx2.cdf(2*x,2,2*a*a));check(f'CDF-{a}-{x}',v<=min(1,x)+1e-13,probability=v,bound=min(1,x))
 for p in [.25,.5,.9]:
  density=lambda y:2*ncx2.pdf(2*y,2,2*a*a)
  v=quad(lambda y:y**(-p)*density(y),0,1,epsabs=1e-9)[0]+quad(lambda y:y**(-p)*density(y),1,np.inf,epsabs=1e-9)[0]
  check(f'inverse-control-{a}-{p}',v<=1/(1-p)+1e-7,integral=v,bound=1/(1-p),not_formalized=True)
  if a==0:check(f'known-Gamma-{p}',abs(v-gamma(1-p))<1e-7,integral=v,reference=float(gamma(1-p)))
 v=quad(lambda y:-np.log(y)*2*ncx2.pdf(2*y,2,2*a*a),0,1,epsabs=1e-9)[0]
 check(f'negative-log-{a}',v<=1+1e-8,integral=v,bound=1,not_formalized=True)
 if a==0:check('known-negative-log',abs(v-(-digamma(1)+exp1(1)))<1e-8)
for x in [1e-8,.01,1.,10.]:check('zero-mean-CDF-'+str(x),abs(ncx2.cdf(2*x,2,0)+np.expm1(-x))<1e-13)
report=dict(source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seed=None,
 model='CN1+mu, Y=norm^2; 2Y is noncentral chi-square(df2,nc2normmu^2)',
 scope='CDF controls precede proof. Inverse/negative-log uniform bounds remain controls until separately proved.',
 checks=checks,status='PASS' if all(c['passed'] for c in checks) else 'FAIL')
root=Path(__file__).resolve().parents[1];(root/'verification/central_mixed_moments/scalar-uniform-smallball-control.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(report['status'],len(checks));raise SystemExit(0 if report['status']=='PASS' else 1)
