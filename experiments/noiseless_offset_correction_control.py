"""Deterministic high-precision controls, not a proof of general matrix asymptotics."""
import json,hashlib
from pathlib import Path
import mpmath as mp
mp.mp.dps=90
root=Path(__file__).resolve().parents[1]
checks=[]
def check(name,ok,**data):
    checks.append(dict(name=name,passed=bool(ok),**data))
# Exact rational u, evaluated at high precision; classical scalar inequalities.
values=[mp.mpf(0)]+[mp.mpf(a)/b for a in [1,2,5,100,100000] for b in [1,3,1000,1000000000000]]
for j,u in enumerate(values):
    g=u-mp.log1p(u); h=mp.log1p(u)-u+u*u/2
    tol=mp.mpf('1e-75')*max(1,u**3)
    check('scalar-gap-'+str(j), -tol<=g<=u*u/2+tol and -tol<=h<=u**3/3+tol,
          u=str(u),gap=str(g),second_remainder=str(h))
# Known scalar ROW model: lambda=1+Exp(1), mean shift in noiseless column.
K=mp.e*mp.e1(1); K2=1-K
I1=mp.quad(lambda t:mp.exp(-t)/(1+t),[0,1,mp.inf])
I2=mp.quad(lambda t:mp.exp(-t)/(1+t)**2,[0,1,mp.inf])
check('known-inverse-first',abs(I1-K)<mp.mpf('1e-75'),value=str(I1),closed=str(K))
check('known-inverse-second',abs(I2-K2)<mp.mpf('1e-75'),value=str(I2),closed=str(K2))
for r in [1,10,100,1000]:
    rr=mp.mpf(r)
    Delta=mp.quad(lambda t:mp.exp(-t)*mp.log1p(1/(rr*(1+t))),[0,1,mp.inf])
    gap=K-rr*Delta
    rem=rr*rr*Delta-rr*K+K2/2
    check('expected-correction-'+str(r), 0<=gap<=mp.mpf(1)/(2*rr) and 0<=rem<=mp.mpf(1)/(3*rr),
          r=r,Delta=str(Delta),first_gap=str(gap),second_remainder=str(rem),
          next_coefficient=str(rr*(rr*Delta-K)),target=str(-K2/2))
report=dict(source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seed=None,method='90-digit mpmath exact-rational scalar inputs and independent positive quadratures',
            model='m=p=1,n=2; B=[1,0],M=[0,1], CN1; lambda=1+Exp1; delta=1',
            scope='Controls only; no general proof, no Monte Carlo, no model parameter uniformity claim.',
            passed=all(c['passed'] for c in checks),checks=checks)
report['status']='PASS' if report['passed'] else 'FAIL'
(root/'verification/central_mixed_moments/noiseless-offset-correction-control.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print('PASS' if report['passed'] else 'FAIL',len(checks))
raise SystemExit(0 if report['passed'] else 1)
