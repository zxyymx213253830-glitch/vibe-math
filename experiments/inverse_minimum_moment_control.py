"""Gamma inverse-moment and layercake power controls; numerical evidence not proof."""
import hashlib,json,math
from pathlib import Path
import numpy as np
import sympy as sp
from scipy.special import gammainc
from scipy.integrate import quad

rng=np.random.default_rng(2026101913);t=sp.Symbol('t',positive=True);records=[]
for k in range(1,7):
 for q in range(1,6):
  # Gamma CDF at1/t has leading1/(k!*t^k); multiplying layercake weight gives
  # exponentq-k-1, integrable at infinity exactly when q<k.
  x=sp.Symbol('x',positive=True)
  H=1-sp.exp(-x)*sum(x**j/sp.factorial(j) for j in range(k))
  lead=sp.limit(H/x**k,x,0,dir='+');assert lead==sp.Rational(1,math.factorial(k))
  exponent=q-k-1;assert (exponent < -1)==(q<k)
  records.append(dict(k=k,q=q,tail_weight_exponent=exponent,finite_predicted=q<k))
# Known scalar Gamma controls with FINITE variance for the Monte Carlo mean.
moments=[]
for k in (3,5,7):
 X=rng.gamma(k,1.,200000);Y=1/X
 exact=1/(k-1);variance=1/((k-1)**2*(k-2))
 z=(float(Y.mean())-exact)/np.sqrt(variance/len(Y));assert abs(z)<6
 # Independent layercake integration vs known inverse-Gamma moment.
 val,err=quad(lambda u:gammainc(k,1/u),0,np.inf,epsabs=1e-10)
 assert abs(val-exact)<1e-8
 moments.append(dict(k=k,count=len(X),mean_error_SE=float(z),layercake_integral=val,closed=exact))
# Criticalk=q=1 diverges logarithmically: t*P(1/Exp(1)>=t)->1.
critical=[float(u*(-np.expm1(-1/u))) for u in (1e2,1e4,1e6)]
assert abs(critical[-1]-1)<1e-6
result=dict(seed=2026101913,status='PASS Gamma inverse moments, exact critical-power controls and layercake integration; not proof',
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),power_records=records,finite_controls=moments,critical_tail_ratios=critical)
(Path(__file__).resolve().parents[1]/'verification/central_mixed_moments/inverse-moment-control.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(result['status'])
