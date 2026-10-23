"""Critical scalar CN1/Exp1 controls; finite values are not divergence proof."""
from pathlib import Path
import hashlib,json,math
import mpmath as mp
from scipy.integrate import quad
mp.mp.dps=60;seed=2026102244;checks=0;records=[]
for rho in [1.,10.,1000.,1e5]:
 exact=mp.mpf(rho)*(mp.exp(1/mp.mpf(rho))*mp.e1(1/mp.mpf(rho))-mp.log(rho)+mp.euler)
 numeric=rho*(quad(lambda x:math.log1p(1/(rho*x))*math.exp(-x),0,1,epsabs=1e-12)[0]+quad(lambda x:math.log1p(1/(rho*x))*math.exp(-x),1,math.inf,epsabs=1e-13)[0])
 assert math.isclose(numeric,float(exact),rel_tol=1e-7,abs_tol=1e-8);checks+=1
 records.append(dict(rho=rho,scaled_offset=float(exact),minus_logrho=float(exact-mp.log(rho))))
for rho in [mp.mpf(10)**j for j in [2,4,8,12]]:
 value=rho*(mp.exp(1/rho)*mp.e1(1/rho)-mp.log(rho)+mp.euler)
 assert value>mp.log(rho);checks+=1
ifinal=mp.mpf(10)**12
last=ifinal*(mp.exp(1/ifinal)*mp.e1(1/ifinal)-mp.log(ifinal)+mp.euler)
assert abs(last-mp.log(ifinal)-(1-mp.euler))<mp.mpf('1e-8');checks+=1
# A deterministic positive mode has finite first coefficient; not every model diverges.
assert abs(mp.mpf(10)**8*mp.log1p(mp.mpf(10)**-8)-1)<mp.mpf('1e-7');checks+=1
out=dict(status='PASS calibrated critical finite controls; not a Fatou/divergence proof',seed=seed,
 checks=checks,records=records,
 reference='Exp1: E log(1+rho X)=exp(1/rho) E1(1/rho); E log X=-EulerGamma',
 counter_control='deterministic lambda=1 scaled offset tends to1',
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('verification/sheaf_wishart/quota-20261022-0949/critical-first-coefficient-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
