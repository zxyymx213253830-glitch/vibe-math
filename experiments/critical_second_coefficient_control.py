"""Finite Gamma2/positive-spectrum controls, never a divergence proof."""
from pathlib import Path
import hashlib, json, random
import mpmath as mp
mp.mp.dps=70
seed=2026102245; rng=random.Random(seed); checks=0; records=[]
for rho0 in [1,10,1000,100000]:
    t=mp.mpf(rho0); a=1/t
    # Gamma(2,1): ElogX=1-EulerGamma, E(1/X)=1.
    offset=(1-a)*mp.exp(a)*mp.e1(a)-mp.log(t)+mp.euler
    exact=t*(1-t*offset)
    numeric=mp.quad(lambda x:t*(1/x-t*mp.log1p(1/(t*x)))*x*mp.exp(-x),[0,1,mp.inf])
    assert mp.almosteq(exact,numeric,rel_eps=mp.mpf('1e-45')); checks+=1
    assert exact>=0; checks+=1
    records.append(dict(t=float(t),second_scaled_gap=float(exact)))
for k in [6,10,16]:
    t=mp.mpf(10)**k; a=1/t
    value=t*(1-t*((1-a)*mp.exp(a)*mp.e1(a)-mp.log(t)+mp.euler))
    assert abs(value-mp.log(t)/2-mp.mpf(1)/4+mp.euler/2)<mp.mpf(10)**(-k+3); checks+=1
for _ in range(36):
    xs=[mp.mpf(rng.randint(1,10))/rng.randint(1,6) for _ in range(rng.randint(1,5))]+[mp.mpf(0)]
    t=mp.mpf(10)**10
    q=sum(1/x**2 for x in xs if x>0)
    g=sum(t*(1/x-t*mp.log1p(1/(t*x))) for x in xs if x>0)
    cubic=sum(1/(3*t*x**3) for x in xs if x>0)
    assert 0<=g<=q/2 and 0<=q/2-g<=cubic; checks+=1
# A deterministic positive mode has finite second coefficient, so criticality matters.
t=mp.mpf(10)**12
assert abs(t*(1-t*mp.log1p(1/t))-mp.mpf('0.5'))<mp.mpf('1e-11'); checks+=1
out=dict(status='PASS finite calibrated controls; not a Fatou/divergence proof',seed=seed,checks=checks,records=records,
    reference='Gamma(2,1): Elog(1+tX)=1+(1-1/t)exp(1/t)E1(1/t), ElogX=1-EulerGamma, E(1/X)=1',
    counter_control='Deterministic positive mode: scaled second gap tends to1/2; zero modes contribute0',
    source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('verification/sheaf_wishart/quota-20261022-0949/critical-second-coefficient-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
