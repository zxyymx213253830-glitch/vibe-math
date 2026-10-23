"""Finite/Gamma second high-scale coefficient controls, not a DCT proof."""
from pathlib import Path
import hashlib,json,math,random
import mpmath as mp
from scipy.integrate import quad
mp.mp.dps=60;seed=2026102243;rng=random.Random(seed);checks=0;records=[]
for n in range(6):
 for k in range(8):
  xs=[mp.mpf(0) if rng.random()<.3 else mp.mpf(rng.randrange(1,8))/rng.randrange(1,6) for _ in range(n)]
  L=sum(1/x for x in xs if x>0);Q=sum(1/x**2 for x in xs if x>0);T=sum(1/x**3 for x in xs if x>0)
  for r0 in [1,10,1000,1000000]:
   r=mp.mpf(r0);E=sum(mp.log1p(1/(r*x)) for x in xs if x>0)
   G=r*(L-r*E);gap=Q/2-G
   assert -mp.mpf('1e-40')<=G<=Q/2+mp.mpf('1e-40');checks+=2
   assert -mp.mpf('1e-40')<=gap<=T/(3*r)+mp.mpf('1e-40');checks+=2
def gap(u):
 if u<1e-3:return sum((-1)**j*u**j/j for j in range(2,12))
 return u-math.log1p(u)
for shape in [3,4]:
 half=1/(2*(shape-1)*(shape-2))
 for rho in [1.,10.,1000.,1e5]:
  value=rho*rho*quad(lambda x:gap(1/(rho*x))*x**(shape-1)*math.exp(-x)/math.gamma(shape),0,math.inf,
    epsabs=1e-16,epsrel=1e-9)[0]
  assert 0<value<=half*(1+1e-6);checks+=1
  records.append(dict(shape=shape,rho=rho,scaled_positive_gap=value,known_half_inverse_square=half))
assert abs(float(mp.mpf(10)**8*(mp.mpf('.5')-mp.mpf(10)**8*mp.log1p(1/(mp.mpf(2)*10**8))))-.125)<1e-8;checks+=1
out=dict(status='PASS finite/Gamma controls, not general model or DCT proof',seed=seed,
 checks=checks,spectrum_cases=48,gamma_records=records,
 coefficient_sign='positive gap coefficient EQ/2; logdet second expansion coefficient -EQ/2',
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('verification/sheaf_wishart/quota-20261022-0949/positive-second-correction-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
