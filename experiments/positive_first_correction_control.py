"""Finite positive-spectrum and Gamma first coefficient controls, not proof."""
from pathlib import Path
import hashlib,json,math,random
from scipy.integrate import quad
seed=2026102242;rng=random.Random(seed);checks=0;records=[]
for n in range(6):
 for k in range(10):
  xs=[0. if rng.random()<.3 else 10**rng.uniform(-2,2) for _ in range(n)]
  inv=sum(1/x for x in xs if x>0);inv2=sum(1/(x*x) for x in xs if x>0)
  for rho in [1.,10.,1e3,1e6]:
   error=sum(math.log1p(1/(rho*x)) for x in xs if x>0)
   gap=inv-rho*error
   assert gap>=-1e-10 and gap<=inv2/(2*rho)+1e-10;checks+=2
   assert 0<=rho*error<=inv+1e-10;checks+=1
for shape in [2,3]:
 known=1/(shape-1)
 moment=quad(lambda x:x**(shape-2)*math.exp(-x)/math.gamma(shape),0,math.inf)[0]
 assert math.isclose(moment,known,rel_tol=1e-10);checks+=1
 for rho in [1.,10.,1000.,1e5]:
  scaled=rho*quad(lambda x:math.log1p(1/(rho*x))*x**(shape-1)*math.exp(-x)/math.gamma(shape),0,math.inf,
     epsabs=1e-13,epsrel=1e-10)[0]
  assert 0<scaled<known*(1+1e-8);checks+=1
  records.append(dict(shape=shape,rho=rho,scaled_offset=scaled,known_inverse_first=known))
assert math.isclose(1e7*math.log1p(1/(2e7)),.5,rel_tol=1e-6);checks+=1
out=dict(status='PASS finite/Gamma controls, not DCT or general model proof',seed=seed,
 checks=checks,spectrum_cases=60,gamma_records=records,
 critical_shape1='inverse first moment divergent; excluded from finite coefficient control',
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('verification/sheaf_wishart/quota-20261022-0949/positive-first-correction-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
