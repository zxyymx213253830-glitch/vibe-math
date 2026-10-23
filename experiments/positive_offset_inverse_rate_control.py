"""Finite-spectrum/Gamma controls for inverse-square offset rates; not proof."""
from pathlib import Path
import hashlib,json,math,random
from scipy.integrate import quad
seed=2026102239;rng=random.Random(seed);checks=0;records=[]
for n in range(6):
 for t in range(12):
  vals=[0.0 if rng.random()<0.35 else 10.0**rng.uniform(-4,4) for _ in range(n)]
  positives=[x for x in vals if x>0]
  for rho in [1.0,3.0,100.0,1e5]:
   direct=sum(math.log1p(rho*x) for x in vals)-len(positives)*math.log(rho)-sum(math.log(x) for x in positives)
   stable=sum(math.log1p(1/(rho*x)) for x in positives)
   assert math.isclose(direct,stable,rel_tol=1e-8,abs_tol=2e-12);checks+=1
   if positives:
    floor=min(positives);bound=n/(rho*floor)
    assert stable>=0 and stable<=bound*(1+1e-13)
    assert stable*stable<=bound*bound*(1+1e-13);checks+=2
   else:
    assert direct==stable==0;checks+=1
for k in [3,4]:
 known=1/((k-1)*(k-2))
 moment=quad(lambda x:x**(k-3)*math.exp(-x)/math.gamma(k),0,math.inf,epsabs=1e-12)[0]
 assert math.isclose(moment,known,rel_tol=1e-10,abs_tol=1e-12);checks+=1
 for rho in [1.0,5.0,100.0,10000.0]:
  err=quad(lambda x: math.log1p(1/(rho*x))**2*x**(k-1)*math.exp(-x)/math.gamma(k),
      0,math.inf,epsabs=1e-14,epsrel=1e-9)[0]
  ratio=rho*rho*err
  assert 0<ratio<=known*(1+1e-7);checks+=1
  records.append(dict(shape=k,rho=rho,scaled_mse=ratio,known_inverse_square=known))
assert math.log1p(1/(3*2))<=1/6;checks+=1
out=dict(status='PASS finite controls only, not general probability proof',seed=seed,
 checks=checks,spectrum_cases=72,gamma_records=records,
 critical_shape2='inverse-square diverges logarithmically near zero; not estimated by cutoff',
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('verification/sheaf_wishart/quota-20261022-0949/positive-offset-inverse-rate-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
