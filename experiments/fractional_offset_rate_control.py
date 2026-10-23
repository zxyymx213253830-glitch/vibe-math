"""Subcritical fractional offset controls, not endpoint asymptotics or proof."""
from pathlib import Path
import hashlib,json,math,random
from scipy.integrate import quad
seed=2026102241;rng=random.Random(seed);checks=0;records=[]
for alpha in [.1,.25,.45,.5,1.0]:
 for x in [0.,1e-8,.2,1.,10.,1e4,1e8]:
  assert math.log1p(x)<=x**alpha/alpha+1e-12;checks+=1
 for n in range(6):
  for t in range(8):
   xs=[0. if rng.random()<.3 else 10**rng.uniform(-4,4) for _ in range(n)]
   pos=[x for x in xs if x>0]
   for rho in [1.,10.,1e4]:
    err=sum(math.log1p(1/(rho*x)) for x in pos)
    if pos:
     bound=(n/alpha)*rho**(-alpha)*min(pos)**(-alpha)
     assert 0<=err<=bound*(1+1e-12);checks+=1
     assert err*err<=bound*bound*(1+1e-12);checks+=1
    else:
     assert err==0;checks+=1
for alpha in [.125,.25,.45]:
 q=2*alpha;known=math.gamma(1-q)
 moment=quad(lambda x:x**(-q)*math.exp(-x),0,1,epsabs=1e-9)[0]+quad(lambda x:x**(-q)*math.exp(-x),1,math.inf,epsabs=1e-10)[0]
 assert math.isclose(moment,known,rel_tol=1e-7,abs_tol=1e-8);checks+=1
 for rho in [1.,10.,1e3]:
  err=quad(lambda x:math.log1p(1/(rho*x))**2*math.exp(-x),0,1,epsabs=1e-10)[0]+quad(lambda x:math.log1p(1/(rho*x))**2*math.exp(-x),1,math.inf,epsabs=1e-11)[0]
  bound=alpha**(-2)*rho**(-q)*known
  assert 0<err<=bound*(1+1e-8);checks+=1
  records.append(dict(alpha=alpha,rho=rho,mse=err,bound=bound,inverse_moment=known))
assert math.log1p(1e6)>(1e6)**.1;checks+=1
out=dict(status='PASS finite fractional controls, not general proof',seed=seed,
 checks=checks,gamma_shape1_records=records,
 negative_control='omitting 1/alpha fails at alpha=.1,x=1e6',
 endpoint='q=1 at Gamma shape1 excluded; not inferred from finite cutoff',
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('verification/sheaf_wishart/quota-20261022-0949/fractional-offset-rate-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
