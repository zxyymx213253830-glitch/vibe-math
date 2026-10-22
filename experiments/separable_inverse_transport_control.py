"""Exact power-tail product calibrations and a nonproduct countercontrol."""
from pathlib import Path
import hashlib,json,sys,math
from scipy.integrate import quad
SEED=2026102233;checks=0;cases=0
for kappa in [1,2,3]:
 for p in [kappa/3,2*kappa/3]:
  for sign in [-1,1]:
   cases+=1
   # independent a~density kappa*a^(kappa-1), h~Uniform(0,1), f=a*(1+h*h)^sign.
   inner=quad(lambda h:(1+h*h)**(-sign*p),0,1)[0]
   ref=kappa/(kappa-p)*inner
   actual=quad(lambda a:kappa*a**(kappa-p-1)*inner,0,1)[0]
   assert abs(actual-ref)<1e-8;checks+=1
 for p in [kappa,kappa+0.5]:
  cases+=1
  truncated=[]
  for delta in [0.1,0.01,0.001]:
   ref=kappa*math.log(1/delta) if p==kappa else kappa*(1-delta**(kappa-p))/(kappa-p)
   val=quad(lambda a:kappa*a**(kappa-p-1),delta,1)[0]
   assert abs(val-ref)<1e-6;checks+=1;truncated.append(val)
  assert truncated[0]<truncated[1]<truncated[2];checks+=1
# Negative control: same marginal power factor is insufficient without product law.
# On the diagonal h=a~Uniform(0,1): g=a, K=a^(-1/2), f=sqrt(a), p=3/2.
# Both f^-p and K^p have finite integral4, while g^-p diverges.
cases+=1
assert abs(quad(lambda a:a**(-0.75),0,1)[0]-4)<1e-8;checks+=1
for a in [0.01,0.1,0.5,1]:
 K=a**(-0.5);f=math.sqrt(a)
 assert a<=K*f+1e-12 and f<=K*a+1e-12;checks+=1
assert 2*(0.001**(-0.5)-1)>2*(0.01**(-0.5)-1);checks+=1
out=dict(seed=SEED,cases=cases,checks=checks,status='PASS',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Closed power-tail and negative-dependence controls only, not a general measure-theory proof',known_controls=['independent factorized integral kappa/(kappa-p)','critical logarithm divergence','supercritical truncated power divergence','nonproduct dependence countercontrol'])
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out))
