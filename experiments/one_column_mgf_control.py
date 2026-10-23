"""Seeded MGF controls before any MGF-source proof. Numerical evidence only."""
from pathlib import Path
import hashlib,json,math
import numpy as np
from scipy.integrate import quad
from scipy.special import ive

seed=2026102251
rng=np.random.default_rng(seed)
checks=0
for s in [-.5,-.1,0.,.3,.7]:
    for u in [-2.,0.,.5,2.]:
        value=quad(lambda z:math.exp((s-1)*z*z/2+s*u*z+s*u*u/2)/math.sqrt(2*math.pi),-math.inf,math.inf,epsabs=1e-10)[0]
        ref=(1-s)**(-.5)*math.exp(u*u*s/(2*(1-s)))
        assert math.isclose(value,ref,rel_tol=2e-10,abs_tol=1e-10)
        checks+=1
for q in range(6):
    for a in [0.,.5,3.]:
        for s in [-.5,0.,.3]:
            def weighted(r):
                if a==0:
                    return r**(2*q+1)*math.exp(-(1-s)*r*r/2)/(2**q*math.factorial(q))
                return r**(q+1)/a**q*math.exp(-(1-s)*r*r/2+a*r-a*a/2)*ive(q,a*r)
            value=quad(weighted,0,math.inf,epsabs=1e-10,epsrel=1e-10)[0]
            ref=(1-s)**(-(q+1))*math.exp(a*a*s/(2*(1-s)))
            assert math.isclose(value,ref,rel_tol=3e-10,abs_tol=1e-10)
            checks+=1
for m in range(1,7):
    u=rng.normal(size=2*m)
    for s in [-.2,.3]:
        product=np.prod((1-s)**(-.5)*np.exp(u*u*s/(2*(1-s))))
        ref=(1-s)**(-m)*math.exp(float(u@u)*s/(2*(1-s)))
        assert math.isclose(product,ref,rel_tol=1e-12)
        checks+=1
for m in [2,4,8]:
    u=rng.normal(size=2*m)*.3
    s=.1
    y=np.sum((rng.normal(size=(200000,2*m))+u)**2,axis=1)/2
    samples=np.exp(s*y)
    def mgf(t):
        return (1-t)**(-m)*math.exp(float(u@u)*t/(2*(1-t)))
    ref=mgf(s)
    se=math.sqrt((mgf(2*s)-ref*ref)/len(y))
    assert abs(float(samples.mean())-ref)<6*se
    checks+=1
# Equal first two moments do not imply equal MGF / distribution.
x=np.array([-1.,1.]); p=np.array([.5,.5])
y=np.array([-math.sqrt(2),0.,math.sqrt(2)]); w=np.array([.25,.5,.25])
assert abs(p@x-w@y)<1e-14 and abs(p@(x*x)-w@(y*y))<1e-14
assert abs(p@np.exp(.5*x)-w@np.exp(.5*y))>1e-3
checks+=1
out=dict(seed=seed,checks=checks,status='PASS finite controls; not proof',
    reference='Completed-square scalar Gaussian integral; Gamma/Rice weighted radial integral; exact Gaussian MGF second moment; finite-support moment negative control',
    scope='MGF route only, no actual general-row radial-law theorem',
    source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('verification/sheaf_wishart/quota-20261022-0949/one-column-mgf-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
