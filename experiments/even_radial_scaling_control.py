"""Controls for the new radial scaling bridge, before its Lean source."""
from pathlib import Path
import hashlib,json
import mpmath as mp
import numpy as np
mp.mp.dps=45
seed=2026102401
rng=np.random.default_rng(seed)
checks=0
def kernel(q,a,r):
    return r**(2*q+1)/2**q*mp.exp(-(r*r+a*a)/2)*mp.hyper([], [q+1], (a*r)**2/4)/mp.factorial(q)
for q in range(6):
    for a in map(mp.mpf,[-2,0,1]):
        for r in map(mp.mpf,[-1,0,.5,3]):
            for c in map(mp.mpf,[.4,1,2]):
                left=mp.exp((1-c*c)*r*r/2)*kernel(q,a,r)
                right=mp.exp(a*a*(1-c*c)/(2*c*c))/c**(2*q+1)*kernel(q,a/c,c*r)
                assert mp.almosteq(left,right,rel_eps=mp.mpf('1e-38'),abs_eps=mp.mpf('1e-38'))
                checks+=1
# Central case is the normalized Gamma radial kernel, including q=0.
for q in range(6):
    c=mp.mpf('0.7')
    value=mp.quad(lambda r:mp.exp((1-c*c)*r*r/2)*kernel(q,mp.mpf(0),r),[0,mp.inf])
    assert mp.almosteq(value,c**(-2*(q+1)),rel_eps=mp.mpf('1e-35'))
    checks+=1
# An omitted Jacobian fails already for the centered two-real-dimensional case.
c=mp.mpf('0.7')
assert abs(c**(-2)-c**(-1))>mp.mpf('.1')
checks+=1
out=dict(seed=seed,checks=checks,status='PASS finite controls; not proof',
    reference='Exact hypergeometric kernel scaling; central Gamma integral; missing-Jacobian negative control',
    scope='Real a/r including zero and negative r; positive scale; no actual general-row Gaussian law',
    source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('verification/sheaf_wishart/quota-20261022-0949/even-radial-scaling-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
