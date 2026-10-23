"""Fixed controls for natural-order Bessel/Nuttall normalization, before source."""
from pathlib import Path
import hashlib,json,math
import mpmath as mp
from scipy.integrate import quad
from scipy.special import ive
from scipy.stats import ncx2
mp.mp.dps=45; seed=2026102249; checks=0
for q in range(9):
    for z in [mp.mpf(0),mp.mpf('0.5'),mp.mpf('-0.7'),mp.mpc('1.2','0.5'),mp.mpc('-1.3','2')]:
        series=(z/2)**q*mp.nsum(lambda n:(z*z/4)**n/(mp.factorial(n)*mp.factorial(n+q)),[0,mp.inf])
        assert mp.almosteq(series,mp.besseli(q,z),rel_eps=mp.mpf('1e-38'),abs_eps=mp.mpf('1e-38'));checks+=1
def kernel(q,a,r):
    a=abs(a)
    if a==0:
        return r**(2*q+1)*math.exp(-r*r/2)/(2**q*math.factorial(q))
    return r**(q+1)/a**q*math.exp(-(r-a)**2/2)*ive(q,a*r)
for q in range(7):
    for a in [-1.,0.,0.5,3.]:
        for r in [0.,0.2,1.,5.]:
            value=kernel(q,a,r)
            reference=2*r*ncx2.pdf(r*r,2*(q+1),a*a)
            assert math.isclose(value,reference,rel_tol=2e-11,abs_tol=1e-13);checks+=1
    for a in [0.,0.5,3.]:
        mass,error=quad(lambda r:kernel(q,a,r),0,math.inf,epsabs=1e-11,epsrel=1e-11)
        assert abs(mass-1)<2e-10;checks+=1
out=dict(status='PASS calibrated finite controls; no general kernel/law proof',seed=seed,checks=checks,
    reference='mpmath integer BesselI and SciPy ncx2 radial transform; centered Gamma and q0 Rice calibrations',
    scope='All-order series and analytic normalization target; actual general-row noncentral Gaussian law remains separate',
    source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('verification/sheaf_wishart/quota-20261022-0949/general-nuttall-normalization-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
