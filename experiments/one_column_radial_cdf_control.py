"""Analytic CDF and actual properCN1 four-row controls before bridge source."""
from pathlib import Path
import hashlib,json,math
import numpy as np
from scipy.integrate import quad
from scipy.special import ive
from scipy.stats import ncx2
seed=2026102250; rng=np.random.default_rng(seed); checks=0; records=[]
def kernel(q,a,r):
    if a==0:
        return r**(2*q+1)*math.exp(-r*r/2)/(2**q*math.factorial(q))
    return r**(q+1)/a**q*math.exp(-(r-a)**2/2)*ive(q,a*r)
xs=[0.,0.2,1.,5.,15.]
for q in range(7):
    for lam in [0.5,2.,5.]:
        a=math.sqrt(2*lam)
        for x in xs:
            b=math.sqrt(2*x)
            lo=quad(lambda r:kernel(q,a,r),0,b,epsabs=1e-11)[0]
            tail=quad(lambda r:kernel(q,a,r),b,math.inf,epsabs=1e-11)[0]
            ref=ncx2.cdf(2*x,2*(q+1),2*lam)
            assert abs(lo-ref)<3e-9;checks+=1
            assert abs(1-tail-ref)<3e-9;checks+=1
samples=200000
for lam in [0.5,2.,5.]:
    mean=rng.normal(size=4)+1j*rng.normal(size=4)
    mean*=math.sqrt(lam/float(np.vdot(mean,mean).real))
    assert abs(float(np.vdot(mean,mean).real)-lam)<1e-12;checks+=1
    noise=(rng.normal(size=(samples,4))+1j*rng.normal(size=(samples,4)))/math.sqrt(2)
    energy=np.sum(abs(noise+mean)**2,axis=1)
    for x in xs:
        ref=ncx2.cdf(2*x,8,2*lam); observed=float(np.mean(energy<=x))
        sigma=math.sqrt(ref*(1-ref)/samples)
        assert abs(observed-ref)<=6*sigma+5/samples;checks+=1
        records.append(dict(lam=lam,x=x,observed=observed,reference=float(ref)))
for x in xs:
    lo=quad(lambda r:kernel(3,0.,r),0,math.sqrt(2*x),epsabs=1e-11)[0]
    assert abs(lo-ncx2.cdf(2*x,8,0.))<1e-11;checks+=1
# Missing factor2 in noncentrality gives a materially different known CDF.
assert abs(ncx2.cdf(18.,8,10.)-ncx2.cdf(18.,8,5.))>0.02;checks+=1
out=dict(status='PASS calibrated CDF/source controls; not a probability proof',seed=seed,checks=checks,
    samples_per_actual_case=samples,actual_cases=3,records=records,
    reference='Energy of properCN1 M+Z: noncentral chi-square(df2m,nc2||M||F^2)/2; centered Gamma4 calibration',
    source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('verification/sheaf_wishart/quota-20261022-0949/one-column-radial-cdf-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k!='records'}))
