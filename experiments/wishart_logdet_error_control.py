"""Quantitative high-scale logdet error controls; numerical evidence only."""
from pathlib import Path
import hashlib,json
import numpy as np
from scipy.integrate import quad

SEED=2026101922
rng=np.random.default_rng(SEED)
records=[]
for m,n,shift in [(1,1,.2),(3,1,0.),(5,3,.1)]:
    z=(rng.normal(size=(200000,m,n))+1j*rng.normal(size=(200000,m,n)))/np.sqrt(2)+shift
    w=z.conj().transpose(0,2,1)@z
    eig=np.linalg.eigvalsh(w)
    assert np.all(eig>0)
    for rho in [1.,10.,1e3,1e6]:
        error=np.log1p(1/(rho*eig)).sum(axis=1)
        independent=np.log1p(rho*eig).sum(axis=1)-n*np.log(rho)-np.log(eig).sum(axis=1)
        assert np.allclose(error,independent,atol=2e-13,rtol=1e-7)
        assert np.all(error>=0)
        for p in [.25,.5,.75,1.]:
            bound=np.sum((1/eig)**p,axis=1)/(p*rho**p)
            assert np.all(error<=bound*(1+1e-12))
        records.append(dict(m=m,n=n,mean_entry=shift,rho=rho,mean_error=float(error.mean()),scaled_error=float(rho*error.mean())))

# Independent scalar Gamma(shape3,rate1) controls: E(1/X)=1/2,
# rho E log(1+1/(rho X))->1/2. This does not hold finitely in square shape1.
scalar=[]
inverse=quad(lambda x: x*np.exp(-x)/2,0,np.inf)[0]
assert abs(inverse-.5)<1e-10
for rho in [1.,10.,1e3,1e6]:
    val=quad(lambda x: rho*np.log1p(1/(rho*x))*x*x*np.exp(-x)/2,0,np.inf,epsabs=1e-10)[0]
    assert 0<val<.5
    scalar.append(dict(rho=rho,scaled_error=val))
assert abs(scalar[-1]['scaled_error']-.5)<1e-5
u=1e-6
assert np.log1p(u)>u**2/2  # p>1 would falsely claim a faster universal bound.
result=dict(seed=SEED,samples_per_shape=200000,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),status='PASS pointwise fractional log error, independent full-offset identity, Gamma3 quadrature/inverse moment and invalid p2 negative controls; not proof',records=records,scalar_gamma3=scalar)
p=Path(__file__).resolve().parents[1]/'verification/central_mixed_moments/logdet-error-control.json'
p.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(result['status'])
