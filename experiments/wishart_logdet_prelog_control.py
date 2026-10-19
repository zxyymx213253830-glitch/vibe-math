"""Fixed-seed controls for full spectral log-det growth; numerical, not proof."""
from pathlib import Path
import hashlib,json
import numpy as np
from scipy.special import exp1

SEED=2026101921
rng=np.random.default_rng(SEED)
size=200_000
records=[]
for m,n,shift in [(1,1,0.),(2,2,0.3),(4,2,0.5),(5,3,0.2)]:
    mean=np.full((m,n),shift+0.1j*shift)
    z=(rng.normal(size=(size,m,n))+1j*rng.normal(size=(size,m,n)))/np.sqrt(2)+mean
    w=z.conj().transpose(0,2,1)@z
    eig=np.linalg.eigvalsh(w)
    assert np.all(eig>0)
    trace=np.trace(w,axis1=1,axis2=2).real
    expected_trace=m*n+np.linalg.norm(mean)**2
    trace_se=np.sqrt((m*n+2*np.linalg.norm(mean)**2)/size)
    assert abs(trace.mean()-expected_trace)<6*trace_se
    logdet=np.log(eig).sum(axis=1)
    rho_values=[1.,10.,1e3,1e5,1e8]
    gaps=[]; values=[]
    for rho in rho_values:
        c=np.log1p(rho*eig).sum(axis=1)
        _,direct=np.linalg.slogdet(np.eye(n)+rho*w[:1000])
        assert np.allclose(c[:1000],direct,rtol=1e-7,atol=1e-7)
        gap=float((c-n*np.log(rho)-logdet).mean())
        assert gap>=-1e-9
        gaps.append(gap);values.append(dict(rho=rho,mean=float(c.mean()),mean_gap=gap))
        if m==n==1:
            known=float(np.exp(1/rho)*exp1(1/rho))
            se=float(c.std(ddof=1)/np.sqrt(size))
            assert abs(c.mean()-known)<6*se
    assert np.all(np.diff(gaps)<=1e-10) and gaps[-1]<0.005
    corrected=values[-1]['mean']/np.log(rho_values[-1])-n-logdet.mean()/np.log(rho_values[-1])
    assert abs(corrected)<0.005/np.log(rho_values[-1])
    assert abs(values[-1]['mean']/np.log(rho_values[-1])-n/2)>0.3
    records.append(dict(m=m,n=n,mean_entry=[float(mean[0,0].real),float(mean[0,0].imag)],
        trace_observed=float(trace.mean()),trace_control=float(expected_trace),
        trace_SE=float(trace_se),mean_logdet=float(logdet.mean()),values=values))

result=dict(seed=SEED,samples_per_shape=size,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    status='PASS actual CN logdet/spectrum, known scalar exp(1/rho)E1(1/rho), noncentral trace and wrong-prelog negative controls; not proof',records=records)
p=Path(__file__).resolve().parents[1]/'verification/central_mixed_moments/logdet-prelog-control.json'
p.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(result['status'])
