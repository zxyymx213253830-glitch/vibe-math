"""Wide Gaussian matrices: full logdet and small-side controls, not proof."""
from pathlib import Path
import hashlib,json
import numpy as np
from scipy.special import digamma,polygamma

SEED=2026101924
rng=np.random.default_rng(SEED)
records=[]
for m,n,shift in [(1,3,0.),(2,4,.2),(3,5,.1)]:
    count=200000
    z=(rng.normal(size=(count,m,n))+1j*rng.normal(size=(count,m,n)))/np.sqrt(2)+shift
    row=z@z.conj().transpose(0,2,1)
    val=np.linalg.eigvalsh(row)
    assert np.all(val>0)
    power=np.trace(row,axis1=1,axis2=2).real
    expected=m*n*(1+shift**2)
    se=np.sqrt(m*n*(1+2*shift**2)/count)
    assert abs(power.mean()-expected)<6*se
    mean_logdet=np.log(val).sum(axis=1).mean()
    if m==1:
        known=digamma(n)
        assert abs(mean_logdet-known)<6*np.sqrt(polygamma(1,n)/count)
    xs=z[:1000]
    col=xs.conj().transpose(0,2,1)@xs
    trans=xs.transpose(0,2,1)
    transgram=trans.conj().transpose(0,2,1)@trans
    assert np.allclose(transgram.transpose(0,2,1),row[:1000])
    rhos=[1.,10.,1e3,1e5]
    stats=[]
    for rho in rhos:
        _,large=np.linalg.slogdet(np.eye(n)+rho*col)
        _,small=np.linalg.slogdet(np.eye(m)+rho*row[:1000])
        _,via_trans=np.linalg.slogdet(np.eye(m)+rho*transgram)
        assert np.allclose(large,small,rtol=1e-7,atol=1e-7)
        assert np.allclose(small,via_trans,rtol=1e-10,atol=1e-10)
        c=np.log1p(rho*val).sum(axis=1)
        stats.append(dict(rho=rho,mean=float(c.mean()),offset=float(c.mean()-m*np.log(rho))))
    assert abs(stats[-1]['offset']-mean_logdet)<1e-3
    assert abs(stats[-1]['mean']/np.log(rhos[-1])-n)>.5
    records.append(dict(m=m,n=n,mean_entry=shift,trace_observed=float(power.mean()),trace_control=float(expected),mean_logdet_small=float(mean_logdet),statistics=stats))
p=Path(__file__).resolve().parents[1]/'verification/central_mixed_moments/wide-logdet-control.json'
result=dict(seed=SEED,samples_per_shape=200000,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),status='PASS Sylvester/transpose determinants, noncentral trace and scalarGamma digamma controls, wrong-N prelog negativecontrol; not proof',records=records)
p.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(result['status'])
