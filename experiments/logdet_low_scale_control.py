"""Deterministic Gamma controls for the low-scale expected logdet slope."""
from pathlib import Path
import hashlib,json
import mpmath as mp

mp.mp.dps=40
records=[]
for k in [1,3]:
    density=lambda x:mp.exp(-x)*x**(k-1)/mp.factorial(k-1)
    mean=mp.quad(lambda x:x*density(x),[0,1,mp.inf])
    assert abs(mean-k)<mp.mpf('1e-30')
    for rho in [mp.mpf('.1'),mp.mpf('.001'),mp.mpf('.000001')]:
        c=mp.quad(lambda x:mp.log1p(rho*x)*density(x),[0,1,mp.inf])
        assert 0<c/rho<k
        assert c<=mp.log1p(rho*k)
        if k==1:assert abs(c-mp.exp(1/rho)*mp.e1(1/rho))<mp.mpf('1e-30')
        records.append(dict(gamma_shape=k,rho=str(rho),capacity=str(c),slope=str(c/rho)))
    assert abs(c/rho-k)<mp.mpf('.0001')
    assert abs(c/rho-k/2)>mp.mpf('.4')
p=Path(__file__).resolve().parents[1]/'verification/central_mixed_moments/logdet-low-scale-control.json'
result=dict(seed=None,decimal_precision=40,status='PASS Gamma1/3 knownmean, direct quadrature vs Exp1 closedform, scalarJensen and wronghalfscale negativecontrol; not proof',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),records=records)
p.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(result['status'])
