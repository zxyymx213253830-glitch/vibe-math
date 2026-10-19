"""Deterministic scalar control for the square-case scaled correction; not proof."""
from pathlib import Path
import hashlib,json
import mpmath as mp

mp.mp.dps=50
elog=mp.quad(lambda x:mp.exp(-x)*mp.log(x),[0,1,mp.inf])
assert abs(elog+mp.euler)<mp.mpf('1e-40')
records=[]
for rho in [1,10,1000,1000000,100000000]:
    rho=mp.mpf(rho)
    closed=mp.exp(1/rho)*mp.e1(1/rho)
    integral=mp.quad(lambda x:mp.exp(-x)*mp.log1p(rho*x),[0,1,mp.inf])
    assert abs(integral-closed)<mp.mpf('1e-35')
    scaled=rho*(closed-mp.log(rho)-elog)
    assert scaled>0
    records.append(dict(rho=str(rho),capacity=str(closed),scaled_offset=str(scaled)))
assert all(mp.mpf(b['scaled_offset'])>mp.mpf(a['scaled_offset']) for a,b in zip(records,records[1:]))
ratio=mp.mpf(records[-1]['scaled_offset'])/mp.log(mp.mpf(records[-1]['rho']))
assert mp.mpf('.9')<ratio<mp.mpf('1.1')
assert mp.mpf(records[-1]['scaled_offset'])>10
result=dict(seed=None,decimal_precision=50,status='PASS Exp1 direct quadrature vs exp(1/rho)E1(1/rho), ElogX=-EulerGamma and growing scaled-error controls; finite values not a divergence proof',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),records=records)
p=Path(__file__).resolve().parents[1]/'verification/central_mixed_moments/logdet-square-control.json'
p.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(result['status'])
