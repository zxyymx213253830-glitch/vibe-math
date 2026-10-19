"""Deterministic reuse of fixed-seed actual samples for logdet mean upper bounds."""
from pathlib import Path
import hashlib,json,math

r=Path(__file__).resolve().parents[1]
sources=[('logdet-prelog-control.json','values',2026101921),('wide-logdet-control.json','statistics',2026101924)]
records=[];inputs=[]
for name,key,seed in sources:
    p=r/'verification/central_mixed_moments'/name
    d=json.loads(p.read_text(encoding='utf-8'))
    assert d['status'].startswith('PASS') and d['seed']==seed
    inputs.append(dict(path=p.relative_to(r).as_posix(),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),original_seed=seed))
    for case in d['records']:
        k=min(case['m'],case['n'])
        power=case['trace_control']
        for v in case[key]:
            bound=k*math.log1p(v['rho']*power/k)
            assert v['mean']<=bound+1e-3
            records.append(dict(m=case['m'],n=case['n'],rho=v['rho'],observed_mean=v['mean'],known_power=power,upper_bound=bound))
scalar=records[0]
assert scalar['m']==scalar['n']==1
assert scalar['observed_mean']>math.log1p(scalar['rho']*scalar['known_power']/2)
out=dict(seed=None,status='PASS reused fixed-seed actual CN means against min-dimension logdet/Jensen bound with known trace controls; wrong-half-power negativecontrol; not proof',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),inputs=inputs,records=records)
p=r/'verification/central_mixed_moments/logdet-mean-bound-control.json'
p.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(out['status'])
