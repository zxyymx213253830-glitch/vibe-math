"""Fixed-seed continuous-coordinate and atomic negative controls; not a proof."""
from pathlib import Path
import hashlib
import json
import numpy as np
from scipy.stats import gamma

rng=np.random.default_rng(2026103103)
samples=200_000
checks=negatives=0
results=[]
for shape in (1,2,4,7):
    values=rng.gamma(shape,1,size=samples)
    for x in (0.3,1.0,3.0):
        assert np.count_nonzero(values == x)==0
        expected=float(gamma.cdf(x,shape))
        observed=float(np.mean(values<=x))
        stderr=np.sqrt(expected*(1-expected)/samples)
        assert abs(observed-expected)<=6*stderr+1e-4
        checks+=2
        results.append(dict(shape=shape,x=x,observed=observed,expected=expected))
for mass in (0.1,0.5):
    atomic=np.array([1.0,2.0]); weights=np.array([mass,1-mass])
    assert np.sum(weights[atomic<=1.0])-np.sum(weights[atomic<1.0])==mass
    negatives+=1
result=dict(seed=2026103103,status='PASS',checks=checks,negative_controls=negatives,
            samples_per_shape=samples,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            not_a_proof=True,scope='continuous Gamma-coordinate calibration and atomic countercontrols')
out=Path(__file__).resolve().parents[1]/'verification/sheaf_wishart/quota-20261022-0949/candidate-coordinate-atom-control.json'
out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('PASS',checks,'negative',negatives)
