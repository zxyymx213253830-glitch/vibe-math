"""Fixed seed actual complex Gaussian trace moment checks; not a proof."""
from pathlib import Path
import hashlib
import json
import numpy as np

rng = np.random.default_rng(2026103101)
samples = 200_000
checks = negatives = 0
outcomes = []
for m,n,lam in [(1,1,[]),(2,1,[0.8]),(2,2,[0.3]),(3,2,[0.4,1.2]),(4,3,[0.2,0.7])]:
    mean = np.zeros((m,n), dtype=complex)
    for j,x in enumerate(lam): mean[j,j] = np.sqrt(x)
    t = np.zeros(samples)
    for i in range(m):
        for j in range(n):
            z = (rng.normal(size=samples)+1j*rng.normal(size=samples))/np.sqrt(2)
            t += np.abs(z+mean[i,j])**2
    mu = m*n+sum(lam)
    var = m*n+2*sum(lam)
    mean_est = float(t.mean()); mean_se = float(t.std(ddof=1)/np.sqrt(samples))
    var_est = float(((t-mu)**2).mean()); var_se = float(((t-mu)**2).std(ddof=1)/np.sqrt(samples))
    assert abs(mean_est-mu) <= 6*mean_se+1e-5
    assert abs(var_est-var) <= 6*var_se+1e-5
    checks += 2
    if lam and abs(var-(m*n+sum(lam))) > 0.01: negatives += 1
    outcomes.append(dict(m=m,n=n,lam=lam,mean=mean_est,expected_mean=mu,variance=var_est,expected_variance=var))
result=dict(seed=2026103101,status='PASS',checks=checks,negative_controls=negatives,samples_per_shape=samples,
            source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),results=outcomes,
            not_a_proof=True,scope='actual Gaussian trace mean and centered second moment for candidate law transport')
out=Path(__file__).resolve().parents[1]/'verification/sheaf_wishart/quota-20261022-0949/candidate-trace-moments-control.json'
out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('PASS',checks,'negative',negatives)
