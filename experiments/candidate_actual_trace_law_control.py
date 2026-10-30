"""Reproducible actual complex-Gaussian trace controls; not a proof."""
from pathlib import Path
import hashlib
import json
import numpy as np

rng = np.random.default_rng(2026103013)
checks, negatives = 0, 0
results = []
samples = 200_000
for n, q, lam in [(1,0,[]),(1,2,[0.7]),(2,0,[0.4]),
                  (2,1,[0.3,1.1]),(3,0,[0.2,0.8]),(3,2,[0.5])]:
    m = n+q
    mean = np.zeros((m,n), dtype=complex)
    for j,a in enumerate(lam):
        mean[j,j] = np.sqrt(a)
    total = np.zeros(samples)
    for i in range(m):
        for j in range(n):
            z = (rng.standard_normal(samples) + 1j*rng.standard_normal(samples))/np.sqrt(2)
            total += np.abs(z+mean[i,j])**2
    for s in (0.2, 0.7, 1.4):
        values = np.exp(-s*total)
        empirical = float(values.mean())
        stderr = float(values.std(ddof=1)/np.sqrt(samples))
        expected = float((1+s)**(-m*n)*np.exp(-s*sum(lam)/(1+s)))
        assert abs(empirical-expected) <= 6*stderr+1e-5
        checks += 1
        wrong = float((1+s)**(-m*n)*np.exp(-s*sum(lam)))
        if abs(wrong-expected) > 0.001:
            negatives += 1
        results.append(dict(n=n,q=q,rank=len(lam),s=s,empirical=empirical,expected=expected,stderr=stderr))
assert negatives > 0
result = dict(seed=2026103013,status='PASS',checks=checks,negative_controls=negatives,
              samples_per_shape=samples, results=results,
              source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              not_a_proof=True,scope='actual complex Gaussian trace versus scalar candidate transform; not joint spectrum')
out = Path(__file__).resolve().parents[1]/'verification/sheaf_wishart/quota-20261022-0949/candidate-actual-trace-control.json'
out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('PASS',checks,'negative',negatives,'samples per shape',samples)
