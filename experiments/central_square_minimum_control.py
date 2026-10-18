"""Actual CN square Gram samples versus Exp(rate n) and known trace Gamma.

Reproducible control only; no numerical result is a mathematical proof.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import numpy as np

SEED = 20261018
N = 200_000
BATCH = 5000
rng = np.random.default_rng(SEED)
records = []
for n in (1, 2, 3, 4):
    eigen_min, traces = [], []
    for start in range(0, N, BATCH):
        count = min(BATCH, N-start)
        X = (rng.standard_normal((count, n, n)) +
             1j*rng.standard_normal((count, n, n))) / np.sqrt(2)
        W = X.conj().transpose(0, 2, 1) @ X
        eigen_min.append(np.linalg.eigvalsh(W)[:, 0])
        traces.append(np.trace(W, axis1=1, axis2=2).real)
    lam = np.concatenate(eigen_min)
    tr = np.concatenate(traces)
    trace_se = (tr.mean()-n*n)/np.sqrt(n*n/N)
    mean_se = (lam.mean()-1/n)/(1/n/np.sqrt(N))
    assert abs(trace_se) < 6 and abs(mean_se) < 6
    thresholds = []
    for y in (0.25, 0.75, 1.5, 3.):
        x = y/n
        expected = float(np.exp(-n*x))
        empirical = float((lam > x).mean())
        se = (empirical-expected)/np.sqrt(expected*(1-expected)/N)
        assert abs(se) < 6
        thresholds.append(dict(x=x, expected_tail=expected,
                               empirical_tail=empirical, standard_errors=se))
    records.append(dict(size=n, samples=N, trace_Gamma_standard_errors=trace_se,
                        minimum_mean_standard_errors=mean_se, thresholds=thresholds))
report = dict(seed=SEED, source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              collected_utc=datetime.now(timezone.utc).isoformat(), records=records,
              status='PASS actual samples; known trace Gamma and Exp(rate n) controls',
              interpretation='Numerical control, not proof; CN variance one, real components variance one half')
target = Path(__file__).resolve().parents[1]/'verification/central_closed_density/minimum-control.json'
target.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
print(report['status'])
