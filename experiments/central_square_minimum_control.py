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
    scale_controls = []
    for a in (0.4, 1.7, 3.0):
        # Exact sample scaling is additionally checked on the final fixed-seed batch.
        W_scaled = (a*X).conj().transpose(0, 2, 1) @ (a*X)
        actual = np.linalg.eigvalsh(W_scaled)[:, 0]
        expected_scaled = a*a*np.linalg.eigvalsh(W)[:, 0]
        error = float(np.max(np.abs(actual-expected_scaled)))
        assert error < 1e-10
        # Same actual full sample, no independence or new density assertion.
        scaled_tail = float(((a*a*lam) > (0.75*a*a/n)).mean())
        expected_tail = float(np.exp(-0.75))
        se = (scaled_tail-expected_tail)/np.sqrt(expected_tail*(1-expected_tail)/N)
        assert abs(se) < 6
        scale_controls.append(dict(amplitude=a, variance=a*a, rate=n/(a*a),
                                   max_pointwise_minimum_error=error, tail_standard_errors=se))
    records.append(dict(size=n, samples=N, trace_Gamma_standard_errors=trace_se,
                        minimum_mean_standard_errors=mean_se, thresholds=thresholds))
    records[-1]['scale_controls'] = scale_controls
    x = 0.75/n
    selected = lam > x
    count = int(selected.sum())
    residual_trace = tr[selected]-n*x
    trace_residual_se = (residual_trace.mean()-n*n)/(n/np.sqrt(count))
    min_residual_se = ((lam[selected]-x).mean()-1/n)/(1/n/np.sqrt(count))
    assert abs(trace_residual_se) < 6 and abs(min_residual_se) < 6
    records[-1]['matrix_memoryless_control'] = dict(threshold=x, conditional_count=count,
        shifted_trace_Gamma_mean_standard_errors=trace_residual_se,
        shifted_minimum_Exp_mean_standard_errors=min_residual_se,
        interpretation='Conditional whole-matrix claim checked only via two known marginal controls; not proof')
report = dict(seed=SEED, source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              collected_utc=datetime.now(timezone.utc).isoformat(), records=records,
              status='PASS actual samples; known trace Gamma and Exp(rate n) controls',
              interpretation='Numerical control, not proof; CN variance one, real components variance one half')
target = Path(__file__).resolve().parents[1]/'verification/central_closed_density/minimum-control.json'
target.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
print(report['status'])
