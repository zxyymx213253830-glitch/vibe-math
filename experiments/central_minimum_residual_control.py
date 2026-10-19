"""Actual-sample controls for a residual/Gamma hard-edge sandwich, not proof."""
from pathlib import Path
import hashlib
import json
import numpy as np
from scipy.special import gammainc

SEED, N = 2026101908, 200000
rng = np.random.default_rng(SEED)
records = []
for m, n in [(3, 1), (3, 2), (4, 2), (5, 3)]:
    A = (rng.standard_normal((N, m, n))+1j*rng.standard_normal((N, m, n)))/np.sqrt(2)
    G = np.einsum('nri,nrj->nij', A.conj(), A)
    lam = np.linalg.eigvalsh(G)[:, 0]
    residuals = 1/np.diagonal(np.linalg.inv(G), axis1=1, axis2=2).real
    eps = 1e-8*(1+np.trace(G, axis1=1, axis2=2).real)
    assert np.all(lam[:, None] <= residuals+eps[:, None])
    assert np.all(residuals.min(axis=1) <= n*lam+eps)
    # Independently form projection residuals for a deterministic initial subset.
    max_error = 0.0
    for k in range(400):
        for j in range(n):
            others = np.delete(A[k], j, axis=1)
            residual = A[k, :, j]-others@np.linalg.lstsq(others, A[k, :, j], rcond=None)[0]
            max_error = max(max_error, abs(float(np.vdot(residual, residual).real)-residuals[k, j]))
    assert max_error < 1e-8
    shape = m-n+1
    energy = residuals[:, 0]
    mean_se = (energy.mean()-shape)/np.sqrt(shape/N)
    second = shape*(shape+1)
    var_second = shape*(shape+1)*(shape+2)*(shape+3)-second**2
    second_se = ((energy**2).mean()-second)/np.sqrt(var_second/N)
    trace = np.trace(G, axis1=1, axis2=2).real
    trace_se = (trace.mean()-m*n)/np.sqrt(m*n/N)
    assert max(abs(mean_se), abs(second_se), abs(trace_se)) < 6
    checks = []
    for x in (0.1, 0.5, 1.0):
        lower_event, min_event = energy <= x, lam <= x
        upper_event = (residuals <= n*x).any(axis=1)
        assert not np.any(lower_event & ~min_event)
        assert not np.any(min_event & ~upper_event)
        lower, upper = float(gammainc(shape, x)), min(1.0, n*float(gammainc(shape, n*x)))
        empirical = float(min_event.mean())
        tolerance = 6*np.sqrt(max(empirical*(1-empirical), 1/N)/N)
        assert lower-tolerance <= empirical <= upper+tolerance
        checks.append(dict(x=x, gamma_lower=lower, empirical_min_cdf=empirical, union_gamma_upper=upper))
    negative_control = int(np.count_nonzero(residuals.min(axis=1) > lam+eps))
    if n > 1:
        assert negative_control > N//2  # Removing factor n is generally false.
    records.append(dict(m=m, n=n, shape=shape, residual_mean_se=float(mean_se),
                        residual_second_moment_se=float(second_se), trace_Gamma_se=float(trace_se),
                        qr_residual_max_error=max_error, false_factor_one_violations=negative_control,
                        checks=checks))
result = dict(seed=SEED, samples_per_shape=N,
              source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              status='PASS residual inequalities and actual Gamma/trace controls; not proof', records=records)
dest = Path(__file__).resolve().parents[1]/'verification/central_mixed_moments/residual-control.json'
dest.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
print(result['status'])
