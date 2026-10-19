"""Fixed-seed actual ZB+M controls, including rectangular/singular B; not proof."""
import hashlib
import json
from pathlib import Path
import numpy as np

SEED, SAMPLES = 2026101926, 200_000
rng = np.random.default_rng(SEED)
records = []
for m, p, n, kind in [(1, 3, 3, 'identity'), (2, 2, 3, 'rectangular'),
                       (3, 4, 2, 'rectangular'), (2, 2, 2, 'singular'), (2, 2, 3, 'zero')]:
    b = (np.arange(p*n).reshape(p, n)+1)/(p*n) + 1j*np.eye(p, n)/3
    if kind == 'identity':
        b = np.eye(n, dtype=complex)
    if kind == 'singular':
        b[:, 1] = (1+1j)*b[:, 0]
    if kind == 'zero':
        b[:] = 0
    mean = (.2+.1j)*(np.arange(m*n).reshape(m, n)+1)/(m*n)
    if kind == 'identity':
        mean[:] = 0
    sigma, a = b.conj().T@b, mean.conj().T@mean
    st, st2, f = np.trace(sigma).real, np.trace(sigma@sigma).real, np.trace(a).real
    cross = np.trace(sigma@a).real
    expected_gram = m*sigma+a
    t = m*st+f
    variance = m*st2+2*cross
    second = m*m*st2+m*st*st+2*m*cross+2*st*f+np.trace(a@a).real
    traces, squares, grams = [], [], []
    for _ in range(SAMPLES//20_000):
        z = (rng.standard_normal((20_000, m, p))+1j*rng.standard_normal((20_000, m, p)))/np.sqrt(2)
        x = z@b+mean
        w = np.swapaxes(x.conj(), 1, 2)@x
        traces.append(np.trace(w, axis1=1, axis2=2).real)
        squares.append(np.sum(np.abs(w)**2, axis=(1, 2)))
        grams.append(w)
    trace, square, gram = np.concatenate(traces), np.concatenate(squares), np.concatenate(grams)
    centered = (trace-t)**2
    for sample, target in [(trace, t), (centered, variance), (square, second)]:
        assert abs(sample.mean()-target) < 6*sample.std(ddof=1)/np.sqrt(SAMPLES)+1e-10
    assert np.all(np.abs(gram.mean(axis=0)-expected_gram) < 6*np.std(gram, axis=0)/np.sqrt(SAMPLES)+1e-10)
    if kind == 'identity':
        assert (t, variance, second) == (3, 3, 12)  # independent Gamma(3,1)
    if kind == 'zero':
        assert variance == 0 and np.allclose(gram, a)
    records.append(dict(m=m, p=p, n=n, kind=kind, rank=int(np.linalg.matrix_rank(b)),
                        mean_power=float(t), trace_variance=float(variance), second_spectral=float(second),
                        observed_mean=float(trace.mean()), observed_variance=float(centered.mean()),
                        observed_second_spectral=float(square.mean())))
report = dict(seed=SEED, samples_per_shape=SAMPLES,
              source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              status='PASS actual rectangular/singular/zero-factor moments and independent Gamma control; NOT Lean proof',
              model='Z m-by-p iid CN(0,1), B p-by-n fixed, X=ZB+M; Sigma=B^H B', records=records)
Path('verification/central_mixed_moments/correlated-trace-control.json').write_text(
    json.dumps(report, indent=2)+'\n', encoding='utf-8')
print(report['status'])
