"""Fixed-seed actual CN controls; sample ranks are not an a.e. proof."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path

import numpy as np
from scipy.special import digamma, polygamma


def main():
    rng = np.random.default_rng(20261017)
    n_samples = 200_000
    records = []
    for m, n in [(2, 1), (3, 2), (4, 4), (5, 3)]:
        traces, logdets, smallest = [], [], []
        for _ in range(n_samples//5000):
            a = (rng.normal(size=(5000, m, n)) + 1j*rng.normal(size=(5000, m, n)))/np.sqrt(2)
            gram = a.conj().transpose(0, 2, 1) @ a
            eig = np.linalg.eigvalsh(gram)
            sign, logdet = np.linalg.slogdet(gram)
            assert np.all(sign.real > 0) and np.all(eig[:, 0] > 0)
            traces.append(np.trace(gram, axis1=1, axis2=2).real)
            logdets.append(logdet)
            smallest.append(eig[:, 0])
        trace = np.concatenate(traces)
        logdet = np.concatenate(logdets)
        # Independent known CN trace Gamma(m*n,1) control and Bartlett log-det moments.
        trace_z = (trace.mean()-m*n)/np.sqrt(m*n/n_samples)
        shapes = np.arange(m-n+1, m+1)
        logdet_mean = float(np.sum(digamma(shapes)))
        logdet_variance = float(np.sum(polygamma(1, shapes)))
        logdet_z = (logdet.mean()-logdet_mean)/np.sqrt(logdet_variance/n_samples)
        assert abs(trace_z) < 6 and abs(logdet_z) < 6
        assert abs(logdet.var(ddof=1)/logdet_variance-1) < .03
        records.append(dict(m=m, n=n, N=n_samples, trace_standard_errors=float(trace_z),
            logdet_standard_errors=float(logdet_z), logdet_variance_ratio=float(
                logdet.var(ddof=1)/logdet_variance),
            minimum_observed_eigenvalue=float(np.concatenate(smallest).min())))
    wide = rng.normal(size=(2, 3)) + 1j*rng.normal(size=(2, 3))
    assert np.linalg.matrix_rank(wide) == 2
    # Exact structural reason: m<n gives a nontrivial kernel; tolerance is only a control.
    assert abs(np.linalg.eigvalsh(wide.conj().T@wide)[0]) < 1e-12
    root = Path(__file__).resolve().parents[1]
    target = root/'verification/gaussian_full_rank'
    target.mkdir(exist_ok=True)
    (target/'control.json').write_text(json.dumps(dict(seed=20261017,
        collected_utc=datetime.now(timezone.utc).isoformat(), records=records,
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        control='Actual CN(0,1) trace Gamma(m*n,1), known Bartlett log-det moments; wide negative control',
        status='PASS numerical controls only; not proof of a.e. full rank'), indent=2)+'\n', encoding='utf-8')
    print('PASS four actual CN cases, 200000 each, trace/logdet controls and wide negative control.')


if __name__ == '__main__':
    main()
