"""Finite-spectrum log domination controls; no integrability proof by sampling."""
from pathlib import Path
import hashlib
import json
import sys
import numpy as np


def main(output):
    seed, samples = 2026102125, 200_000
    rng = np.random.default_rng(seed)
    rows = []
    for n in range(9):
        lam = np.exp(rng.normal(scale=4, size=(samples, n)))
        lam[rng.random(lam.shape) < .2] = 0
        logs = np.zeros_like(lam)
        np.log(lam, out=logs, where=lam > 0)
        dom = lam.sum(axis=1) + np.abs(logs.sum(axis=1))
        assert np.all(np.abs(logs) <= dom[:, None] + 1e-10)
        assert np.all(logs <= lam + 1e-10)
        rows.append({'n': n, 'status': 'PASS'})
    eps = np.array([1e-2, 1e-4, 1e-8])
    # For arbitrary functions cancellation alone does not control individual L1:
    # h1(t)=1/t,h2(t)=-1/t, sum0 but integral_eps^1 |h1|=-log eps.
    truncation = -np.log(eps)
    assert np.all(np.diff(truncation) > 0)
    rows.append({'case': 'cancellation-only-negative-control', 'status': 'PASS',
                 'eps': eps.tolist(), 'exact_truncated_absolute_integral': truncation.tolist()})
    # The unproved rank/spectral polynomial bridge is not tested by these arrays.
    result = {'seed': seed, 'samples': samples, 'status': 'PASS 10 controls',
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'interpretation': 'Nonnegative finite spectra and exact cancellation countercontrol; not probability proof.',
              'rows': rows}
    p = Path(output)
    if p.exists():
        raise SystemExit('Refusing overwrite')
    p.write_text(json.dumps(result, indent=2) + '\n', encoding='utf8')
    print(result['status'])


if __name__ == '__main__':
    main(sys.argv[1])
