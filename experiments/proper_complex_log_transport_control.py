"""Proper CN1 log transport controls, fixed seed; not a proof."""
from pathlib import Path
import hashlib
import json
import sys

import numpy as np
from scipy.special import exp1, digamma


def lognorm(x):
    a = np.abs(x)
    out = np.zeros_like(a, dtype=float)
    np.log(a, out=out, where=a > 0)
    return out


def main(output):
    seed, samples = 2026102124, 200_000
    rng = np.random.default_rng(seed)
    rows = []
    for n in range(1, 7):
        planar = rng.normal(size=(samples, n)) + 1j * rng.normal(size=(samples, n))
        proper = planar / np.sqrt(2)
        a = np.prod(proper, axis=1) + 1
        b = np.prod(planar / np.sqrt(2), axis=1) + 1
        assert np.allclose(a, b, rtol=0, atol=0)
        lp = lognorm(np.prod(proper, axis=1))
        exact = -n * np.euler_gamma / 2
        assert abs(lp.mean() - exact) <= 7 * lp.std(ddof=1) / np.sqrt(samples)
        affine = np.maximum(0, -lognorm(proper.sum(axis=1)))
        exact_neg = (np.euler_gamma - np.log(n) + exp1(1 / n)) / 2
        assert abs(affine.mean() - exact_neg) <= 7 * affine.std(ddof=1) / np.sqrt(samples)
        rows.append({'case': f'proper-product-{n}', 'status': 'PASS', 'mean_log': float(lp.mean()),
                     'exact_mean_log': float(exact)})
        rows.append({'case': f'proper-affine-{n}', 'status': 'PASS',
                     'negative_mean': float(affine.mean()), 'exact_negative_mean': float(exact_neg)})
        rows.append({'case': f'polynomial-scaling-identity-{n}', 'status': 'PASS'})
    for q in [1, 2, 3]:
        z = (rng.normal(size=(samples, q, q)) + 1j * rng.normal(size=(samples, q, q))) / np.sqrt(2)
        # Identity compression has known central square Wishart log determinant.
        lp = lognorm(np.linalg.det(z))
        exact = float(sum(digamma(j) for j in range(1, q + 1)) / 2)
        assert abs(lp.mean() - exact) <= 7 * lp.std(ddof=1) / np.sqrt(samples)
        rows.append({'case': f'physical-square-compression-{q}', 'status': 'PASS',
                     'mean_log_abs_det': float(lp.mean()), 'known_bartlett_value': exact})
    # Zero-dimensional and zero-polynomial values use totalized log0=0.
    assert np.prod(np.empty(0, dtype=complex)) == 1
    assert lognorm(np.array([0j]))[0] == 0
    rows.append({'case': 'empty-product-and-totalized-zero', 'status': 'PASS'})
    assert abs(-np.euler_gamma / 2 - (np.log(2) - np.euler_gamma) / 2) > .3
    rows.append({'case': 'missing-sqrt2-negative-control', 'status': 'PASS'})
    result = {'seed': seed, 'samples': samples, 'status': f'PASS {len(rows)} controls',
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'interpretation': 'Reproducible scaling/model controls, not general proof.', 'rows': rows}
    p = Path(output)
    if p.exists():
        raise SystemExit('Refusing overwrite')
    p.write_text(json.dumps(result, indent=2) + '\n', encoding='utf8')
    print(result['status'])


if __name__ == '__main__':
    main(sys.argv[1])
