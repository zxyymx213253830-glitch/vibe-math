"""Finite-N planar Gaussian polynomial controls; numerical evidence, not proof."""
from pathlib import Path
import hashlib
import json
import sys

import numpy as np
from scipy.special import exp1

SEED = 2026102123
SAMPLES = 200_000


def lognorm(values):
    norms = np.abs(values)
    result = np.zeros_like(norms, dtype=float)
    np.log(norms, out=result, where=norms > 0)  # Lean's totalized log0=0.
    return result


def main(output):
    rng = np.random.default_rng(SEED)
    rows = []
    for n in range(1, 7):
        z = rng.normal(size=(SAMPLES, n)) + 1j * rng.normal(size=(SAMPLES, n))
        product = z.prod(axis=1)
        lp = lognorm(product)
        exact_mean = n * (np.log(2) - np.euler_gamma) / 2
        se = lp.std(ddof=1) / np.sqrt(SAMPLES)
        assert abs(lp.mean() - exact_mean) <= 7 * se + 1e-5
        assert np.all(np.maximum(0, -lp) <= np.maximum(0, -lognorm(z)).sum(axis=1) + 1e-10)
        rows.append({'case': f'product-{n}', 'status': 'PASS', 'mean_log': float(lp.mean()),
                     'exact_mean_log': float(exact_mean), 'standard_error': float(se)})
        affine = z.sum(axis=1)
        neg = np.maximum(0, -lognorm(affine))
        exact_neg = (np.euler_gamma + np.log(1 / (2 * n)) + exp1(1 / (2 * n))) / 2
        se_neg = neg.std(ddof=1) / np.sqrt(SAMPLES)
        assert abs(neg.mean() - exact_neg) <= 7 * se_neg + 1e-5
        rows.append({'case': f'sum-{n}', 'status': 'PASS', 'negative_mean': float(neg.mean()),
                     'exact_negative_mean': float(exact_neg), 'standard_error': float(se_neg)})
        translated_product = np.maximum(0, -lognorm(product + 1))
        assert translated_product.mean() <= n / 4 + 7 * translated_product.std(ddof=1) / np.sqrt(SAMPLES)
        rows.append({'case': f'product-plus-one-{n}', 'status': 'PASS',
                     'negative_mean': float(translated_product.mean()), 'candidate_bound': n / 4})
    # Degree-drop fiber: P(a,b,c)=a^2*b+c; lexicographic degree sum=3.
    z = rng.normal(size=(SAMPLES, 3)) + 1j * rng.normal(size=(SAMPLES, 3))
    neg = np.maximum(0, -lognorm(z[:, 0] ** 2 * z[:, 1] + z[:, 2]))
    assert neg.mean() <= .75 + 7 * neg.std(ddof=1) / np.sqrt(SAMPLES)
    assert (0 ** 2 * 0 + 2j) == 2j  # Leading coefficient can vanish; polynomial need not.
    rows.append({'case': 'dependent-leading-coefficient', 'status': 'PASS',
                 'negative_mean': float(neg.mean()), 'candidate_bound': .75})
    assert lognorm(np.array([0j]))[0] == 0
    rows.append({'case': 'zero-polynomial-totalization', 'status': 'PASS'})
    # Negative control: variance-one REAL coordinates are not proper CN1.
    c1 = (np.euler_gamma + np.log(.5) + exp1(.5)) / 2
    cproper = (np.euler_gamma + exp1(1)) / 2
    assert abs(c1 - cproper) > .1
    rows.append({'case': 'wrong-variance-negative-control', 'status': 'PASS',
                 'planar_value': float(c1), 'proper_cn1_value': float(cproper)})
    result = {'seed': SEED, 'samples': SAMPLES, 'status': 'PASS 21 controls',
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'normalization': 'Each real coordinate N(0,1); complex second moment2.',
              'interpretation': 'Reproducible controls only; not an all-N proof.', 'rows': rows}
    target = Path(output)
    if target.exists():
        raise SystemExit('Refusing to overwrite control result')
    target.write_text(json.dumps(result, indent=2) + '\n', encoding='utf8')
    print(result['status'])


if __name__ == '__main__':
    main(sys.argv[1])
