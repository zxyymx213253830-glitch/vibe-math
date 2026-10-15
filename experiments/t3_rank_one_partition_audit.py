"""Independent rank-one T3 controls; numerical evidence, never a proof.

Source: arXiv cs/0611007v2 HTML (17),(21),(24)--(26),(64)--(68).
The displayed coefficient and original row positions are retained literally.
A second raw-column integration checks the normalization independently.
No Lean candidate is changed and no probability identity is assumed.
"""
from pathlib import Path
from datetime import datetime, timezone
import itertools
import json
import math
import numpy as np
from scipy.integrate import quad
from scipy.special import gammainc, gammaincc, gamma, ive, hyp0f1
from scipy.stats import ncx2

SEED = 20261015
N = 200000
ROOT = Path(__file__).resolve().parents[1]


def multigamma(q, r):
    return math.prod(math.factorial(r-i) for i in range(1, q+1))


def matrix_pair(s, t, lam, x):
    upper = np.empty((s, s)); lower = np.empty((s, s))
    raw_upper = np.empty((s, s)); raw_lower = np.empty((s, s))
    errors = []
    for ii in range(s):
        i = ii + 1
        # Literal Nuttall-Q entry after substitution u=sqrt(2y).
        power = (s+t)/2-i

        def kernel(y):
            if y == 0:
                return 0.0
            arg = 2*math.sqrt(lam*y)
            return y**power * math.exp(-(math.sqrt(y)-math.sqrt(lam))**2) * ive(t-s, arg)

        lower[ii, 0], e1 = quad(kernel, 0, x, epsabs=1e-11, epsrel=1e-11)
        upper[ii, 0], e2 = quad(kernel, x, np.inf, epsabs=1e-11, epsrel=1e-11)

        def raw(y):
            return y**(t-i)*math.exp(-y)*hyp0f1(t-s+1, lam*y)

        raw_lower[ii, 0], e3 = quad(raw, 0, x, epsabs=1e-10, epsrel=1e-10)
        # Finite truncation avoids overflow in the independent hypergeometric kernel.
        raw_upper[ii, 0], e4 = quad(raw, x, 160, epsabs=1e-10, epsrel=1e-10)
        raw_tail, et = quad(raw, 160, 220, epsabs=1e-10, epsrel=1e-10)
        assert abs(raw_tail) < 1e-10
        d = math.factorial(t-s)*lam**((s-t)/2)*math.exp(lam)
        assert np.allclose([raw_lower[ii, 0], raw_upper[ii, 0]],
                           d*np.array([lower[ii, 0], upper[ii, 0]]), rtol=2e-10, atol=1e-11)
        errors += [e1, e2, e3, e4, et]
        for jj in range(1, s):
            j = jj+1; shape = t+s-i-j+1
            lower[ii, jj] = gamma(shape)*gammainc(shape, x)
            upper[ii, jj] = gamma(shape)*gammaincc(shape, x)
            d = math.factorial(t-s)/math.factorial(t-j)
            raw_lower[ii, jj] = d*lower[ii, jj]
            raw_upper[ii, jj] = d*upper[ii, jj]
    return upper, lower, raw_upper, raw_lower, max(errors)


def row_sum(upper, lower, k):
    s = len(upper)
    return sum(float(np.linalg.det(np.array([
        upper[i] if i in selected else lower[i] for i in range(s)])))
        for selected in itertools.combinations(range(s), k-1))


def main():
    rng = np.random.default_rng(SEED); cases = []; controls = []
    for s, t, lam in [(3, 4, 1.0), (3, 4, 2.0)]:
        z = (rng.normal(size=(N, s, t))+1j*rng.normal(size=(N, s, t)))/math.sqrt(2)
        trace0 = np.sum(np.abs(z)**2, axis=(1, 2))
        for point in [s*t-2, s*t, s*t+2]:
            exact = float(ncx2.cdf(2*point, 2*s*t, 0)); hat = float(np.mean(trace0 <= point))
            tol = 6*math.sqrt(exact*(1-exact)/N)+2/N
            assert abs(hat-exact) < tol
            controls.append({'kind': 'central Gamma(st,1)', 'point': point,
                             'empirical': hat, 'exact': exact})
        z[:, 0, 0] += math.sqrt(lam)
        trace = np.sum(np.abs(z)**2, axis=(1, 2))
        for point in [s*t, s*t+2]:
            exact = float(ncx2.cdf(2*point, 2*s*t, 2*lam)); hat = float(np.mean(trace <= point))
            tol = 6*math.sqrt(exact*(1-exact)/N)+2/N
            assert abs(hat-exact) < tol
            controls.append({'kind': 'noncentral trace / variance', 'lambda': lam,
                             'point': point, 'empirical': hat, 'exact': exact})
        eigen = np.linalg.eigvalsh(z @ z.conj().transpose(0, 2, 1))
        for x in [0.5, 1.0, 2.0]:
            up, lo, ru, rl, err = matrix_pair(s, t, lam, x)
            total = row_sum(up, lo, 2)
            c3 = lam**((2-s-t)/2)/multigamma(s-1, s-1)
            literal = c3*total; factor = multigamma(s-1, t-1); derived = literal/factor
            raw_normalized = row_sum(ru, rl, 2)/np.linalg.det(ru+rl)
            assert abs(raw_normalized-derived) < 1e-9
            # k=2: exactly one eigenvalue above x (numpy orders ascending).
            hits = int(np.count_nonzero((eigen[:, s-2] < x) & (x < eigen[:, s-1])))
            empirical = hits/N; se = math.sqrt(derived*(1-derived)/N)
            assert abs(empirical-derived) < 6*se+2/N
            # Very small probabilities may be unresolved at N=200000. Require
            # discrimination only at the preselected resolvable thresholds.
            if x >= 1:
                assert abs(empirical-literal) > 8*se
            cases.append({'s': s, 't': t, 'L': 1, 'lambda': lam, 'k': 2, 'x': x,
                'hits': hits, 'N': N, 'empirical': empirical, 'standard_error': se,
                'literal_c3_row_sum': literal, 'residual_Gamma': factor,
                'literal_div_residual': derived, 'independent_raw_normalized': raw_normalized,
                'literal_deviation_SE': abs(empirical-literal)/se,
                'derived_deviation_SE': abs(empirical-derived)/se,
                'displayed_separated_at_8SE': bool(abs(empirical-literal) > 8*se),
                'quadrature_max_error': err})
    result = {'utc': datetime.now(timezone.utc).isoformat(), 'seed': SEED, 'N_per_case': N,
        'source': 'https://arxiv.org/html/cs/0611007v2',
        'source_equations': ['17', '21', '24-26', '64-68'], 'controls': controls, 'cases': cases,
        'status': 'PASS controls; displayed formula inconsistent with actual samples',
        'interpretation': 'Numerical diagnostic only. Supports residual Gamma factor; does not decide journal erratum or hidden convention. No T3 Lean candidate modified; no probability bridge asserted.'}
    output = ROOT/'verification/WISHART_T3_RANK_ONE_AUDIT_20261015.json'
    output.write_text(json.dumps(result, indent=2), encoding='utf-8')
    for c in cases:
        print('lambda={lambda} x={x} MC={empirical:.8f} displayed={literal_c3_row_sum:.8f} normalized={literal_div_residual:.8f} SEdev={derived_deviation_SE:.2f}'.format(**c))
    print('Fixed-seed actual-model controls PASS; not a proof.')


if __name__ == '__main__':
    main()
